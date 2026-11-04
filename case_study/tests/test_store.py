"""Atomic business effects, native units, DPoP replay and state snapshots."""
import tempfile
import unittest
from pathlib import Path

from case_study.store import Store, Denied


SEARCH = {"query": "hotel"}
DETAILS = {"item_id": "hotel-101"}
BOOK = {"item_id": "hotel-101", "customer": "synthetic-test"}
BATCH = {"items": [{"item_id": "hotel-101", "resource": "inventory/allowed"} for _ in range(8)]}
CLAIMS = {"sub": "agent", "cnf": {"jkt": "test-confirmation-key"}, "period": 1}


class StoreTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.store = Store(Path(self.directory.name) / "state.sqlite")

    def tearDown(self):
        self.directory.cleanup()

    def oauth_grant(self, **options):
        self.store.install_grant("agent", jkt=CLAIMS["cnf"]["jkt"], **options)

    def test_injected_backend_failure_rolls_back_booking_and_all_units(self):
        with self.assertRaisesRegex(Denied, "injected_backend_failure"):
            self.store.commit("darlt", "agent", "book_item", BOOK, "request", ["a", "b", "c", "d"], inject_failure=True)
        self.assertEqual(self.store.facts("agent"), {"effects": 0, "bookings": 0, "consumed": 0, "remaining": None})
        self.assertTrue(self.store.commit("darlt", "agent", "book_item", BOOK, "request", ["a", "b", "c", "d"])["accepted"])

    def test_last_replayed_unit_rolls_back_other_batch_units(self):
        self.store.commit("darlt", "agent", "get_details", DETAILS, "prior", ["used"])
        before = self.store.facts("agent")
        with self.assertRaisesRegex(Denied, "serial_or_dpop_replay"):
            self.store.commit("darlt", "agent", "batch_query", BATCH, "batch", [str(i) for i in range(7)] + ["used"])
        self.assertEqual(self.store.facts("agent"), before)
        self.assertTrue(self.store.commit("darlt", "agent", "batch_query", BATCH, "clean", [str(i) for i in range(8)])["accepted"])
        self.assertEqual(self.store.facts("agent")["consumed"], 9)

    def test_duplicate_batch_serial_or_wrong_native_amount_has_no_effect(self):
        for serials in [["same"] * 8, [str(i) for i in range(7)]]:
            with self.subTest(serials=serials), self.assertRaises(Denied):
                self.store.commit("sma", "agent", "batch_query", BATCH, "request", serials)
        self.assertEqual(self.store.facts()["effects"], 0)
        self.assertEqual(self.store.facts()["consumed"], 0)

    def test_cost_eight_and_exhaustion_apply_to_server_counter_modes(self):
        for mode in ("msb", "slw"):
            with self.subTest(mode=mode):
                name = mode + "-agent"; self.store.install_grant(name, quota=8)
                self.assertEqual(self.store.commit(mode, name, "batch_query", BATCH, "batch")["units"], 8)
                self.assertEqual(self.store.facts(name)["remaining"], 0)
                with self.assertRaisesRegex(Denied, "quota_exhausted"):
                    self.store.commit(mode, name, "get_details", DETAILS, "extra")
                self.assertEqual(self.store.facts(name)["effects"], 1)

    def test_dpop_jti_replay_cannot_decrement_quota_or_book(self):
        self.oauth_grant(quota=16)
        self.store.commit("oauth", "agent", "get_details", DETAILS, "first", claims=CLAIMS, dpop_jti="one-use")
        before = self.store.facts("agent")
        with self.assertRaisesRegex(Denied, "serial_or_dpop_replay"):
            self.store.commit("oauth", "agent", "book_item", BOOK, "second", claims=CLAIMS, dpop_jti="one-use")
        self.assertEqual(self.store.facts("agent"), before)
        self.assertEqual(before["remaining"], 15)

    def test_oauth_batch_cost_eight_and_quota_failure_does_not_consume_jti(self):
        self.oauth_grant(quota=8)
        self.assertEqual(self.store.commit("oauth", "agent", "batch_query", BATCH, "batch", claims=CLAIMS, dpop_jti="first")["units"], 8)
        with self.assertRaisesRegex(Denied, "quota_exhausted"):
            self.store.commit("oauth", "agent", "get_details", DETAILS, "extra", claims=CLAIMS, dpop_jti="rolled-back")
        with self.store.connect() as db:
            self.assertEqual(db.execute("SELECT COUNT(*) FROM dpop").fetchone()[0], 1)
        self.assertEqual(self.store.facts("agent")["effects"], 1)

    def test_snapshot_is_deep_and_restores_quota_jti_and_business_rows(self):
        self.oauth_grant(quota=64)
        snapshot = self.store.snapshot()
        try:
            self.store.commit("oauth", "agent", "book_item", BOOK, "first", claims=CLAIMS, dpop_jti="reusable-after-restore")
            self.assertEqual(self.store.facts("agent")["bookings"], 1)
            self.store.restore(snapshot)
            self.assertEqual(self.store.facts("agent"), {"effects": 0, "bookings": 0, "consumed": 0, "remaining": 64})
            self.store.commit("oauth", "agent", "book_item", BOOK, "fresh", claims=CLAIMS, dpop_jti="reusable-after-restore")
            self.assertEqual(self.store.facts("agent")["bookings"], 1)
            self.assertEqual(self.store.facts("agent")["remaining"], 60)
        finally:
            snapshot.close()

    def test_empty_scope_grants_no_implicit_default_permissions(self):
        self.oauth_grant(scopes=[])
        with self.assertRaisesRegex(Denied, "scope_not_granted"):
            self.store.commit("oauth", "agent", "search_inventory", SEARCH, "request", claims=CLAIMS, dpop_jti="unused")
        self.assertEqual(self.store.facts("agent")["remaining"], 64)
        self.assertEqual(self.store.facts("agent")["effects"], 0)

    def test_ungranted_attribute_or_private_attribute_rejected(self):
        for name, tool, attrs in [("ungranted", "delete_record", (0, 1, 2, 3)),
                                  ("private", "export_private", (0, 1, 2, 3, 6))]:
            with self.subTest(name=name):
                self.store.install_grant(name, scopes=[tool + ":inventory/allowed"], attributes=attrs)
                with self.assertRaisesRegex(Denied, "attribute_not_granted"):
                    self.store.commit("msb", name, tool, DETAILS, "request")
                self.assertEqual(self.store.facts(name)["remaining"], 64)

    def test_mixed_resource_batch_rejection_is_atomic(self):
        self.oauth_grant()
        batch = {"items": [dict(x) for x in BATCH["items"]]}
        batch["items"][-1]["resource"] = "inventory/restricted"
        with self.assertRaisesRegex(Denied, "scope_not_granted"):
            self.store.commit("oauth", "agent", "batch_query", batch, "request", claims=CLAIMS, dpop_jti="unused")
        self.assertEqual(self.store.facts("agent")["remaining"], 64)
        self.assertEqual(self.store.facts("agent")["effects"], 0)


if __name__ == "__main__":
    unittest.main()
