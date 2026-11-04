"""Correctness-only OAuth/DPoP checks; no performance records are produced."""

import hashlib
import unittest

from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import ec, padding, utils

from case_study import oauth


class OAuthTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.issuer = oauth.OAuthIssuer()
        cls.verifier = cls.issuer.verifier()
        cls.key = oauth.new_dpop_key()
        cls.other_key = oauth.new_dpop_key()
        cls.now = 1800000000
        cls.url = "http://127.0.0.1:8080/mcp"

    def token(self, **kwargs):
        values = dict(dpop_public_key=self.key.public_key(), audience=self.url,
                      scopes=["search_inventory:hotel"], subject="agent-A", period=1,
                      attributes=["region", "booking"], now=self.now)
        values.update(kwargs)
        return self.issuer.issue(**values)

    def access(self, token, **kwargs):
        values = dict(audience=self.url, period=1, now=self.now)
        values.update(kwargs)
        return self.verifier.verify(token, **values)

    def change_access(self, token, change=None, header_change=None, payload_bytes=None):
        header, claims, _, _ = oauth._decode(token)
        if change:
            change(claims)
        if header_change:
            header_change(header)
        payload = oauth._canonical(claims) if payload_bytes is None else payload_bytes
        message = (oauth._b64(oauth._canonical(header)) + "." + oauth._b64(payload)).encode()
        return message.decode() + "." + oauth._b64(self.issuer._key.sign(message, padding.PKCS1v15(), hashes.SHA256()))

    def change_dpop(self, proof, change=None, header_change=None, payload_bytes=None):
        header, claims, _, _ = oauth._decode(proof)
        if change:
            change(claims)
        if header_change:
            header_change(header)
        payload = oauth._canonical(claims) if payload_bytes is None else payload_bytes
        message = (oauth._b64(oauth._canonical(header)) + "." + oauth._b64(payload)).encode()
        r, s = utils.decode_dss_signature(self.key.sign(message, ec.ECDSA(hashes.SHA256())))
        return message.decode() + "." + oauth._b64(r.to_bytes(32, "big") + s.to_bytes(32, "big"))

    def dpop_fixture(self, **kwargs):
        token = self.token()
        claims = self.access(token)
        args = dict(key=self.key, token=token, url=self.url, nonce="server-nonce", now=self.now)
        args.update(kwargs)
        return token, claims, oauth.dpop_sign(**args)

    def check_dpop(self, proof, token, claims, **kwargs):
        args = dict(url=self.url, expected_nonce="server-nonce", now=self.now)
        args.update(kwargs)
        return oauth.verify_dpop(proof, token, claims, **args)

    def test_valid_access_and_public_only_verifier(self):
        claims = self.access(self.token())
        self.assertEqual(claims["quota"], 64)
        self.assertEqual(claims["attributes"], ["region", "booking"])
        self.assertFalse(hasattr(self.verifier, "_key"))
        self.assertFalse(hasattr(self.verifier.public_key, "sign"))

    def test_access_audience_list_and_empty_scope(self):
        self.assertEqual(self.access(self.token(audience=[self.url, "https://other.test/mcp"], scopes=[]))["scope"], "")

    def test_access_wrong_key_and_audience(self):
        token = self.token()
        with self.assertRaisesRegex(ValueError, "signature"):
            oauth.OAuthIssuer().verifier().verify(token, self.url, 1, now=self.now)
        with self.assertRaisesRegex(ValueError, "audience"):
            self.access(token, audience="https://elsewhere.test/mcp")

    def test_access_expired_not_yet_valid_and_wrong_period(self):
        with self.assertRaises(ValueError):
            self.access(self.token(now=self.now - 3600))
        with self.assertRaises(ValueError):
            self.access(self.change_access(self.token(), lambda c: c.update(nbf=self.now + 100)))
        with self.assertRaises(ValueError):
            self.access(self.change_access(self.token(lifetime=10), lambda c: c.update(nbf=self.now + 20)))
        with self.assertRaises(ValueError):
            self.access(self.token(), period=2)

    def test_access_type_and_algorithm_confusion(self):
        for update in [{"alg": "HS256"}, {"alg": "none"}, {"typ": "JWT"}, {"crit": ["x"]}, {"jku": "https://untrusted.test/key"}]:
            with self.subTest(update=update), self.assertRaises(ValueError):
                self.access(self.change_access(self.token(), header_change=lambda h: h.update(update)))

    def test_access_required_claims_and_types(self):
        for name in ["iss", "exp", "aud", "sub", "client_id", "iat", "jti", "scope", "cnf", "quota", "period"]:
            with self.subTest(missing=name), self.assertRaises(ValueError):
                self.access(self.change_access(self.token(), lambda c: c.pop(name)))
        for name, value in [("iat", True), ("exp", "forever"), ("nbf", False), ("quota", True), ("quota", -1), ("period", 1.0), ("aud", []), ("scope", "has  duplicate-space")]:
            with self.subTest(name=name, value=value), self.assertRaises(ValueError):
                self.access(self.change_access(self.token(), lambda c: c.update({name: value})))

    def test_duplicate_json_and_nonfinite_json_rejected(self):
        token = self.token()
        _, claims, _, _ = oauth._decode(token)
        payload = oauth._canonical(claims)[:-1] + b',"iat":1800000000}'
        with self.assertRaisesRegex(ValueError, "duplicate_json"):
            self.access(self.change_access(token, payload_bytes=payload))
        with self.assertRaises(ValueError):
            self.access(self.change_access(token, payload_bytes=b'{"exp":NaN}'))
        with self.assertRaises(ValueError):
            self.access(self.change_access(token, payload_bytes=b'{"exp":1e999}'))
        with self.assertRaises(ValueError):
            self.access(self.change_access(token, payload_bytes=oauth._canonical(claims).decode().encode("utf-16")))

    def test_noncanonical_base64url_rejected(self):
        token = self.token()
        head, payload, signature = token.split(".")
        for bad in [head + "=." + payload + "." + signature,
                    head + "." + payload + "." + signature + "=",
                    head + "." + payload + ".*", "x.y.z", ".."]:
            with self.subTest(token=bad[:20]), self.assertRaises(ValueError):
                self.access(bad)

    def test_dpop_valid_and_token_thumbprint(self):
        token, claims, proof = self.dpop_fixture()
        jti = self.check_dpop(proof, token, claims)
        self.assertEqual(len(jti), 32)
        self.assertEqual(claims["cnf"]["jkt"], oauth.thumbprint(self.key.public_key()))

    def test_dpop_replay_is_callers_atomic_state_responsibility(self):
        token, claims, proof = self.dpop_fixture()
        self.assertEqual(self.check_dpop(proof, token, claims), self.check_dpop(proof, token, claims))

    def test_dpop_wrong_key(self):
        token, claims, proof = self.dpop_fixture(key=self.other_key)
        with self.assertRaisesRegex(ValueError, "confirmation"):
            self.check_dpop(proof, token, claims)

    def test_dpop_method_uri_hash_nonce_and_clock(self):
        token, claims, proof = self.dpop_fixture()
        mutations = [{"htm": "GET"}, {"htu": self.url + "/other"}, {"ath": oauth._b64(hashlib.sha256(b"other").digest())},
                     {"nonce": "other"}, {"iat": self.now - 61}, {"iat": self.now + 61}, {"iat": True}, {"jti": ""}]
        for update in mutations:
            with self.subTest(update=update), self.assertRaises(ValueError):
                self.check_dpop(self.change_dpop(proof, lambda c: c.update(update)), token, claims)

    def test_dpop_query_fragment_and_default_port_normalization(self):
        token, claims, proof = self.dpop_fixture(url="HTTPS://Example.TEST:443/mcp?q=one#fragment")
        payload = oauth._decode(proof)[1]
        self.assertEqual(payload["htu"], "https://example.test/mcp")
        self.assertTrue(self.check_dpop(proof, token, claims, url="https://example.test/mcp?q=two"))

    def test_dpop_private_or_invalid_jwk_and_header_rejected(self):
        token, claims, proof = self.dpop_fixture()
        updates = [lambda h: h["jwk"].update(d="private"), lambda h: h["jwk"].update(kty="oct"),
                   lambda h: h.update(alg="HS256"), lambda h: h.update(typ="JWT"), lambda h: h.update(jku="https://bad.test/")]
        for update in updates:
            with self.subTest(update=update), self.assertRaises(ValueError):
                self.check_dpop(self.change_dpop(proof, header_change=update), token, claims)

    def test_dpop_bad_signature_and_duplicates(self):
        token, claims, proof = self.dpop_fixture()
        head, body, sig = proof.split(".")
        tampered = bytes([oauth._unb64(sig)[0] ^ 1]) + oauth._unb64(sig)[1:]
        with self.assertRaises(ValueError):
            self.check_dpop(head + "." + body + "." + oauth._b64(tampered), token, claims)
        payload = oauth._canonical(oauth._decode(proof)[1])[:-1] + b',"htm":"POST"}'
        with self.assertRaisesRegex(ValueError, "duplicate_json"):
            self.check_dpop(self.change_dpop(proof, payload_bytes=payload), token, claims)

    def test_dpop_nonce_optional_and_required(self):
        token, claims, proof = self.dpop_fixture(nonce=None)
        self.assertTrue(self.check_dpop(proof, token, claims, expected_nonce=None))
        with self.assertRaises(ValueError):
            self.check_dpop(proof, token, claims)

    def test_dpop_nonascii_hash_is_rejected_without_type_error(self):
        token, claims, proof = self.dpop_fixture()
        with self.assertRaisesRegex(ValueError, "token_hash"):
            self.check_dpop(self.change_dpop(proof, lambda c: c.update(ath="错误")), token, claims)

    def test_zero_quota_and_invalid_issuance_fields(self):
        self.assertEqual(self.access(self.token(quota=0))["quota"], 0)
        for values in [{"quota": True}, {"period": -1}, {"scopes": [{}]}, {"lifetime": 0}, {"attributes": ["duplicate", "duplicate"]}]:
            with self.subTest(values=values), self.assertRaises(ValueError):
                self.token(**values)


if __name__ == "__main__":
    unittest.main()
