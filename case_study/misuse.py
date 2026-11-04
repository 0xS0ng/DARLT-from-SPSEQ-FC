"""Clock-free local misuse checks over the real MCP and native interfaces.

Each concrete case has independent service databases and a fresh native
instance. Only public outcome descriptions and aggregate state facts are
returned; access tokens, proofs, keys, headers and native evidence are omitted.
"""
from __future__ import annotations

from contextlib import contextmanager, ExitStack
import copy
from pathlib import Path
import tempfile

from .role_bridge import native_pair, process_record
from .client import Client
from .mcp import RpcError, Transport
from .oauth import OAuthIssuer, new_dpop_key, thumbprint
from .server import ToolServer


MODES = ("oauth", "sma", "darlt")
_KNOWN_REJECTIONS = {
    "scope_not_granted", "attribute_not_granted", "quota_exhausted",
    "serial_or_dpop_replay", "duplicate_unit_in_batch", "dpop_confirmation",
    "native_verification_rejected", "wrong_native_unit_count",
    "native_amount_does_not_match_tool_cost", "grant_binding",
}


def _clock_free(value):
    if isinstance(value, dict):
        for key, child in value.items():
            if key == "timing" or key.endswith("_ns"):
                raise ValueError("misuse_unexpected_timing_output")
            _clock_free(child)
    elif isinstance(value, (list, tuple)):
        for child in value:
            _clock_free(child)


def _arguments(tool, resource="inventory/allowed", *, mixed=False):
    if tool == "search_inventory":
        return {"query": "hotel", "resource": resource}
    if tool == "batch_query":
        items = [{"item_id": "hotel-101", "resource": resource} for _ in range(8)]
        if mixed:
            items[-1] = {"item_id": "hotel-101", "resource": "inventory/restricted"}
        return {"resource": "inventory/allowed", "items": items}
    return {"item_id": "hotel-101", "resource": resource}


def _attempt(client, tool, arguments, **kwargs):
    try:
        result = client.call(tool, arguments, **kwargs)
        _clock_free(result)
        return bool(result["accepted"]), result, None
    except RpcError as exc:
        # Only an explicit service authorization rejection is a blocked call.
        # Transport or service errors do not count as authorization rejections.
        if exc.status != 403:
            raise
        reason = str(exc)
        return False, None, reason if reason in _KNOWN_REJECTIONS else "service_authorization_rejected"
    except ValueError as exc:
        if str(exc).startswith(("native_bridge_", "unexpected_authorization_", "MCP_", "misuse_")):
            raise
        # Native proving can reject a policy or an out-of-scope position before
        # any HTTP request. Do not copy arbitrary native exception text to logs.
        return False, None, "native_preparation_rejected"


def _facts(client):
    return client.server.stores[client.mode].facts(client.instance)


def _scope(mode):
    return {
        "oauth": "DPoP key binding and this service's authenticated scope, attribute and quota grant; no native unit coordinates or public unit Judge",
        "sma": "Original shared user wallet and its 1024 native units; no agent key, agent-only attributes or native agent quota; Identify names the user",
        "darlt": "Native recipient-key binding, delegated attributes and 64-unit scope, plus serial consumption at this service; public Judge distinguishes double use from overlapping owner allocation",
    }[mode]


def _record(case_id, category, mode, precondition, attempted_operation, before, after,
            *, applicable=True, blocked=None, accepted_before_judge=(),
            classification="not_applicable", **extra):
    return {"case_id": case_id, "category": category, "mode": mode,
            "precondition": precondition, "attempted_operation": attempted_operation,
            "applicable": applicable, "blocked": blocked,
            "accepted_before_judge": list(accepted_before_judge),
            "classification": classification,
            "effects_before_after": {"before": before, "after": after},
            "protection_scope": _scope(mode), **extra}


@contextmanager
def _fixture(root, bridge, issuer, mode, case_id, *, scopes=None):
    directory = root / case_id
    with ExitStack() as stack:
        server = stack.enter_context(ToolServer(directory / "A", bridge.service_bridge, issuer.verifier(), verifier_id="bank-A"))
        client = stack.enter_context(Client(server, bridge, mode, case_id, issuer, scopes=scopes))
        _clock_free(client.init_result)
        yield stack, server, client


def _clone_for_server(stack, original, server, *, actor="agent"):
    # Both services install the same legitimate instance/grant. In OAuth mode,
    # keep the same JWT and holder key: only htu, server nonce and fresh jti
    # change for each HTTP request. Neither malicious actor gains the AS key.
    server.register(original.instance, original.mode, subject="agent", quota=64,
                    attributes=(0, 1, 2, 3),
                    jkt=thumbprint(original.dpop_key.public_key()) if original.mode == "oauth" else None)
    if original.mode in ("darlt", "sma"):
        server.install_native(original.instance, original.bridge)
    clone = copy.copy(original)
    clone.server, clone.cursor, clone.actor = server, 0, actor
    clone.transport = Transport(server.url + "/mcp/" + original.mode)
    stack.callback(clone.close)
    return clone


def _burn(client, units):
    batches, singles = divmod(units, 8)
    for _ in range(batches):
        accepted, _, _ = _attempt(client, "batch_query", _arguments("batch_query"))
        if not accepted:
            raise ValueError("misuse_precondition_native_burn_rejected")
    for _ in range(singles):
        accepted, _, _ = _attempt(client, "search_inventory", _arguments("search_inventory"))
        if not accepted:
            raise ValueError("misuse_precondition_native_burn_rejected")
    return {"accepted_requests": batches + singles, "accepted_units": units,
            "batch_requests": batches, "single_requests": singles}


def _atomic(before, after, accepted, mode, cost):
    if not accepted:
        return before == after
    return (after["effects"] == before["effects"] + 1
            and after["bookings"] == before["bookings"]
            and after["consumed"] == before["consumed"] + (cost if mode in ("sma", "darlt") else 0)
            and (mode != "oauth" or after["remaining"] == before["remaining"] - cost))


def _authorization_cases(root, bridge, issuer, mode):
    result = []
    cases = [
        ("scope-delete", "ungranted_tool_or_resource", "delete_record", "inventory/allowed", False,
         "Default agent grant excludes delete_record (native policy requires attribute 5)."),
        ("scope-restricted", "ungranted_tool_or_resource", "get_details", "inventory/restricted", False,
         "Default agent grant excludes the restricted resource (native policy additionally requires attribute 4)."),
        ("attribute-4", "ungranted_or_private_attribute", "get_details", "inventory/restricted", True,
         "Agent attributes are 0,1,2,3; attribute 4 is not granted. OAuth resource scope is included to isolate the attribute gate."),
        ("private-attribute-6", "ungranted_or_private_attribute", "get_details", "owner/private", True,
         "Attribute 6 is owner-private and absent from agent attributes. OAuth resource scope is included to isolate the attribute gate."),
    ]
    for slug, category, tool, resource, isolate_attribute, precondition in cases:
        case_id = mode + "-" + slug
        scopes = [name + ":" + target for name in ("search_inventory", "get_details", "book_item", "batch_query")
                  for target in ("inventory/allowed", resource)] if isolate_attribute else None
        # The default allowed resource would otherwise duplicate itself.
        if scopes is not None:
            scopes = list(dict.fromkeys(scopes))
        with _fixture(root, bridge, issuer, mode, case_id, scopes=scopes) as (_, _, client):
            before = _facts(client)
            accepted, _, reason = _attempt(client, tool, _arguments(tool, resource))
            after = _facts(client)
            result.append(_record(case_id, category, mode, precondition,
                          {"tool": tool, "resource": resource}, before, after,
                          blocked=not accepted, accepted_before_judge=[accepted],
                          classification="authorization_rejected" if not accepted else "accepted_with_original_shared_wallet_authority",
                          rejection_reason=reason, atomicity_passed=_atomic(before, after, accepted, mode, 1)))
    return result


def _stolen_material(root, bridge, issuer, mode):
    case_id = mode + "-stolen-without-agent-key"
    with _fixture(root, bridge, issuer, mode, case_id) as (_, _, client):
        before = _facts(client)
        if mode == "oauth":
            client.dpop_key = new_dpop_key()
            accepted, _, reason = _attempt(client, "search_inventory", _arguments("search_inventory"))
            blocked, classification = not accepted, "DPoP_holder_key_binding" if not accepted else "stolen_JWT_accepted_with_wrong_key"
            attempted = "Use the stolen access JWT with a newly generated DPoP key; retain the legitimate server nonce and target URI."
            scope = "Stolen JWT excludes the legitimate DPoP private key."
        elif mode == "sma":
            material = bridge.command("attack_material", instance=client.instance, attack="stolen_without_key")
            _clock_free(material)
            accepted, _, reason = _attempt(client, "search_inventory", _arguments("search_inventory"), actor="stolen")
            blocked, classification = not accepted, "shared_wallet_contains_original_user_witness" if accepted else "shared_wallet_request_rejected"
            attempted = "Generate and send a real native request as the stolen shared-wallet actor."
            scope = "The stolen shared original wallet includes its native user witness; this scheme has no distinct agent secret."
        else:
            material = bridge.command("attack_material", instance=client.instance, attack="stolen_without_key")
            _clock_free(material)
            blocked, accepted, reason = material["blocked"] is True, False, "recipient_secret_mismatch" if material["blocked"] else None
            classification = "native_receive_recipient_key_binding" if blocked else "native_receive_not_blocked"
            attempted = "Run native receive on the authentic delegated delivery using a fresh incorrect recipient secret."
            scope = "Delegated delivery and public material are stolen without agentSK; inability to receive prevents construction of a valid request."
        after = _facts(client)
        return _record(case_id, "stolen_material_without_agent_secret", mode, scope, attempted, before, after,
                       blocked=blocked, accepted_before_judge=[accepted] if mode != "darlt" else [],
                       classification=classification, rejection_reason=reason,
                       atomicity_passed=_atomic(before, after, accepted, mode, 1),
                       request_sent=mode != "darlt")


def _quota(root, bridge, issuer, mode):
    case_id = mode + "-agent-budget-64-exhausted"
    with _fixture(root, bridge, issuer, mode, case_id) as (_, _, client):
        burn = _burn(client, 56)
        for _ in range(8):
            accepted, _, _ = _attempt(client, "search_inventory", _arguments("search_inventory"))
            if not accepted:
                raise ValueError("misuse_precondition_native_burn_rejected")
        burn = {"accepted_requests": 15, "accepted_units": 64,
                "batch_requests": 7, "single_requests": 8}
        before = _facts(client)
        accepted, _, reason = _attempt(client, "search_inventory", _arguments("search_inventory"))
        after = _facts(client)
        return _record(case_id, "agent_budget_exhaustion", mode,
                       {**burn, "schedule": "seven batch requests of 8 units, then eight single-unit searches",
                        "native_wallet_capacity": 1024 if mode == "sma" else None,
                        "agent_limit": None if mode == "sma" else 64},
                       "Request unit 65 after 64 successful units.", before, after,
                       blocked=not accepted, accepted_before_judge=[accepted],
                       classification="no_native_agent_quota_in_shared_1024_wallet" if accepted and mode == "sma" else "quota_or_native_scope_rejected" if not accepted else "extra_unit_accepted",
                       rejection_reason=reason, atomicity_passed=_atomic(before, after, accepted, mode, 1))


def _batch_cases(root, bridge, issuer, mode):
    result = []
    for slug in ["mixed-resource", "remaining-under-eight", "already-used-position"]:
        case_id = mode + "-batch-" + slug
        with _fixture(root, bridge, issuer, mode, case_id) as (_, _, client):
            if slug == "already-used-position" and mode == "oauth":
                facts = _facts(client)
                result.append(_record(case_id, "batch_atomicity", mode,
                              "OAuth has no native unit-position coordinate.",
                              "Batch containing a previously consumed native position.", facts, facts,
                              applicable=False, classification="not_applicable_no_native_unit_coordinates"))
                continue
            arguments = _arguments("batch_query", mixed=slug == "mixed-resource")
            options = {}
            if slug == "remaining-under-eight":
                capacity = 1024 if mode == "sma" else 64
                burn = _burn(client, capacity - 3)
                precondition = {**burn, "native_or_grant_capacity": capacity, "remaining_units": 3,
                                "no_synthetic_SMA_agent_quota": mode == "sma"}
            elif slug == "already-used-position":
                accepted, _, _ = _attempt(client, "search_inventory", _arguments("search_inventory"), positions=[0])
                if not accepted:
                    raise ValueError("misuse_precondition_first_position_rejected")
                options["positions"] = list(range(8))
                precondition = "Position 0 was accepted at this service; positions 1..7 remain unused."
            else:
                precondition = "One batch has seven allowed-resource items and one restricted-resource item; its top-level resource is allowed."
            before = _facts(client)
            accepted, _, reason = _attempt(client, "batch_query", arguments, **options)
            after = _facts(client)
            result.append(_record(case_id, "batch_atomicity", mode, precondition,
                          {"tool": "batch_query", "units": 8, "variant": slug}, before, after,
                          blocked=not accepted, accepted_before_judge=[accepted],
                          classification="entire_batch_rejected" if not accepted else "entire_batch_accepted",
                          rejection_reason=reason, atomicity_passed=_atomic(before, after, accepted, mode, 8)))
    return result


def _two_server_case(root, bridge, issuer, mode, *, actor=None):
    suffix = "double-use" if actor is None else "overlap-second-agent" if actor == "second" else "delegate-then-self"
    case_id = mode + "-" + suffix
    category = "cross_verifier_double_use" if actor is None else "malicious_owner_overlapping_allocation"
    with _fixture(root, bridge, issuer, mode, case_id) as (stack, _, a):
        if mode == "oauth" and actor is not None:
            facts = _facts(a)
            return _record(case_id, category, mode,
                           "An ordinary user has neither the AS signing key nor a native anonymous pool-delegation interface.",
                           "Allocate the same native pool to another agent." if actor == "second" else "Delegate a pool and then self-allocate the same pool.",
                           facts, facts, applicable=False,
                           classification="not_applicable_no_user_pool_delegation_interface")
        allocation = None
        if mode == "darlt" and actor is not None:
            allocation = bridge.command("reallocate", instance=a.instance, actor=actor)
            _clock_free(allocation)
        server_b = stack.enter_context(ToolServer(root / case_id / "B", bridge.service_bridge, issuer.verifier(),
                                                  domain=a.server.domain, verifier_id="bank-B"))
        b = _clone_for_server(stack, a, server_b, actor=actor or "agent")
        before = {"bank_A": _facts(a), "bank_B": _facts(b)}
        accepted_a, result_a, reason_a = _attempt(a, "search_inventory", _arguments("search_inventory"), positions=[0])
        accepted_b, result_b, reason_b = _attempt(b, "search_inventory", _arguments("search_inventory"), positions=[0])
        after = {"bank_A": _facts(a), "bank_B": _facts(b)}
        judged = False
        key_matches_expected = None
        if accepted_a and accepted_b and mode != "oauth":
            verdict = a.server.bridge.command("judge", evidence_a=result_a["evidence_handle"], evidence_b=result_b["evidence_handle"])
            _clock_free(verdict)
            classification = verdict["classification"]
            expected_key = "agent_public_key" if mode == "darlt" and actor is None else "user_public_key"
            key_matches_expected = verdict.get("public_key") == a.init_result.get(expected_key)
            judged = True
        elif accepted_a and accepted_b:
            classification = "authenticated_subject_agent"
        else:
            classification = "one_or_both_requests_rejected"
        precondition = {"independent_service_states": True, "same_logical_domain": True,
                        "fresh_nonce_and_distinct_request_contexts": True,
                        "same_native_position": 0 if mode != "oauth" else None,
                        "OAuth_same_JWT_and_holder_key_fresh_htu_nonce_jti": mode == "oauth"}
        if actor is not None:
            precondition.update(actor=actor,
                                owner_state_fork=bool(allocation and allocation.get("adversarial_owner_state_fork")),
                                shared_original_wallet_copy=mode == "sma")
        return _record(case_id, category, mode, precondition,
                       "Accept each request at a distinct service, then run native Judge/Identify." if mode != "oauth" else
                       "Send two freshly DPoP-signed requests using the same JWT to the same logical audience at two independent services.",
                       before, after, blocked=not (accepted_a and accepted_b),
                       accepted_before_judge=[accepted_a, accepted_b], classification=classification,
                       native_judge_executed=judged, native_unit_judge_available=mode != "oauth",
                       judge_key_matches_expected_identity=key_matches_expected,
                       rejection_reason=[reason_a, reason_b],
                       atomicity_passed=(_atomic(before["bank_A"], after["bank_A"], accepted_a, mode, 1)
                                         and _atomic(before["bank_B"], after["bank_B"], accepted_b, mode, 1)),
                       attribution_granularity="user only; cannot distinguish shared-wallet actors" if mode == "sma" else
                       "authenticated subject only; no native unit Judge" if mode == "oauth" else "native agent versus malicious allocating user")


def validate_outcomes(records):
    """Check the fixed 36-case contract, including native identity attribution."""
    if len(records) != 36 or len({r["case_id"] for r in records}) != 36:
        raise ValueError("misuse_case_inventory")
    for row in records:
        mode, category = row["mode"], row["category"]
        if not row["applicable"]:
            expected_na = mode == "oauth" and (
                category == "malicious_owner_overlapping_allocation" or
                row["case_id"] == "oauth-batch-already-used-position")
            if not expected_na or row.get("blocked") is not None:
                raise ValueError("misuse_unexpected_not_applicable")
            continue
        if row.get("atomicity_passed") is not True:
            raise ValueError("misuse_atomicity_gate_failed")
        if category in ("cross_verifier_double_use", "malicious_owner_overlapping_allocation"):
            expected = "authenticated_subject_agent" if mode == "oauth" else (
                "agent" if mode == "darlt" and category == "cross_verifier_double_use" else "user")
            if (row.get("blocked") is not False or row.get("accepted_before_judge") != [True, True]
                    or row.get("classification") != expected):
                raise ValueError("misuse_attribution_outcome_failed")
            if mode != "oauth" and (row.get("native_judge_executed") is not True or
                                     row.get("judge_key_matches_expected_identity") is not True):
                raise ValueError("misuse_native_judge_identity_failed")
        else:
            expected_block = not (mode == "sma" and not (
                category == "batch_atomicity" and not row["case_id"].endswith("mixed-resource")))
            if row.get("blocked") is not expected_block:
                raise ValueError("misuse_accept_reject_outcome_failed")
    return {"passed": True, "records": 36, "applicable": 33, "not_applicable": 3}


def run_misuse(binary, outdir):
    """Return the 36 concrete functional records, with no timing/model calls."""
    outdir = Path(outdir)
    outdir.mkdir(parents=True, exist_ok=True)
    root = Path(tempfile.mkdtemp(prefix="misuse-", dir=outdir))
    issuer = OAuthIssuer()
    records = []
    with ExitStack() as stack:
        bridge, verifier = stack.enter_context(native_pair(binary))
        bridge.service_bridge = verifier
        import json
        (outdir / "native_processes.json").write_text(json.dumps(process_record(bridge, verifier), indent=2) + "\n")
        if verifier.command("metadata").get("clock_free") is not True:
            raise ValueError("misuse_server_native_clock_not_disabled")
        metadata = bridge.command("metadata")
        _clock_free(metadata)
        if metadata.get("clock_free") is not True:
            raise ValueError("misuse_native_clock_not_disabled")
        for mode in MODES:
            records.extend(_authorization_cases(root, bridge, issuer, mode))
            records.append(_stolen_material(root, bridge, issuer, mode))
            records.append(_quota(root, bridge, issuer, mode))
            records.extend(_batch_cases(root, bridge, issuer, mode))
            records.append(_two_server_case(root, bridge, issuer, mode))
            records.append(_two_server_case(root, bridge, issuer, mode, actor="second"))
            records.append(_two_server_case(root, bridge, issuer, mode, actor="user"))
    _clock_free(records)
    validate_outcomes(records)
    return records
