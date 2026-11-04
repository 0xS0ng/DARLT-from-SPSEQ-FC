"""RFC 9068 access JWTs and RFC 9449 DPoP for the local experiment.

The verifier holds only the authorization server's public key. Replay, grant
scope, and quota decisions belong to the caller's SQLite transaction. DPoP
binds the token, HTTP method, and target URI, not a tool's JSON arguments.
"""

from __future__ import annotations

import base64
import hashlib
import hmac
import json
import math
import re
import secrets
import time
from urllib.parse import urlsplit, urlunsplit

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import ec, padding, rsa, utils

_B64 = re.compile(r"^[A-Za-z0-9_-]*$")
_ACCESS_TYPES = {"at+jwt", "application/at+jwt"}
_KID = "case_study-rsa-1"
_ISSUER = "https://darlt.test/issuer"
_CLIENT_ID = "darlt-case_study-agent"
_CLOCK_SKEW = 30
_DPOP_WINDOW = 60


def _canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False, allow_nan=False).encode("utf-8")


def _strict(data):
    def pairs(items):
        value = {}
        for key, item in items:
            if key in value:
                raise ValueError("duplicate_json_key")
            value[key] = item
        return value

    def constant(_):
        raise ValueError("nonfinite_json_number")

    def number(value):
        parsed = float(value)
        if not math.isfinite(parsed):
            raise ValueError("nonfinite_json_number")
        return parsed

    try:
        if isinstance(data, bytes):
            data = data.decode("utf-8")
        value = json.loads(data, object_pairs_hook=pairs, parse_constant=constant,
                           parse_float=number)
    except (UnicodeError, json.JSONDecodeError, TypeError) as exc:
        raise ValueError("invalid_json") from exc
    if not isinstance(value, dict):
        raise ValueError("json_object_required")
    return value


def _b64(value):
    return base64.urlsafe_b64encode(value).rstrip(b"=").decode("ascii")


def _unb64(value):
    if not isinstance(value, str) or not _B64.fullmatch(value) or len(value) % 4 == 1:
        raise ValueError("invalid_base64url")
    try:
        result = base64.b64decode(value + "=" * (-len(value) % 4),
                                  altchars=b"-_", validate=True)
    except (ValueError, base64.binascii.Error) as exc:
        raise ValueError("invalid_base64url") from exc
    if _b64(result) != value:
        raise ValueError("noncanonical_base64url")
    return result


def _text(value, name):
    if not isinstance(value, str) or not value or len(value) > 4096:
        raise ValueError(name)
    return value


def _same_text(left, right):
    if not isinstance(left, str) or not isinstance(right, str):
        return False
    try:
        return hmac.compare_digest(left.encode("utf-8"), right.encode("utf-8"))
    except UnicodeError:
        return False


def _number(value, name):
    if type(value) not in (int, float):
        raise ValueError(name)
    try:
        valid = math.isfinite(value)
    except (OverflowError, TypeError):
        valid = False
    if not valid:
        raise ValueError(name)
    return value


def _integer(value, name):
    if type(value) is not int or value < 0:
        raise ValueError(name)
    return value


def _attributes(value):
    if value is None:
        return None
    if isinstance(value, list):
        if any(not isinstance(x, str) or not x for x in value) or len(set(value)) != len(value):
            raise ValueError("access_attributes")
    elif isinstance(value, dict):
        if any(not isinstance(k, str) or not k or type(v) not in (str, int, bool)
               for k, v in value.items()):
            raise ValueError("access_attributes")
    else:
        raise ValueError("access_attributes")
    return value


def _scope(values):
    if isinstance(values, str):
        if values != " ".join(values.split()):
            raise ValueError("access_scope")
        values = values.split()
    if not isinstance(values, (list, tuple, set)):
        raise ValueError("access_scope")
    result = sorted(values) if isinstance(values, set) else list(values)
    for value in result:
        if not isinstance(value, str) or not value or any(
                not (ord(c) == 0x21 or 0x23 <= ord(c) <= 0x5B or 0x5D <= ord(c) <= 0x7E)
                for c in value):
            raise ValueError("access_scope")
    if len(set(result)) != len(result):
        raise ValueError("access_scope")
    return " ".join(result)


def _audiences(value):
    values = [value] if isinstance(value, str) else value
    if not isinstance(values, list) or not values:
        raise ValueError("access_audience")
    for item in values:
        _text(item, "access_audience")
    if len(set(values)) != len(values):
        raise ValueError("access_audience")
    return values


def _decode(token):
    if not isinstance(token, str) or len(token) > 65536:
        raise ValueError("jwt_format")
    pieces = token.split(".")
    if len(pieces) != 3 or any(not p for p in pieces):
        raise ValueError("jwt_format")
    header, claims = (_strict(_unb64(p)) for p in pieces[:2])
    signature = _unb64(pieces[2])
    return header, claims, signature, (pieces[0] + "." + pieces[1]).encode("ascii")


def new_dpop_key():
    return ec.generate_private_key(ec.SECP256R1())


def _jwk(public_key):
    if not isinstance(public_key, ec.EllipticCurvePublicKey) or not isinstance(public_key.curve, ec.SECP256R1):
        raise ValueError("dpop_public_key")
    numbers = public_key.public_numbers()
    return {"kty": "EC", "crv": "P-256", "x": _b64(numbers.x.to_bytes(32, "big")),
            "y": _b64(numbers.y.to_bytes(32, "big"))}


def thumbprint(public_key):
    return _b64(hashlib.sha256(_canonical(_jwk(public_key))).digest())


def _htu(url):
    _text(url, "dpop_htu")
    try:
        value = urlsplit(url)
        port = value.port
    except ValueError as exc:
        raise ValueError("dpop_htu") from exc
    if value.scheme.lower() not in ("http", "https") or not value.hostname or value.username or value.password:
        raise ValueError("dpop_htu")
    host = value.hostname.lower()
    if ":" in host:
        host = "[" + host + "]"
    if port is not None and (value.scheme.lower(), port) not in (("http", 80), ("https", 443)):
        host += ":" + str(port)
    return urlunsplit((value.scheme.lower(), host, value.path or "/", "", ""))


class OAuthVerifier:
    """A resource-server verifier with no authorization-server signing key."""

    def __init__(self, public_key, issuer=_ISSUER):
        if not isinstance(public_key, rsa.RSAPublicKey):
            raise ValueError("access_public_key")
        self.public_key = public_key
        self.issuer = _text(issuer, "access_issuer")
        self.iss = self.issuer

    def verify(self, token, audience, period, *, now=None):
        header, claims, signature, message = _decode(token)
        if set(header) - {"alg", "typ", "kid"} or header.get("alg") != "RS256":
            raise ValueError("access_header")
        if not isinstance(header.get("typ"), str) or header["typ"].lower() not in _ACCESS_TYPES:
            raise ValueError("access_type")
        if "kid" in header and header["kid"] != _KID:
            raise ValueError("access_key_id")
        try:
            self.public_key.verify(signature, message, padding.PKCS1v15(), hashes.SHA256())
        except (InvalidSignature, ValueError) as exc:
            raise ValueError("access_signature") from exc
        required = {"iss", "sub", "aud", "exp", "iat", "client_id", "jti", "scope", "cnf", "quota", "period"}
        if not required <= set(claims):
            raise ValueError("access_claims")
        for name in ("iss", "sub", "client_id", "jti"):
            _text(claims[name], "access_" + name)
        now = _number(time.time() if now is None else now, "clock")
        exp = _number(claims["exp"], "access_exp")
        issued = _number(claims["iat"], "access_iat")
        if claims["iss"] != self.issuer or exp <= now or issued > now + _CLOCK_SKEW or exp <= issued:
            raise ValueError("access_time_issuer")
        if "nbf" in claims:
            not_before = _number(claims["nbf"], "access_nbf")
            if not_before > now + _CLOCK_SKEW or not_before >= exp:
                raise ValueError("access_not_yet_valid")
        if _text(audience, "access_audience") not in _audiences(claims["aud"]):
            raise ValueError("access_audience")
        _integer(period, "access_period")
        if _integer(claims["period"], "access_period") != period:
            raise ValueError("access_period")
        _integer(claims["quota"], "access_quota")
        if not isinstance(claims["scope"], str) or _scope(claims["scope"]) != claims["scope"]:
            raise ValueError("access_scope")
        confirmation = claims["cnf"]
        if not isinstance(confirmation, dict) or set(confirmation) != {"jkt"} or len(_unb64(confirmation["jkt"])) != 32:
            raise ValueError("access_confirmation")
        if "attributes" in claims:
            _attributes(claims["attributes"])
        return claims

    verify_access = verify


class OAuthIssuer:
    def __init__(self, issuer=_ISSUER):
        self._key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
        self.issuer = _text(issuer, "access_issuer")
        self.iss = self.issuer

    def verifier(self):
        return OAuthVerifier(self._key.public_key(), self.issuer)

    def issue(self, dpop_public_key, audience, scopes, quota=64, subject="agent", period=1,
              attributes=None, *, lifetime=3600, now=None):
        now = int(time.time()) if now is None else _number(now, "clock")
        if _number(lifetime, "access_lifetime") <= 0:
            raise ValueError("access_lifetime")
        _audiences(audience)
        claims = {"iss": self.issuer, "sub": _text(subject, "access_subject"), "aud": audience,
                  "iat": now, "exp": now + lifetime, "client_id": _CLIENT_ID,
                  "jti": secrets.token_hex(16), "scope": _scope(scopes),
                  "cnf": {"jkt": thumbprint(dpop_public_key)},
                  "quota": _integer(quota, "access_quota"), "period": _integer(period, "access_period")}
        if attributes is not None:
            claims["attributes"] = _attributes(attributes)
        message = (_b64(_canonical({"alg": "RS256", "typ": "at+jwt", "kid": _KID}))
                   + "." + _b64(_canonical(claims))).encode("ascii")
        signature = self._key.sign(message, padding.PKCS1v15(), hashes.SHA256())
        return message.decode("ascii") + "." + _b64(signature)


def dpop_sign(key, token, url, nonce=None, *, jti=None, now=None):
    if not isinstance(key, ec.EllipticCurvePrivateKey) or not isinstance(key.curve, ec.SECP256R1):
        raise ValueError("dpop_private_key")
    _text(token, "access_token")
    try:
        digest = hashlib.sha256(token.encode("ascii")).digest()
    except UnicodeError as exc:
        raise ValueError("access_token") from exc
    header = {"typ": "dpop+jwt", "alg": "ES256", "jwk": _jwk(key.public_key())}
    claims = {"jti": secrets.token_hex(16) if jti is None else _text(jti, "dpop_jti"),
              "htm": "POST", "htu": _htu(url), "iat": int(time.time()) if now is None else _number(now, "clock"),
              "ath": _b64(digest)}
    if nonce is not None:
        claims["nonce"] = _text(nonce, "dpop_nonce")
    message = (_b64(_canonical(header)) + "." + _b64(_canonical(claims))).encode("ascii")
    r, s = utils.decode_dss_signature(key.sign(message, ec.ECDSA(hashes.SHA256())))
    return message.decode("ascii") + "." + _b64(r.to_bytes(32, "big") + s.to_bytes(32, "big"))


def verify_dpop(proof, token, claims, url, expected_nonce=None, *, now=None):
    header, payload, signature, message = _decode(proof)
    if set(header) != {"typ", "alg", "jwk"} or header["typ"] != "dpop+jwt" or header["alg"] != "ES256":
        raise ValueError("dpop_header")
    jwk = header["jwk"]
    if not isinstance(jwk, dict) or set(jwk) != {"kty", "crv", "x", "y"} or jwk["kty"] != "EC" or jwk["crv"] != "P-256":
        raise ValueError("dpop_jwk")
    x, y = _unb64(jwk["x"]), _unb64(jwk["y"])
    if len(x) != 32 or len(y) != 32 or len(signature) != 64:
        raise ValueError("dpop_encoding")
    try:
        public_key = ec.EllipticCurvePublicNumbers(int.from_bytes(x, "big"), int.from_bytes(y, "big"), ec.SECP256R1()).public_key()
        r, s = int.from_bytes(signature[:32], "big"), int.from_bytes(signature[32:], "big")
        public_key.verify(utils.encode_dss_signature(r, s), message, ec.ECDSA(hashes.SHA256()))
    except (ValueError, InvalidSignature) as exc:
        raise ValueError("dpop_signature") from exc
    if not isinstance(claims, dict) or not isinstance(claims.get("cnf"), dict):
        raise ValueError("dpop_confirmation")
    expected_thumbprint = claims["cnf"].get("jkt")
    if not _same_text(thumbprint(public_key), expected_thumbprint):
        raise ValueError("dpop_confirmation")
    required = {"jti", "htm", "htu", "iat", "ath"}
    if not required <= set(payload) or payload["htm"] != "POST" or _htu(payload["htu"]) != _htu(url):
        raise ValueError("dpop_method_uri")
    issued = _number(payload["iat"], "dpop_iat")
    now = _number(time.time() if now is None else now, "clock")
    if abs(now - issued) > _DPOP_WINDOW:
        raise ValueError("dpop_time")
    try:
        expected_hash = _b64(hashlib.sha256(_text(token, "access_token").encode("ascii")).digest())
    except UnicodeError as exc:
        raise ValueError("access_token") from exc
    if not _same_text(payload["ath"], expected_hash):
        raise ValueError("dpop_token_hash")
    if expected_nonce is not None:
        if not _same_text(payload.get("nonce"), _text(expected_nonce, "dpop_nonce")):
            raise ValueError("dpop_nonce")
    return _text(payload["jti"], "dpop_jti")
