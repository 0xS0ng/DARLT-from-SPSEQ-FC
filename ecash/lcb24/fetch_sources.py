#!/usr/bin/env python3
"""Fetch the four pinned author modules used by the native LCB24 adapter."""
import hashlib
from pathlib import Path
from urllib.request import urlopen

COMMIT = '5dfbf5609ba528be31e6a50ebce0f49037bdb159'
FILES = {
    'divtokens/src/dap/circuit.rs': 'f8e69af05b40010c0318470fd212b8041236dd415e6f2082b3e81e424cf03ee0',
    'divtokens/src/schnorr/mod.rs': '7b01a0a79ed4f46784f700b3cb028ea58ffe41679191d6059282e48281872537',
    'divtokens/src/schnorr/constraints.rs': '6f54c877cc54bff8743b1e1247c736d87f217b1b9b48b2aa05871c8e40284ef7',
    'divtokens/src/schnorr/params.rs': '465a3b7801c10a82010fce72e9de5cb3c03633b41046b9ed36c593dfe89dc049',
}
root = Path(__file__).resolve().parents[2] / 'source-cache' / 'private-billing'
for name, expected in FILES.items():
    target = root / name
    data = target.read_bytes() if target.exists() else urlopen(
        f'https://raw.githubusercontent.com/kev-liao/private-billing/{COMMIT}/{name}', timeout=60
    ).read()
    if hashlib.sha256(data).hexdigest() != expected:
        raise SystemExit(f'Pinned source hash mismatch: {name}')
    if not target.exists():
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    print(f'{expected}  {name}')
