"""Case-study command-line entry point and CSV output helper."""
from __future__ import annotations
import csv

def write_csv(path, records):
    keys = list(dict.fromkeys(k for row in records for k in row))
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, keys); writer.writeheader(); writer.writerows(records)

def main():
    from .workflows import main as execute
    return execute()

if __name__ == "__main__":
    raise SystemExit(main())
