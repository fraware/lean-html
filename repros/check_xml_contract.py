#!/usr/bin/env python3
"""Check actual XHTML output from XhtmlContractAudit.lean using an independent XML parser."""
import sys
import xml.etree.ElementTree as ET

EXPECTED = {
    "control-valid": True,
    "duplicate-typed-raw": False,
    "duplicate-sanitized": False,
    "duplicate-formal-witness": False,
    "nul-text": False,
    "nul-attribute": False,
    "unbound-namespace-prefix": False,
    "arbitrary-tag-name": False,
}


def main() -> int:
    seen = set()
    mismatches = 0
    for line in sys.stdin.buffer:
        if not line.startswith(b"XHTML_CASE\t"):
            if line.strip():
                sys.stderr.write(f"IGNORED: {line[:120]!r}\n")
            continue
        try:
            _, name_bytes, xml = line.rstrip(b"\r\n").split(b"\t", 2)
            name = name_bytes.decode("ascii")
        except (ValueError, UnicodeDecodeError) as exc:
            sys.stderr.write(f"Invalid record: {exc}\n")
            return 1
        if name not in EXPECTED or name in seen:
            sys.stderr.write(f"Unknown or duplicate case: {name}\n")
            return 1
        seen.add(name)
        try:
            ET.fromstring(xml)
            valid = True
            reason = "accepted"
        except ET.ParseError as exc:
            valid = False
            reason = str(exc)
        expected = EXPECTED[name]
        verdict = "MATCH" if valid == expected else "MISMATCH"
        print(f"{verdict:8} {name:28} xml_valid={valid:<5} {reason}")
        mismatches += valid != expected
    missing = EXPECTED.keys() - seen
    if missing:
        sys.stderr.write(f"Missing audit cases: {', '.join(sorted(missing))}\n")
    return 1 if missing or mismatches else 0


if __name__ == "__main__":
    raise SystemExit(main())
