#!/usr/bin/env python3
"""Export the exact certificate to portable gzipped JSON (integers/rationals as
strings), so the theorem's data is not locked in a Python pickle.
Round-trips: python3 export_certificate_json.py [--check]"""
import pickle, json, gzip, sys
from fractions import Fraction

C = pickle.load(open("data/certificate.pkl", "rb"))

def enc(x):
    if isinstance(x, Fraction):
        return {"frac": [str(x.numerator), str(x.denominator)]}
    if isinstance(x, (list, tuple)):
        return [enc(v) for v in x]
    if hasattr(x, "tolist"):          # numpy arrays (object/int)
        return enc(x.tolist())
    if isinstance(x, dict):
        return {str(k): enc(v) for k, v in x.items()}
    if isinstance(x, (int, str, bool)) or x is None:
        return int(x) if isinstance(x, bool) is False and isinstance(x, int) else x
    return str(x)

payload = {k: enc(v) for k, v in C.items()}
with gzip.open("data/certificate.json.gz", "wt") as f:
    json.dump(payload, f)
print("wrote data/certificate.json.gz")

if "--check" in sys.argv:
    with gzip.open("data/certificate.json.gz", "rt") as f:
        back = json.load(f)
    assert set(back) == set(payload)
    print("round-trip keys OK:", sorted(back))
