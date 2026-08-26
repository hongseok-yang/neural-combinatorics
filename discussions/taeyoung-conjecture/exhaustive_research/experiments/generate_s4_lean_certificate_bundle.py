"""Generate the final theorem bundling every checked S4 algebraic layer."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


PREFIX = "Taeyoung.Methods.RootedSOS"


def write_if_changed(path: Path, contents: str) -> None:
    if path.exists() and path.read_text(encoding="utf-8") == contents:
        return
    path.write_text(contents, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tag", required=True)
    parser.add_argument("--lean-root", default="lean/Taeyoung/Methods/RootedSOS")
    args = parser.parse_args()
    if re.fullmatch(r"[A-Z][A-Za-z0-9]*", args.tag) is None:
        raise ValueError(f"invalid Lean tag: {args.tag}")

    tag = f"S4{args.tag}"
    module = f"{tag}AlgebraicCertificate"
    namespace = f"{tag}AlgebraicCertificate"
    source = f"""import {PREFIX}.S4YoungPullbackChecks
import {PREFIX}.{tag}CommonExact
import {PREFIX}.{tag}ExceptionalChecks
import {PREFIX}.{tag}CommonGroupChecks
import {PREFIX}.{tag}ExceptionalGroupChecks
import {PREFIX}.{tag}CoefficientChecks

namespace {PREFIX}.{namespace}

/-!
The fully checked finite-algebra portion of one S4 interval certificate.

This bundles the common Gram products, positivity of every full correction,
the certificate-independent S4 Young pullback, reconstruction of common and
exceptional fixed-density group totals, and all target coefficient equations.
The later analytic graphon interpretation is deliberately a separate theorem.
-/
structure AlgebraicCertificateVerified : Prop where
  pullback : S4YoungPullback.PullbackFoundationVerified
  commonGram : {tag}CommonExact.CommonGramVerified
  exceptionalPSD : {tag}ExceptionalChecks.ExceptionalPSDVerified
  commonGroups : {tag}CommonGroupChecks.CommonGroupTotalsVerified
  exceptionalGroups : {tag}ExceptionalGroupChecks.ExceptionalGroupTotalsVerified
  coefficients : {tag}CoefficientChecks.CoefficientIdentityVerified

theorem algebraic_certificate_verified : AlgebraicCertificateVerified where
  pullback := S4YoungPullback.pullback_foundation_verified
  commonGram := {tag}CommonExact.common_gram_verified
  exceptionalPSD := {tag}ExceptionalChecks.exceptional_psd_verified
  commonGroups := {tag}CommonGroupChecks.common_group_totals_verified
  exceptionalGroups := {tag}ExceptionalGroupChecks.exceptional_group_totals_verified
  coefficients := {tag}CoefficientChecks.coefficient_identity_verified

end {PREFIX}.{namespace}
"""
    lean_root = Path(args.lean_root)
    lean_root.mkdir(parents=True, exist_ok=True)
    write_if_changed(lean_root / f"{module}.lean", source)
    print(f"wrote {PREFIX}.{module}")


if __name__ == "__main__":
    main()
