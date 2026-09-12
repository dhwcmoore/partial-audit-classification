#!/usr/bin/env python3
"""fixture_check.py -- runs the OCaml CLI (extracted from the Coq
development) and checks its output against the classifications the
corresponding rocq/Cases.v Examples prove by `reflexivity`. This is C17
in the sense of the sibling proof-carrying-* repositories: it checks
*observed agreement* between the extracted executable and the formally
characterised decisions. That is testing, not proof; the proof is
rocq/Cases.v itself, checked by coqchk.
"""

import subprocess
import sys

EXPECTED = [
    # Wirecard: the same four fixtures rocq/Cases.v proves by reflexivity
    # (fixture{1,2,3,4}_decision), checked here against decide_opinion's
    # actual extracted output rather than the classification alone.
    "Opinion:         Inadmissible [NotVerified(Undefined)]",
    "Opinion:         Inadmissible [MissingCertificate]",
    "Opinion:         Unqualified",
    "Opinion:         Inadmissible [InvalidCertificate]",
    # Continuous auditing: matches eight_residuals_from_pipeline and
    # no_residual_is_verified.
    "Txn 0: Verified",
    "Txn 1: Verified",
    "Txn 2: Undefined",
    "Txn 9: Undefined",
    "Residual register entries after this run: 8",
    'Residual register entries after "clearing" the dashboard: 8',
    # SQL Unknown: matches absent_score_undefined, honest_zero_verified,
    # absence_distinguishable_from_honest_zero, and the renderer pair.
    "nullable_score_to_classification(None)   = Undefined",
    "nullable_score_to_classification(Some 0) = Verified",
    "distinguishable: yes",
    "silently_converted_render(Unknown) = 0",
    "silently_converted_render(Score 0) = 0",
    "disciplined_render(Unknown) = RUndefined",
    "disciplined_render(Score 0) = RNumeric 0",
    "distinguishable under the disciplined renderer: yes",
]


def main() -> int:
    try:
        result = subprocess.run(
            ["dune", "exec", "ocaml/cli/main.exe"],
            cwd=".",
            capture_output=True,
            text=True,
            timeout=60,
        )
    except FileNotFoundError:
        print("dune not found on PATH; run `make ocaml` first", file=sys.stderr)
        return 2

    if result.returncode != 0:
        print("CLI exited non-zero:", result.returncode, file=sys.stderr)
        print(result.stderr, file=sys.stderr)
        return 1

    output = result.stdout
    missing = [line for line in EXPECTED if line not in output]

    if missing:
        print("FIXTURE CHECK FAILED -- missing expected lines:", file=sys.stderr)
        for line in missing:
            print(f"  {line!r}", file=sys.stderr)
        print("\n--- actual CLI output ---", file=sys.stderr)
        print(output, file=sys.stderr)
        return 1

    print(f"fixture_check: {len(EXPECTED)}/{len(EXPECTED)} expected lines present. PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
