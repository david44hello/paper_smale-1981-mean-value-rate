# How fast Smale's mean value constants (1981) approach 4

The paper's link is on the [front page of this repository](https://github.com/david44hello/paper_smale-1981-mean-value-rate).

Conditional forms of Theorem 1.1 and Corollary 1.2 are proved in Lean 4 using two refereed cited results (Betsakos 2013, Theorem 1.1; NIST DLMF 19.9.5) and two explicit named background hypotheses (planar Jordan-curve topology and the exterior conformal-map transfinite-diameter coefficient upper bound). Proposition 3.4 and Lemma 2.1 are proved from NIST DLMF 19.9.5 alone, and all thirteen finite interval-arithmetic cases for degrees 8 through 20 in Corollary 1.2 (Table 3) are proved inside Lean from standard axioms alone. Unconditional forms of the main bounds, the expanded-only bounds of Sections 4 and 5, and other open entries remain explicitly marked `OPEN`.

For the exact statements, assumptions, open claims, and verification details, see [What to read](WHAT_TO_READ.md).

## How to verify

Install Git, Python 3, ripgrep, and elan (the Lean toolchain manager). From the `lean/` directory of a Git checkout, run:

```sh
lake exe cache get
./scripts/check.sh --final
```

This builds the full proof, checks the source policy, regenerates the Lean axiom audit, and verifies that the only placeholders are the 34 listed `OPEN` declarations. The final two lines read:

```text
FINAL GATE PASS: placeholders only as whole bodies of the 34 listed OPEN rows; statuses match the list.
PASS (final): project builds; source policy passes; the only gaps are the listed OPEN rows.
```

Peak memory during a single-thread build from empty is 8.09 GB (7.71 GB for `SmaleRate/Paper/Statements.lean` and 8.08 GB for the heaviest interval-cover chunk modules) with Mathlib cached.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
