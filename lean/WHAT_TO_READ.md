# What to read in the Smale rate formalization

Start with [the theorem audit](AUDIT.md), generated directly from Lean's kernel axiom inspection and elaborated signature checks. [The paper correspondence](CLAIM_MAP.tsv) maps each declaration to version `1.00` of the paper. [The audit notes](AUDIT_NOTES.md) summarize the scope, route differences, and retired auxiliary rows.

| Question | Where to read |
|---|---|
| What is formalized for Theorem 1.1 (`K(d) <= (4/y) exp(-mu(y^{1/d}))`)? | `thm_1_1_given_background` in [Statements.lean](SmaleRate/Paper/Statements.lean) proves the bound for every integer `d >= 2` and `y in (0, 1)` given `JordanCurveFact`, `CoefficientUpperFact`, and the two refereed cited results `betsakos_2013` and `dlmf_19_9_5`. The unconditional row `thm_1_1` remains `OPEN`. |
| What is formalized for Corollary 1.2 (`K(d) < 4 - 4 / log d`, `d >= 8`)? | `cor_1_2_given_background` in [Statements.lean](SmaleRate/Paper/Statements.lean) proves the strict bound under the same two background hypotheses and two refereed cited results. All thirteen finite cases `8 <= d <= 20` (Table 3) are kernel-proved in Lean from standard axioms alone (`TableCertificates.lean`). The unconditional row `cor_1_2` remains `OPEN`. |
| What is proved for the limit `(4 - B(d)) log d -> 2 pi^2` (Proposition 3.4)? | `prop_3_4_lower_error`, `prop_3_4_upper`, and `prop_3_4_limit` in [Statements.lean](SmaleRate/Paper/Statements.lean) are proved from `dlmf_19_9_5` alone, with no background hypotheses and no Betsakos input. |
| What is proved from Lean's three standard axioms alone? | 160 declarations, including all 65 Table 3 rows, Smale's `K(d) <= 4` (`smale_bound`), `K(d) < 4` (`kd_lt_four`), `lim K(d) = sup K(d) = 4` (`kd_limit_and_sup`), exact `K(d) = (d-1)/d` for `d <= 4` (`small_degrees`), monotonicity (`kd_monotone`), and all earlier-bound comparisons. |
| What about Remark 3.5 (`d = 7, 8`) and Table 2 AGM values? | Proved in Lean via finite rational AGM interval covers (`SmaleRate/Proofs/AGMCertificates.lean` and `SmaleRate/Proofs/Generated/`) using `dlmf_19_8_5` and `dlmf_19_9_5`. |
| Are Sections 4 and 5 of the expanded edition (Theorems 1.3, 1.4, Corollary 1.5) formalized? | No. The formalization covers Sections 1 through 3 shared by both editions. `expanded_lower_bound` and `expanded_upper_bound` remain `OPEN`. |
| Which declarations are `OPEN` or `RETIRED`? | The 34 `OPEN` rows are listed in [OPEN_ROWS.txt](OPEN_ROWS.txt) and excluded from the comparator. Eleven auxiliary Jatar-Ng declarations are retained in the formalization and marked `RETIRED` in [CLAIM_MAP.tsv](CLAIM_MAP.tsv); they are not printed in `v1.00` and are unused by any printed theorem. |

## The four assumptions behind Theorem 1.1 and Corollary 1.2

The paper's page-1 footnote states that Theorem 1.1 and Corollary 1.2 are proved in Lean 4 from Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and **four assumptions**, and checked with `lake comparator`. Although the repository's full comparator scope permits five cited axioms in total, Theorem 1.1 and Corollary 1.2 use **only two** of those five cited axioms together with **two** explicit background hypotheses — making exactly four assumptions beyond Lean's three standard axioms:

| Paper result | Lean declaration | `#print axioms` beyond Lean's three standard axioms (2 cited axioms) | Explicit `Prop` hypotheses in the theorem type (2 background hypotheses) |
|---|---|---|---|
| **Theorem 1.1** | `SmaleRate.Paper.thm_1_1_given_background` | `SmaleRate.Cited.betsakos_2013`, `SmaleRate.Cited.dlmf_19_9_5` | `SmaleRate.Background.JordanCurveFact`, `SmaleRate.Background.CoefficientUpperFact` |
| **Corollary 1.2** | `SmaleRate.Paper.cor_1_2_given_background` | `SmaleRate.Cited.betsakos_2013`, `SmaleRate.Cited.dlmf_19_9_5` | `SmaleRate.Background.JordanCurveFact`, `SmaleRate.Background.CoefficientUpperFact` |

The remaining three cited axioms in the repository's five-axiom comparator list do **not** appear in `#print axioms` for Theorem 1.1 or Corollary 1.2:
- `SmaleRate.Cited.dlmf_19_8_5` (refereed) is used only by the Table 2 and Remark 3.5 AGM interval enclosures (and elliptic endpoint limits).
- `SmaleRate.Cited.jatar_ng_2026_theorem1_v` and `SmaleRate.Cited.jatar_ng_2026_sec1_2_leading_lt_one` (unrefereed) are used only by retired auxiliary declarations not printed in version `1.00`.

## Results taken as given

### Refereed cited axioms (`SmaleRate/Cited/Approved.lean`)

| Lean axiom | Used by | Source |
|---|---|---|
| `SmaleRate.Cited.betsakos_2013` | Theorem 1.1, Corollary 1.2 (conditional forms) | D. Betsakos, *J. Aust. Math. Soc.* 94 (2013), Theorem 1.1, p. 146, [DOI 10.1017/S1446788712000559](https://doi.org/10.1017/S1446788712000559) (inequality only). |
| `SmaleRate.Cited.dlmf_19_9_5` | Lemma 2.1, Theorem 1.1, Corollary 1.2, Proposition 3.4 | NIST DLMF [19.9.5](https://dlmf.nist.gov/19.9.E5) (Lehto-Virtanen 1973, p. 62). |
| `SmaleRate.Cited.dlmf_19_8_5` | Table 2 and Remark 3.5 AGM enclosures (not Theorem 1.1 or Corollary 1.2) | NIST DLMF [19.8.5](https://dlmf.nist.gov/19.8.E5) (elliptic integral AGM identity). |

### Named background hypotheses (`SmaleRate/Defs/BackgroundFacts.lean`, explicit `Prop` binders)

| Lean hypothesis | Used by | Mathematical statement and source |
|---|---|---|
| `SmaleRate.Background.JordanCurveFact` | Theorem 1.1, Corollary 1.2, and conditional geometric consequences | A bounded planar Jordan domain has simply connected interior and connected complement of its closure (classical Jordan-Schoenflies theorem). |
| `SmaleRate.Background.CoefficientUpperFact` | Theorem 1.1, Corollary 1.2, and conditional capacity consequences | For a compact connected nontrivial continuum `Q` with connected complement and exterior conformal map `phi(z) = a z + O(1)`, `capacityTD Q <= |a|` (T. Ransford, *Potential Theory in the Complex Plane*, 1995, Section 5.2 / Corollary 5.2.2 and Section 5.5 / Theorem 5.5.2). |

### Auxiliary unrefereed axioms (`SmaleRate/Cited/JatarNg.lean`, retired rows only)

| Lean axiom | Used by | Source |
|---|---|---|
| `SmaleRate.Cited.jatar_ng_2026_theorem1_v` | Retired auxiliary declarations only (no printed `v1.00` claim) | A. Jatar and T. W. Ng, [arXiv:2608.27047v1](https://arxiv.org/abs/2608.27047v1) (unrefereed preprint), Theorem 1(v), Section 1.2. |
| `SmaleRate.Cited.jatar_ng_2026_sec1_2_leading_lt_one` | Retired auxiliary declarations only (no printed `v1.00` claim) | A. Jatar and T. W. Ng, [arXiv:2608.27047v1](https://arxiv.org/abs/2608.27047v1) (unrefereed preprint), Section 1.2 observation. |

## Proof route differences

Where the Lean formalization takes a different route from the printed exposition:

- **Table 3 (Corollary 1.2, Step 2, degrees `8 <= d <= 20`):** proved completely inside Lean from standard axioms alone via rational Taylor/logarithm/`pi` bounds (`SmaleRate/Proofs/TableCertificates.lean`), with no external computer-check hypothesis.
- **Remark 3.5 and Table 2 (`d = 7, 8`):** proved inside Lean via finite dyadic rational AGM interval covers (`SmaleRate/Proofs/AGMCertificates.lean` and `SmaleRate/Proofs/Generated/`) from DLMF 19.8.5 and 19.9.5.
- **Small degrees (`d <= 4`), `K(d) <= 4`, `K(d) < 4`, `lim K(d) = sup K(d) = 4`, and monotonicity:** proved unconditionally from Lean's three standard axioms, reusing the companion `Smale/` modules documented in [Provenance030/README.md](Provenance030/README.md).
- **Proposition 3.4 lower error:** proved from DLMF 19.9.5 alone for both an elementary choice `L = 1 / (log d)^2` and the paper's `L = pi^2 / (2 (log d)^2)` (`prop_selected_L`).

## Verification of this release

All checks below ran on the exact `.lean`, `comparator/`, and audit files of this release:

- **Clean cold build from empty (`./scripts/check.sh --final`, Mathlib cached):** **PASS** (`rc=0`, `4h46m04s`, single-thread peak RSS `8.09 GB`, `SmaleRate/Paper/Statements.lean` `7.71 GB`, heaviest interval-cover chunk modules `8.08 GB`, `367/367` modules built, `AUDIT.md` regenerated with zero diff, only the 34 listed `OPEN` placeholders present).
- **Per-module kernel `.olean` replay (`leanchecker` across all 367 modules):** **PASS** (`rc=0`, `366` modules passed, `1` empty parent module `SmaleRate` verified to contain 0 constants, `0` failures, total `6,122.04 s`, peak RSS `7.19 GB`).
- **Standard minimal-mode `lake --no-cache comparator --config=comparator.json`** (257 selected statements, 34 `OPEN` excluded, 8 permitted axioms, challenge imports `SmaleRate.Defs.*` and `SmaleRate.Cited.*` only): **ACCEPTED** (`rc=0`, `4h44m23s`, max RSS `4.06 GB`), printing `Lean default kernel accepts the solution` and `Your solution is okay!`.
- **Paranoid `lake --no-cache comparator --paranoid --config=comparator.json`** (`5h00m49s`, max RSS `4.06 GB`): **4 of 6 kernels accept and 2 do not apply**. `Lean default kernel`, `Lean paranoid kernel`, `lean4lean` (`80,578` declarations), and `nanoda` all accept the solution; `con-leche` and `con-ron` both decline any non-standard cited axiom by design (`rc=2` at `SmaleRate.Cited.dlmf_19_9_5`), causing the outer `--paranoid` wrapper to exit `rc=1` (`error: con-leche exited with 2`).
- **Standalone independent export checkers** on the 295-name selected-scope `leanexport` (`2,721,131,758` bytes, SHA-256 `9cb03c1170d8235ff97a8a346ffa6ab0ac259b9723fa9bacc2aeb465b37b1ac1`, `80,581` records, `257/257` selected statements present, `0/34` `OPEN` statements present, exact 8 permitted axioms, `0` `sorryAx`): **4 of 6 accept** (`leanchecker`, `leanchecker-paranoid`, `lean4lean`, `nanoda` under a strict 8-axiom config checking `82,979` declarations) and **2 do not apply** (`con-leche` and `con-ron`, both `rc=2` on the non-standard cited axiom `SmaleRate.Cited.dlmf_19_9_5`). A negative control deleting one middle line from the export was **rejected** (`rc=1`).
- **Hosted build:** No GitHub Actions build ran while this repository was private; in its place before tagging, `./scripts/check.sh --final` is verified on a fresh clone of the pushed commit, and GitHub Actions runs on the tag commit once the repository goes public.

See [Comparison instructions](../comparator/README.md).

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
