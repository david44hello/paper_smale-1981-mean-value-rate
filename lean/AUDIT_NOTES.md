# Audit notes for the Smale rate formalization (v1.00)

This file documents the proof scope, external inputs, explicit background hypotheses, route differences, and retired declarations for version `1.00` of *How fast Smale's mean value constants (1981) approach 4* (focused edition, 12 pages) and *How fast Smale's mean value constants (1981) approach 4, and other miscellanea* (expanded edition, 48 pages).

## Summary of audited declarations

Of 291 Lean declarations in `SmaleRate/Paper/Statements.lean`:
- **160 `PROVED`**: proved from Lean's three standard axioms alone (`propext`, `Classical.choice`, `Quot.sound`). Includes all 65 Table 3 bounds and rounding inequalities for degrees 8 through 20, Smale's bound `K(d) <= 4`, strict `K(d) < 4`, `lim K(d) = sup K(d) = 4`, exact `K(d) = (d-1)/d` for `d <= 4`, monotonicity of `K(d)`, and earlier-bound comparisons.
- **60 `PROVED-FROM-CITED`**: derived internally from the cited axioms in `SmaleRate/Cited/`. Includes Lemma 2.1 (`mu_*`), Proposition 3.4 (`prop_3_4_lower_error`, `prop_3_4_upper`, `prop_3_4_limit` from DLMF 19.9.5 alone), and the Remark 3.5 / Table 2 AGM enclosures (from DLMF 19.8.5 and 19.9.5).
- **5 `CITED`**: direct restatements of the five cited axioms.
- **32 `PROVED-GIVEN`**: proved conditionally given one or both named background hypotheses in `SmaleRate/Defs/BackgroundFacts.lean` (`JordanCurveFact`, `CoefficientUpperFact`), plus cited axioms where listed in `AUDIT.md`. Includes `thm_1_1_given_background` (Theorem 1.1) and `cor_1_2_given_background` (Corollary 1.2).
- **34 `OPEN`**: unproved rows listed in `OPEN_ROWS.txt` and excluded from `comparator/comparator.json`, comprising 22 unconditional counterparts of `PROVED-GIVEN` consequences, 5 foundational unconditional rows (`riemann_map_for_exterior`, `capacity_conformal_coefficient`, `capacity_identity`, `finite_green_exists`, `exterior_green_exists`), and 7 historical/context/companion rows (`betsakos_equality`, `bernstein_walsh`, `dubinin_polynomial_specialization`, `counterexample_explicit_degree`, `earlier_bounds`, `expanded_lower_bound`, `expanded_upper_bound`).
- **3 `NOT-FORMALIZED` registry entries**: general irregular-domain Green theory (`NgreenGeneral`), Dubinin's general spherical meromorphic inequality (`NdubininGeneral`), and general potential-theoretic capacity (`NcapacityPotential`; transfinite diameter is used directly and Fekete-Szego is absorbed into `CoefficientUpperFact`).

## Expanded edition scope

Sections 1 through 3 are shared identically by the focused and expanded `v1.00` editions. Sections 4 and 5 of the expanded edition (Theorems 1.3 and 1.4, Corollary 1.5, and their proofs) are **not formalized in Lean**; the placeholder rows `expanded_lower_bound` and `expanded_upper_bound` remain `OPEN`.

## Cited axioms and named background hypotheses

1. **Refereed cited axioms (`SmaleRate/Cited/Approved.lean`):**
   - `SmaleRate.Cited.dlmf_19_9_5` — NIST DLMF 19.9.5 (Lehto-Virtanen 1973, p. 62).
   - `SmaleRate.Cited.dlmf_19_8_5` — NIST DLMF 19.8.5 (elliptic integral / AGM identity).
   - `SmaleRate.Cited.betsakos_2013` — D. Betsakos, *J. Aust. Math. Soc.* 94 (2013), Theorem 1.1, p. 146 (inequality only).
2. **Unrefereed cited axioms (`SmaleRate/Cited/JatarNg.lean`, auxiliary retired rows only):**
   - `SmaleRate.Cited.jatar_ng_2026_theorem1_v` and `SmaleRate.Cited.jatar_ng_2026_sec1_2_leading_lt_one` (Jatar-Ng, arXiv:2608.27047v1, Section 1.2). Used **only** by auxiliary declarations marked `RETIRED` in `CLAIM_MAP.tsv` (not printed in `v1.00`); absent from Theorem 1.1, Corollary 1.2, Proposition 3.4, and every currently printed claim of either edition.
3. **Named background hypotheses (`SmaleRate/Defs/BackgroundFacts.lean`, ordinary `Prop` binders, never axioms):**
   - `SmaleRate.Background.JordanCurveFact` — a bounded planar Jordan domain has simply connected interior and connected closure complement (Jordan-Schoenflies topology).
   - `SmaleRate.Background.CoefficientUpperFact` — for a nontrivial compact connected continuum with connected complement and exterior conformal map `phi(z) = a z + O(1)`, `capacityTD Q <= |a|` (Ransford 1995, Section 5.2 / Corollary 5.2.2 and Section 5.5 / Fekete-Szego 5.5.2).

## Route differences

- **Table 3 (Corollary 1.2, Step 2, degrees 8 through 20):** proved completely inside Lean via rational Taylor/log/pi bounds (no external computer-check hypothesis).
- **Degree-7 and degree-8 enclosures (Remark 3.5):** proved inside Lean via finite dyadic interval covers (`SmaleRate/Proofs/Generated/`) and DLMF 19.8.5 / 19.9.5.
- **Small degrees (`d <= 4`), `K(d) <= 4`, `K(d) < 4`, `K(d) -> 4`, and monotonicity:** proved unconditionally from Lean's three standard axioms (reusing the `Smale/` closure from the companion `K(d) -> 4` formalization and direct polynomial bounds for `d <= 4`).
- **Proposition 3.4 lower error:** both an elementary choice `L = 1/(log d)^2` and the paper's `L = pi^2 / (2 (log d)^2)` (`prop_selected_L`) are proved from DLMF 19.9.5.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
