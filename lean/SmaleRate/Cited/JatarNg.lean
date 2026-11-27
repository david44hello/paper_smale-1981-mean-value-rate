/-
SmaleRate — approved external Jatar–Ng polynomial inputs.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Defs.AnalyticBackground

set_option backward.proofsInPublic true

@[expose] public section

namespace SmaleRate.Cited
open Set Polynomial

/-- UNREFEREED: Jatar–Ng, arXiv:2608.27047v1,27 August2026,
Theorem1(v),section1.2; finite-degree inequality only.
https://arxiv.org/html/2608.27047v1 -/
axiom jatar_ng_2026_theorem1_v
    (degree : ℕ) (hdegree : 169 ≤ degree)
    (poly : ℂ[X]) (hpoly : IsSchlichtNormalized degree poly)
    (hlog : (Real.log (1 / ‖poly.leadingCoeff‖)) ^ 2 ≤ (degree : ℝ))
    (point : ℂ) (hpoint : point ∈ criticalPoints poly)
    (hboundary : point ∈ frontier (lemniscateComponent poly 1)) :
    criticalRatio poly point ≤ jatarNgBound degree

/-- UNREFEREED: Jatar–Ng, arXiv:2608.27047v1,27 August2026,
section1.2,unnumbered normalized-polynomial observation before Theorem1.
Only the strict upper half; positivity is proved internally.
https://arxiv.org/html/2608.27047v1 -/
axiom jatar_ng_2026_sec1_2_leading_lt_one
    (degree : ℕ) (hdegree : 2 ≤ degree)
    (poly : ℂ[X]) (hpoly : IsSchlichtNormalized degree poly) :
    ‖poly.leadingCoeff‖ < 1

end SmaleRate.Cited
