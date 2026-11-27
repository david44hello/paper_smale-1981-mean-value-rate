/-
SmaleRate — named background hypotheses.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Defs.Basic

noncomputable section
namespace SmaleRate.Background
open Set Filter
open scoped Topology

/-- NAMED HYPOTHESIS, NOT AN AXIOM. Jordan–Schoenflies topology.
For a bounded domain with a continuous injective circle frontier, the interior is simply
connected and the exterior of its closure is connected. Both clauses are needed: the second
supports the constructed exterior E_y; the first feeds the separately proved analytic RMT.
Every conditional result must bind this proposition explicitly and report PROVED GIVEN it.
The paper's E_y construction is not part of this universal background fact. -/
def JordanCurveFact : Prop :=
  ∀ domain : Set ℂ, IsBoundedJordanDomain domain →
    IsSimplyConnected domain ∧ IsConnected (closure domain)ᶜ

/-- NAMED HYPOTHESIS, NOT AN AXIOM. Upper half of the continuum leading-coefficient formula,
in transfinite-diameter notation: Ransford5.2.3 / Corollary5.2.2 AND Fekete–Szegő5.5.2.
This remains an explicit hypothesis throughout.
The application to E_y, its concrete coefficient and the scalar bound remain proofs. -/
def CoefficientUpperFact : Prop :=
  ∀ (compactSet : Set ℂ), IsCompact compactSet → IsConnected compactSet →
    (∃ first ∈ compactSet, ∃ second ∈ compactSet, first ≠ second) →
    IsConnected compactSetᶜ →
    ∀ (phi : ℂ → ℂ),
      IsConformalOnto phi {point : ℂ | 1 < ‖point‖} compactSetᶜ →
    ∀ (coefficient : ℂ), coefficient ≠ 0 →
      (∃ constant : ℂ, Tendsto (fun point : ℂ => phi point - coefficient * point)
        (cocompact ℂ) (𝓝 constant)) →
      capacityTD compactSet ≤ ‖coefficient‖

end SmaleRate.Background
