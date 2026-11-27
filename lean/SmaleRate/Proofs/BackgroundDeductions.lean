/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Defs.BackgroundFacts
import SmaleRate.Proofs.RiemannBridge

noncomputable section
namespace SmaleRate.Proofs
open Set

theorem riemann_map_given_jordan (hjordan : Background.JordanCurveFact)
    (domain : Set ℂ) (hdomain : IsBoundedJordanDomain domain) (hzero : (0 : ℂ) ∈ domain) :
    ∃ func : ℂ → ℂ, IsConformalOnto func (disk 1) domain ∧ func 0 = 0 := by
  have hproper : domain ≠ univ := by
    intro heq
    have hbounded := hdomain.2.2.2.1
    rw [heq] at hbounded
    exact NormedSpace.unbounded_univ ℂ ℂ hbounded
  exact riemann_map_disk_to_domain domain hdomain.1 (hjordan domain hdomain).1 hproper 0 hzero

end SmaleRate.Proofs
