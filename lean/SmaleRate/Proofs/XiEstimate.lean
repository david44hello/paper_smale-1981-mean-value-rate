/-
SmaleRate — xi estimate from the checked polynomial extension.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.BoundaryMaximum

set_option backward.proofsInPublic true

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology Polynomial

theorem xi_bound_of_extension (degree : ℕ) (hdegree : 0 < degree) (poly : ℂ[X])
    (critical : ℂ) (hnormal : ‖poly.eval critical‖ = 1)
    (func : ℂ → ℂ) (hzero : func 0 = 0) (extension : ℂ → ℂ)
    (hformula : ∀ point ∈ disk 1, point ≠ 0 →
      extension point = point^degree * poly.eval (inversion critical (func point)))
    (height : ℝ) (hheight : 0 ≤ height)
    (hbound : ∀ point ∈ disk 1, ‖extension point‖ ≤ height)
    (xi : ℂ) (hxi : xi ∈ disk 1) (hminusone : func xi = -1) :
    xi ≠ 0 ∧ ‖xi‖ ≤ height ^ (1 / (degree : ℝ)) := by
  have hxi_ne : xi ≠ 0 := by
    intro heq
    subst xi
    rw [hzero] at hminusone
    norm_num at hminusone
  refine ⟨hxi_ne, ?_⟩
  have hpower : ‖xi‖ ^ degree ≤ height := by
    have hnorm := hbound xi hxi
    rw [hformula xi hxi hxi_ne, hminusone, inversion, div_neg, div_one, neg_neg,
      norm_mul, norm_pow, hnormal, mul_one] at hnorm
    exact hnorm
  rw [one_div]
  apply (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) hheight
    (by exact_mod_cast hdegree : (0 : ℝ) < degree)).mpr
  simpa only [Real.rpow_natCast] using hpower

end SmaleRate.Proofs


