/-
SmaleRate — elementary geometry coverage and quadratic inverse example.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.InverseGeometry

set_option backward.proofsInPublic true

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology Polynomial

theorem conformal_geometry_witness_proved : IsBoundedJordanDomain (disk 1) ∧
    IsConformalOnto (fun point : ℂ => point) (disk 1) (disk 1) := by
  refine ⟨⟨isOpen_ball, (convex_ball (0 : ℂ) 1).isPreconnected,
    ⟨0, by simp [disk]⟩, isBounded_ball, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · refine ⟨(fun point : ℂ => point), continuousOn_id, fun _ _ _ _ h => h, ?_⟩
    simpa only [disk, image_id'] using (frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)).symm
  · fun_prop
  · exact fun _ _ _ _ h => h
  · exact image_id _

theorem quadratic_inverse_example_proved :
    IsInverseBranch ((2 : ℂ[X]) * X - X^2) (fun point : ℂ => 1 - Complex.sqrt (1 - point)) ∧
    (1 : ℂ) ∉ (fun point : ℂ => 1 - Complex.sqrt (1 - point)) '' disk 1 ∧
    (1 : ℂ) ∈ frontier ((fun point : ℂ => 1 - Complex.sqrt (1 - point)) '' disk 1) := by
  let inverse : ℂ → ℂ := fun point => 1 - Complex.sqrt (1 - point)
  have hright : ∀ point : ℂ, (((2 : ℂ[X]) * X - X^2).eval (inverse point)) = point := by
    intro point
    have hsquare : (Complex.sqrt (1 - point))^2 = 1 - point := by
      simpa [Complex.sqrt] using Complex.cpow_nat_inv_pow (1 - point) (n := 2) (by decide)
    dsimp only [inverse]
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X, eval_pow]
    linear_combination -hsquare
  have hbranch : IsInverseBranch ((2 : ℂ[X]) * X - X^2) inverse := by
    refine ⟨?_, ?_, fun point _ => hright point⟩
    · intro point hpoint
      have hnorm : ‖point‖ < 1 := mem_ball_zero_iff.mp hpoint
      have hreal : 0 < (1 - point).re := by
        rw [Complex.sub_re, Complex.one_re]
        linarith [Complex.re_le_norm point]
      have hslit : 1 - point ∈ Complex.slitPlane := Or.inl hreal
      have hconst : DifferentiableAt ℂ (fun _ : ℂ => (1 : ℂ)) point := by fun_prop
      exact (hconst.sub ((Complex.differentiableAt_sqrt hslit).comp point
        (hconst.sub differentiableAt_id))).differentiableWithinAt
    · simp [inverse]
  have homit : (1 : ℂ) ∉ inverse '' disk 1 := by
    rintro ⟨point, hpoint, heq⟩
    have hvalue := hright point
    rw [heq] at hvalue
    norm_num at hvalue
    exact (ne_of_lt (mem_ball_zero_iff.mp hpoint)) (by simpa [hvalue] using norm_one (α := ℂ))
  have hcont : ContinuousAt inverse (1 : ℂ) := by
    have hsqrt : ContinuousAt Complex.sqrt (1 - (1 : ℂ)) :=
      Complex.continuousAt_sqrt (Or.inl (by norm_num))
    have hinner : ContinuousAt (fun point : ℂ => 1 - point) 1 := by fun_prop
    have hcompose := hsqrt.comp hinner
    exact continuousAt_const.sub hcompose
  have hclosure : (1 : ℂ) ∈ closure (inverse '' disk 1) := by
    have hmem : (1 : ℂ) ∈ closure (disk 1) := by
      rw [disk, closure_ball 0 (by norm_num : (1 : ℝ) ≠ 0)]
      simp
    simpa [inverse] using mem_closure_image hcont hmem
  refine ⟨hbranch, homit, hclosure, ?_⟩
  exact fun hinterior => homit (interior_subset hinterior)

end SmaleRate.Proofs


