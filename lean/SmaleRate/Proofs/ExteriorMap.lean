/-
SmaleRate — explicit exterior conformal map.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.ExteriorJordan

set_option backward.proofsInPublic true

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology

theorem not_mem_closure_invertedExterior_iff (domain : Set ℂ)
    (hregular : interior (closure domain) = domain) (critical : ℂ) (hcritical : critical ≠ 0)
    (point : ℂ) (hpoint : point ≠ 0) :
    point ∉ closure (invertedExterior domain critical) ↔ inversion critical point ∈ domain := by
  let equiv := inversionPartialHomeomorph critical hcritical
  have himage : equiv.IsImage (closure domain)ᶜ (invertedExterior domain critical) := by
    intro source hsource
    change inversion critical source ∈ invertedExterior domain critical ↔ source ∉ closure domain
    rw [mem_invertedExterior_iff domain critical hcritical _
      (inversion_ne_zero critical hcritical source hsource), inversion_involutive critical hcritical]
  have heq := himage.closure.symm_apply_mem_iff (show point ∈ equiv.target from hpoint)
  change inversion critical point ∈ closure ((closure domain)ᶜ) ↔
    point ∈ closure (invertedExterior domain critical) at heq
  simpa only [closure_compl, hregular, mem_compl_iff, not_not] using (not_congr heq).symm

theorem exterior_conformal_map_proved (inverse : ℂ → ℂ)
    (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (hcritical : critical ≠ 0) :
    IsConformalOnto (fun point : ℂ => inversion critical (inverse ((height : ℂ) / point)))
      {point : ℂ | 1 < ‖point‖} (closure (exteriorImage inverse height critical))ᶜ := by
  have hheight_ne : (height : ℂ) ≠ 0 := by exact_mod_cast hheight.1.ne'
  have hbase : (0 : ℂ) ∈ disk 1 := by simp [disk]
  have hregular := inverseDomain_regular inverse hinverse height hheight
  have harg : ∀ point : ℂ, 1 < ‖point‖ → (height : ℂ) / point ∈ disk height := by
    intro point hpoint
    change (height : ℂ) / point ∈ ball 0 height
    rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hheight.1]
    exact (div_lt_iff₀ (lt_trans zero_lt_one hpoint)).mpr (by nlinarith [hheight.1])
  have harg_disk : ∀ point : ℂ, 1 < ‖point‖ → (height : ℂ) / point ∈ disk 1 :=
    fun point hp => ball_subset_ball hheight.2.le (harg point hp)
  have hinverse_ne : ∀ point : ℂ, 1 < ‖point‖ → inverse ((height : ℂ) / point) ≠ 0 := by
    intro point hp heq
    have hpoint_ne : point ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hp)
    have hsame := hinverse.2 (harg_disk point hp) hbase (heq.trans hzero.symm)
    exact (div_ne_zero hheight_ne hpoint_ne) hsame
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro point hp
    have hpoint_ne : point ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hp)
    have hconst : DifferentiableAt ℂ (fun _ : ℂ => (height : ℂ)) point := by fun_prop
    have harg_diff : DifferentiableAt ℂ (fun other : ℂ => (height : ℂ) / other) point :=
      hconst.div differentiableAt_id hpoint_ne
    have hdiff := (hinverse.1.differentiableAt (isOpen_ball.mem_nhds (harg_disk point hp))).comp
      point harg_diff
    have hcritical_const : DifferentiableAt ℂ (fun _ : ℂ => -critical) point := by fun_prop
    exact (hcritical_const.div hdiff (hinverse_ne point hp)).differentiableWithinAt
  · intro first hfirst second hsecond heq
    have hsame := (inversion_involutive critical hcritical).injective heq
    have harg_same := hinverse.2 (harg_disk first hfirst) (harg_disk second hsecond) hsame
    apply (inversion_involutive (-(height : ℂ)) (neg_ne_zero.mpr hheight_ne)).injective
    simpa only [inversion, neg_neg] using harg_same
  · apply subset_antisymm
    · rintro point ⟨source, hsource, rfl⟩
      have himage : inverse ((height : ℂ) / source) ∈ inverseDomain inverse height :=
        ⟨_, harg source hsource, rfl⟩
      apply (not_mem_closure_invertedExterior_iff _ hregular critical hcritical _
        (inversion_ne_zero critical hcritical _ (hinverse_ne source hsource))).mpr
      rw [inversion_involutive critical hcritical]
      exact himage
    · intro point hpoint
      have hpoint_ne : point ≠ 0 := by
        rintro rfl
        exact hpoint (subset_closure (Or.inl rfl))
      have himage := (not_mem_closure_invertedExterior_iff _ hregular critical hcritical point
        hpoint_ne).mp hpoint
      obtain ⟨source, hsource, heq⟩ := himage
      have hsource_ne : source ≠ 0 := by
        intro hsame
        have hvalue : inversion critical point = 0 := by rw [← heq, hsame, hzero]
        exact inversion_ne_zero critical hcritical point hpoint_ne hvalue
      refine ⟨(height : ℂ) / source, ?_, ?_⟩
      · change 1 < ‖(height : ℂ) / source‖
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hheight.1]
        exact (one_lt_div (norm_pos_iff.mpr hsource_ne)).mpr (mem_ball_zero_iff.mp hsource)
      · have hcancel : (height : ℂ) / ((height : ℂ) / source) = source := by field_simp
        change inversion critical (inverse ((height : ℂ) / ((height : ℂ) / source))) = point
        rw [hcancel, heq, inversion_involutive critical hcritical]

end SmaleRate.Proofs


