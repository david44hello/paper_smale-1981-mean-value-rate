/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.Elementary

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter
open scoped Topology

theorem lambda_small_multiple_identity (multiple : ℝ) (hmultiple : 0 < multiple)
    (degree : ℕ) (hdegree : 2 ≤ degree) (hell : 0 < ell degree)
    (hratio : (multiple/ell degree)/(degree : ℝ) < 1) :
    lambda degree (multiple/ell degree) = ell degree + Real.log (8/multiple) +
      Real.log (ell degree) - Real.log (1-(multiple/ell degree)/(degree : ℝ)) := by
  have hdpos : 0 < (degree : ℝ) := by exact_mod_cast (show 0 < degree by omega)
  have hlast : 0 < 1-(multiple/ell degree)/(degree : ℝ) := by linarith
  have hid : 8*(degree : ℝ)/((multiple/ell degree)*(1-(multiple/ell degree)/(degree : ℝ))) =
      ((degree : ℝ)*(8/multiple)*ell degree)/(1-(multiple/ell degree)/(degree : ℝ)) := by
    field_simp
    <;> ring
  unfold lambda
  rw [hid, Real.log_div (by positivity) (ne_of_gt hlast),
    Real.log_mul (by positivity) (ne_of_gt hell),
    Real.log_mul (ne_of_gt hdpos) (by positivity)]
  rfl

theorem lambda_small_multiple_ratio_tendsto (multiple : ℝ) (hmultiple : 0 < multiple) :
    Tendsto (fun degree : ℕ => lambda degree (multiple/ell degree)/ell degree) atTop (𝓝 1) := by
  have helltop : Tendsto ell atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlength : Tendsto (fun degree : ℕ => multiple/ell degree) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop helltop
  have hratio : Tendsto (fun degree : ℕ => (multiple/ell degree)/(degree : ℝ)) atTop (𝓝 0) :=
    hlength.div_atTop tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun degree : ℕ => Real.log (1-(multiple/ell degree)/(degree : ℝ)))
      atTop (𝓝 0) := by
    have hsub : Tendsto (fun degree : ℕ => 1-(multiple/ell degree)/(degree : ℝ))
        atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hratio
    simpa only [Function.comp_def, Real.log_one] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      hsub
  have hlogratio : Tendsto (fun degree : ℕ => Real.log (ell degree)/ell degree) atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp helltop
  have hconstant : Tendsto (fun degree : ℕ => Real.log (8/multiple)/ell degree) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop helltop
  have hcorrection := hlog.div_atTop helltop
  have hresult : Tendsto (fun degree : ℕ =>
      1+Real.log (8/multiple)/ell degree+Real.log (ell degree)/ell degree-
        Real.log (1-(multiple/ell degree)/(degree : ℝ))/ell degree) atTop (𝓝 1) := by
    convert ((tendsto_const_nhds.add hconstant).add hlogratio).sub hcorrection using 1 <;> norm_num
  apply hresult.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ), helltop.eventually_gt_atTop 0,
    hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with degree hdegree hell hsmall
  rw [lambda_small_multiple_identity multiple hmultiple degree hdegree hell hsmall]
  field_simp [ne_of_gt hell]
  <;> ring

theorem small_multiple_asymptotic_proved (multiple : ℝ)
    (hmultiple : multiple ∈ Ioo 0 (Real.pi^2/2)) :
    Tendsto (fun degree : ℕ =>
      (4-4*Real.exp (multiple/ell degree-Real.pi^2/(2*lambda degree (multiple/ell degree))))*ell degree)
      atTop (𝓝 (2*Real.pi^2-4*multiple)) := by
  have helltop : Tendsto ell atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio := lambda_small_multiple_ratio_tendsto multiple hmultiple.1
  have hinverse : Tendsto (fun degree : ℕ => ell degree/lambda degree (multiple/ell degree))
      atTop (𝓝 1) := by
    have hlimit := ((tendsto_const_nhds (x := (1 : ℝ))).div hratio (by norm_num : (1 : ℝ) ≠ 0))
    change Tendsto (fun degree : ℕ => 1/(lambda degree (multiple/ell degree)/ell degree)) atTop (𝓝 (1/1 : ℝ)) at hlimit
    simpa only [one_div_div, div_one] using hlimit
  let exponent : ℕ → ℝ := fun degree => multiple/ell degree-Real.pi^2/(2*lambda degree (multiple/ell degree))
  have hscaled : Tendsto (fun degree : ℕ => exponent degree*ell degree)
      atTop (𝓝 (multiple-Real.pi^2/2)) := by
    have hlimit : Tendsto (fun degree : ℕ => multiple-(Real.pi^2/2)*
        (ell degree/lambda degree (multiple/ell degree))) atTop (𝓝 (multiple-Real.pi^2/2)) := by
      simpa only [mul_one] using
        (tendsto_const_nhds (x := multiple)).sub (hinverse.const_mul (Real.pi^2/2))
    apply hlimit.congr'
    filter_upwards [helltop.eventually_gt_atTop 0] with degree hell
    dsimp [exponent]
    field_simp [ne_of_gt hell]
    <;> ring
  have hzero : Tendsto exponent atTop (𝓝 0) := by
    apply (hscaled.div_atTop helltop).congr'
    filter_upwards [helltop.eventually_gt_atTop 0] with degree hell
    exact mul_div_cancel_right₀ _ (ne_of_gt hell)
  have hnonzero : ∀ᶠ degree : ℕ in atTop, exponent degree ≠ 0 := by
    have hnegative := hscaled.eventually
      (gt_mem_nhds (by linarith [hmultiple.2] : multiple-Real.pi^2/2 < 0))
    filter_upwards [hnegative] with degree hdegree
    intro heq
    rw [heq, zero_mul] at hdegree
    exact (lt_irrefl 0) hdegree
  have hwithin : Tendsto exponent atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hnonzero⟩
  have hslope : Tendsto (fun degree : ℕ => (Real.exp (exponent degree)-1)/exponent degree)
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, zero_add, Real.exp_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_exp 0).tendsto_slope_zero.comp hwithin
  have hlimit := (hslope.mul hscaled).const_mul (-4)
  have hfinal : Tendsto (fun degree : ℕ => (4-4*Real.exp (exponent degree))*ell degree)
      atTop (𝓝 (-4*(1*(multiple-Real.pi^2/2)))) := by
    apply hlimit.congr'
    filter_upwards [hnonzero] with degree hdegree
    field_simp [hdegree]
    <;> ring
  have hend : -4*(1*(multiple-Real.pi^2/2)) = 2*Real.pi^2-4*multiple := by ring
  rw [hend] at hfinal
  exact hfinal

end SmaleRate.Proofs
