/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Defs.AnalyticBackground

noncomputable section
namespace SmaleRate.Proofs
open Set Filter
open scoped Topology

theorem jatar_ng_bound_limit_proved : Tendsto jatarNgBound atTop (𝓝 1) := by
  have hnat : Tendsto (fun degree : ℕ => (degree : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hsqrttop : Tendsto (fun degree : ℕ => Real.sqrt degree) atTop atTop := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).comp hnat
  have hlogratio : Tendsto (fun degree : ℕ => Real.log degree/Real.sqrt degree) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).tendsto_div_nhds_zero.comp hnat
  have hconstant : Tendsto (fun degree : ℕ => (Real.log 2+1)/Real.sqrt degree) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsqrttop
  have hquotient : Tendsto (fun degree : ℕ =>
      Real.log (2*Real.exp 1*Real.sqrt degree)/Real.sqrt degree) atTop (𝓝 0) := by
    have hlimit : Tendsto (fun degree : ℕ => (Real.log 2+1)/Real.sqrt degree+
        (Real.log degree/Real.sqrt degree)/2) atTop (𝓝 0) := by
      simpa only [zero_div, add_zero] using
        hconstant.add (hlogratio.div_const 2)
    apply hlimit.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with degree hdegree
    have hdpos : 0 < (degree : ℝ) := by exact_mod_cast (show 0 < degree by omega)
    rw [Real.log_mul (by positivity) (ne_of_gt (Real.sqrt_pos.mpr hdpos)),
      Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp,
      Real.log_sqrt hdpos.le]
    ring
  have hroot : Tendsto (fun degree : ℕ =>
      Real.sqrt (Real.log (2*Real.exp 1*Real.sqrt degree)/Real.sqrt degree)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hquotient
  have hformula : Tendsto (fun degree : ℕ => (degree : ℝ)^(-1/4 : ℝ)*
      Real.sqrt (Real.log (2*Real.exp 1*Real.sqrt degree))) atTop (𝓝 0) := by
    apply hroot.congr'
    filter_upwards [] with degree
    have hdnonneg : 0 ≤ (degree : ℝ) := Nat.cast_nonneg degree
    have hrootid : Real.sqrt (Real.sqrt (degree : ℝ)) = (degree : ℝ)^(1/4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hdnonneg]
      norm_num
    rw [Real.sqrt_div' _ (Real.sqrt_nonneg _), hrootid,
      show (-1/4 : ℝ) = -(1/4 : ℝ) by ring, Real.rpow_neg hdnonneg]
    ring
  have hfinal : Tendsto (fun degree : ℕ => 1+3*((degree : ℝ)^(-1/4 : ℝ)*
      Real.sqrt (Real.log (2*Real.exp 1*Real.sqrt degree)))) atTop (𝓝 1) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).add (hformula.const_mul 3)
  convert hfinal using 1
  ext degree
  unfold jatarNgBound
  ring

end SmaleRate.Proofs

#check SmaleRate.Proofs.jatar_ng_bound_limit_proved
#print axioms SmaleRate.Proofs.jatar_ng_bound_limit_proved
