/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.MuApproximation

noncomputable section
namespace SmaleRate.Proofs
open Set Filter
open scoped Topology

theorem mu_exponential_limit_from_dlmf
    (hdlmf : ∀ modulus ∈ Ioo 0 1,
      Real.log ((1 + Real.sqrt (complement modulus))^2 / modulus) < mu modulus ∧
        mu modulus < Real.log (2 * (1 + complement modulus) / modulus)) :
    Tendsto (fun modulus : ℝ => 4 * Real.exp (-mu modulus) / modulus) (𝓝[>] 0) (𝓝 1) := by
  have hpoly : Tendsto (fun modulus : ℝ => 2 * modulus^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using (show ContinuousAt (fun modulus : ℝ => 2 * modulus^2) 0 by fun_prop).tendsto.mono_left
      nhdsWithin_le_nhds
  have herror : Tendsto (fun modulus : ℝ => mu modulus - Real.log (4 / modulus)) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' _ hpoly
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1/2)] with modulus hmodulus
    simpa only [Real.norm_eq_abs] using mu_small_error_pointwise hdlmf modulus hmodulus
  have hexp : Tendsto (fun modulus : ℝ => Real.exp (-(mu modulus - Real.log (4 / modulus))))
      (𝓝[>] 0) (𝓝 1) := by
    simpa only [Function.comp_def, neg_zero, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp herror.neg
  apply hexp.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1/2)] with modulus hmodulus
  rw [neg_sub, Real.exp_sub, Real.exp_log (div_pos (by norm_num : (0 : ℝ) < 4) hmodulus.1)]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  ring

end SmaleRate.Proofs
