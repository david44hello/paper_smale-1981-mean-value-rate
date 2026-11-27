/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.MuApproximation

noncomputable section
namespace SmaleRate.Proofs
open Set Filter
open scoped Topology

section DLMF
variable (hdlmf : ∀ modulus ∈ Ioo 0 1,
  Real.log ((1 + Real.sqrt (complement modulus))^2 / modulus) < mu modulus ∧
    mu modulus < Real.log (2 * (1 + complement modulus) / modulus))
include hdlmf

theorem mu_over_log_tendsto_one :
    Tendsto (fun modulus : ℝ => mu modulus / Real.log (4 / modulus)) (𝓝[>] 0) (𝓝 1) := by
  have hpoly : Tendsto (fun modulus : ℝ => 2 * modulus^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using (show ContinuousAt (fun modulus : ℝ => 2 * modulus^2) 0 by fun_prop).tendsto.mono_left
      nhdsWithin_le_nhds
  have herror : Tendsto (fun modulus : ℝ => mu modulus - Real.log (4 / modulus)) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' _ hpoly
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1/2)] with modulus hmodulus
    simpa only [Real.norm_eq_abs] using mu_small_error_pointwise hdlmf modulus hmodulus
  have hlogbase : Tendsto (fun modulus : ℝ => Real.log (1 / modulus)) (𝓝[>] 0) atTop := by
    simpa only [Function.comp_def, one_div] using Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have hlog : Tendsto (fun modulus : ℝ => Real.log (4 / modulus)) (𝓝[>] 0) atTop := by
    apply tendsto_atTop_mono' (𝓝[>] (0 : ℝ)) _ hlogbase
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with modulus hmodulus
    exact Real.log_le_log (one_div_pos.mpr hmodulus.1)
      (div_le_div_of_nonneg_right (by norm_num) hmodulus.1.le)
  have hquotient := herror.div_atTop hlog
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := tendsto_const_nhds
  have hsum : Tendsto (fun modulus : ℝ => 1 +
      (mu modulus - Real.log (4 / modulus)) / Real.log (4 / modulus)) (𝓝[>] 0) (𝓝 1) := by
    convert hone.add hquotient using 1 <;> norm_num
  apply hsum.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1/2)] with modulus hmodulus
  have hmodpos := hmodulus.1
  have hlogpos : 0 < Real.log (4 / modulus) :=
    Real.log_pos ((lt_div_iff₀ hmodpos).mpr (by linarith [hmodulus.2]))
  field_simp [ne_of_gt hlogpos]
  ring

theorem mu_near_one_from_dlmf : Tendsto (fun modulus : ℝ => mu modulus /
    (Real.pi^2/(2*Real.log (16/(1-modulus^2))))) (𝓝[<] 1) (𝓝 1) := by
  have hcomp_limit : Tendsto complement (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hcontinuous : Continuous complement := by unfold complement; fun_prop
    simpa [complement] using
      (hcontinuous.continuousAt : ContinuousAt complement (1 : ℝ)).tendsto.mono_left nhdsWithin_le_nhds
  have hcomp_within : Tendsto complement (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hcomp_limit, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with modulus hmodulus
    exact (complement_mem modulus hmodulus).1
  have hratio := (mu_over_log_tendsto_one hdlmf).comp hcomp_within
  have hinv : Tendsto (fun modulus : ℝ => Real.log (4 / complement modulus) / mu (complement modulus))
      (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    simpa only [Function.comp_def, inv_div, inv_one] using hratio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  apply hinv.congr'
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with modulus hmodulus
  have hcomp := complement_mem modulus hmodulus
  have hpositive := mu_positive_of_lower_dlmf modulus hmodulus (hdlmf modulus hmodulus).1
  have hcomppos := mu_positive_of_lower_dlmf (complement modulus) hcomp (hdlmf _ hcomp).1
  have hproduct := mu_complement_of_positive modulus hmodulus hpositive hcomppos
  have harg : 0 ≤ 1 - modulus^2 := by nlinarith [hmodulus.1, hmodulus.2]
  have hlog : Real.log (16 / (1-modulus^2)) = 2 * Real.log (4 / complement modulus) := by
    calc
      Real.log (16 / (1-modulus^2)) = Real.log ((4 / complement modulus)^2) := by
        congr 1
        rw [div_pow, show (4 : ℝ)^2 = 16 by norm_num]
        rw [show (complement modulus)^2 = 1 - modulus^2 from Real.sq_sqrt harg]
      _ = 2 * Real.log (4 / complement modulus) := by rw [Real.log_pow]; norm_num
  have hlogpos : 0 < Real.log (4 / complement modulus) :=
    Real.log_pos ((lt_div_iff₀ hcomp.1).mpr (by linarith [hcomp.2]))
  rw [hlog]
  field_simp [ne_of_gt hcomppos, Real.pi_ne_zero, ne_of_gt hlogpos]
  nlinarith [hproduct]

end DLMF
end SmaleRate.Proofs
