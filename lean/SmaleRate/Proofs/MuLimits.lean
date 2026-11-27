/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.EllipticContinuity

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter
open scoped Topology

theorem mu_tendsto_zero_right
    (hlower : ∀ modulus ∈ Ioo 0 1,
      Real.log ((1 + Real.sqrt (complement modulus))^2 / modulus) < mu modulus) :
    Tendsto mu (𝓝[>] (0 : ℝ)) atTop := by
  have hlog : Tendsto (fun modulus : ℝ => Real.log (1 / modulus)) (𝓝[>] 0) atTop := by
    simpa only [one_div, Function.comp_def] using Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  apply tendsto_atTop_mono' (𝓝[>] (0 : ℝ)) _ hlog
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with modulus hmodulus
  have hcompare : 1 / modulus ≤ (1 + Real.sqrt (complement modulus))^2 / modulus := by
    apply div_le_div_of_nonneg_right _ hmodulus.1.le
    nlinarith [Real.sqrt_nonneg (complement modulus)]
  exact (Real.log_le_log (one_div_pos.mpr hmodulus.1) hcompare).trans (hlower modulus hmodulus).le

theorem mu_endpoints_from_lower_dlmf
    (hlower : ∀ modulus ∈ Ioo 0 1,
      Real.log ((1 + Real.sqrt (complement modulus))^2 / modulus) < mu modulus) :
    Tendsto mu (𝓝[>] (0 : ℝ)) atTop ∧ Tendsto mu (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hzero := mu_tendsto_zero_right hlower
  have hpositive : ∀ modulus ∈ Ioo 0 1, 0 < mu modulus :=
    fun modulus hmodulus => mu_positive_of_lower_dlmf modulus hmodulus (hlower modulus hmodulus)
  refine ⟨hzero, ?_⟩
  have hcomp_limit : Tendsto complement (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hcontinuous : Continuous complement := by unfold complement; fun_prop
    simpa [complement] using
      (hcontinuous.continuousAt : ContinuousAt complement (1 : ℝ)).tendsto.mono_left nhdsWithin_le_nhds
  have hcomp_within : Tendsto complement (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hcomp_limit, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with modulus hmodulus
    exact (complement_mem modulus hmodulus).1
  have hdivergent := hzero.comp hcomp_within
  have hquotient : Tendsto (fun modulus : ℝ => (Real.pi^2 / 4) / mu (complement modulus))
      (𝓝[<] (1 : ℝ)) (𝓝 0) := tendsto_const_nhds.div_atTop hdivergent
  apply hquotient.congr'
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with modulus hmodulus
  have hcomp := complement_mem modulus hmodulus
  have hproduct := mu_complement_of_positive modulus hmodulus
    (hpositive modulus hmodulus) (hpositive (complement modulus) hcomp)
  exact (eq_div_iff (ne_of_gt (hpositive (complement modulus) hcomp))).mpr hproduct |>.symm

theorem mu_range_from_lower_dlmf
    (hlower : ∀ modulus ∈ Ioo 0 1,
      Real.log ((1 + Real.sqrt (complement modulus))^2 / modulus) < mu modulus) :
    mu '' Ioo 0 1 = Ioi 0 := by
  have hpositive : ∀ modulus ∈ Ioo 0 1, 0 < mu modulus :=
    fun modulus hmodulus => mu_positive_of_lower_dlmf modulus hmodulus (hlower modulus hmodulus)
  apply Set.Subset.antisymm
  · rintro value ⟨modulus, hmodulus, rfl⟩
    exact hpositive modulus hmodulus
  · have hleft : 𝓝[<] (1 : ℝ) ≤ 𝓟 (Ioo (0 : ℝ) 1) :=
      le_principal_iff.mpr (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1))
    have hright : 𝓝[>] (0 : ℝ) ≤ 𝓟 (Ioo (0 : ℝ) 1) :=
      le_principal_iff.mpr (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))
    have hcontinuous : ContinuousOn mu (Ioo 0 1) :=
      fun modulus hmodulus => (mu_continuousAt_of_positive hpositive modulus hmodulus).continuousWithinAt
    have hlimits := mu_endpoints_from_lower_dlmf hlower
    exact isPreconnected_Ioo.intermediate_value_Ioi hleft hright hcontinuous hlimits.2 hlimits.1

end SmaleRate.Proofs
