/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.AGMBounds
import SmaleRate.Proofs.MuLimits

noncomputable section
namespace SmaleRate.Proofs
open Set Filter
open scoped Topology

section Identity
variable (hidentity : ∀ modulus ∈ Ioo 0 1,
  ellipticK modulus = Real.pi / (2 * agm (complement modulus)))
include hidentity

theorem agm_elliptic_identity_from_dlmf (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) :
    ellipticK modulus = Real.pi / (2 * agm (complement modulus)) ∧
    mu modulus = Real.pi * agm (complement modulus) / (2 * agm modulus) := by
  have hcomp := complement_mem modulus hmodulus
  have hagm : 0 < agm modulus := hmodulus.1.trans_le (agm_initial_bounds modulus hmodulus).1
  have hagmcomp : 0 < agm (complement modulus) := hcomp.1.trans_le (agm_initial_bounds _ hcomp).1
  refine ⟨hidentity modulus hmodulus, ?_⟩
  unfold mu
  rw [hidentity modulus hmodulus, hidentity (complement modulus) hcomp,
    complement_involutive modulus hmodulus]
  field_simp <;> ring

theorem ellipticK_tendsto_zero_right : Tendsto ellipticK (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi / 2)) := by
  have hcomp : Tendsto complement (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hcontinuous : Continuous complement := by unfold complement; fun_prop
    simpa [complement] using
      (hcontinuous.continuousAt : ContinuousAt complement (0 : ℝ)).tendsto.mono_left nhdsWithin_le_nhds
  have hagm : Tendsto (fun modulus : ℝ => agm (complement modulus)) (𝓝[>] 0) (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hcomp tendsto_const_nhds
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with modulus hmodulus
      exact (agm_initial_bounds _ (complement_mem modulus hmodulus)).1
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with modulus hmodulus
      exact (agm_initial_bounds _ (complement_mem modulus hmodulus)).2
  have htwo : Tendsto (fun _ : ℝ => (2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) := tendsto_const_nhds
  have hpi : Tendsto (fun _ : ℝ => Real.pi) (𝓝[>] (0 : ℝ)) (𝓝 Real.pi) := tendsto_const_nhds
  have hratio := hpi.div (htwo.mul hagm) (by norm_num : (2 : ℝ) * 1 ≠ 0)
  have hratio' : Tendsto (fun modulus : ℝ => Real.pi / (2 * agm (complement modulus)))
      (𝓝[>] 0) (𝓝 (Real.pi / 2)) := by
    convert hratio using 1 <;> simp
  apply hratio'.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with modulus hmodulus
  exact (hidentity modulus hmodulus).symm

end Identity

theorem elliptic_endpoints_from_dlmf
    (hidentity : ∀ modulus ∈ Ioo 0 1,
      ellipticK modulus = Real.pi / (2 * agm (complement modulus)))
    (hlower : ∀ modulus ∈ Ioo 0 1,
      Real.log ((1 + Real.sqrt (complement modulus))^2 / modulus) < mu modulus) :
    Tendsto ellipticK (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi / 2)) ∧
    Tendsto ellipticK (𝓝[<] (1 : ℝ)) atTop := by
  have hzero := ellipticK_tendsto_zero_right hidentity
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
  have hdivergent := (mu_tendsto_zero_right hlower).comp hcomp_within
  have hden : Tendsto (fun modulus : ℝ => 2 / Real.pi * ellipticK (complement modulus))
      (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hconst : Tendsto (fun _ : ℝ => 2 / Real.pi) (𝓝[<] (1 : ℝ)) (𝓝 (2 / Real.pi)) := tendsto_const_nhds
    convert hconst.mul (hzero.comp hcomp_within) using 1 <;>
      simp [Function.comp_def] <;> field_simp [Real.pi_ne_zero]
  have hproduct := Filter.Tendsto.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) hdivergent hden
  apply hproduct.congr'
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with modulus hmodulus
  have hcomp := complement_mem modulus hmodulus
  have hagmcomp : 0 < agm (complement modulus) := hcomp.1.trans_le (agm_initial_bounds _ hcomp).1
  have hden_ne : ellipticK (complement modulus) ≠ 0 := by
    rw [hidentity (complement modulus) hcomp]
    have hagm : 0 < agm (complement (complement modulus)) :=
      (complement_mem _ hcomp).1.trans_le (agm_initial_bounds _ (complement_mem _ hcomp)).1
    exact div_ne_zero Real.pi_ne_zero (by positivity)
  simp only [Function.comp_def]
  unfold mu
  rw [complement_involutive modulus hmodulus]
  field_simp [hden_ne, Real.pi_ne_zero] <;> ring

end SmaleRate.Proofs
