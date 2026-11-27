/-
SmaleRate — derivative consequence of Betsakos's inequality.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.MuExponentialLimit
public import SmaleRate.Proofs.DiameterMonotonicity

set_option backward.proofsInPublic true

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology

theorem transfiniteDiameter_nonneg_of_bounded (domain : Set ℂ)
    (hbounded : Bornology.IsBounded domain) (hnonempty : domain.Nonempty) :
    0 ≤ transfiniteDiameter domain := by
  unfold transfiniteDiameter
  apply le_csInf (s := {value : ℝ | ∃ count ≥ 2, value = nDiameter domain count})
    ⟨nDiameter domain 2, 2, le_rfl, rfl⟩
  rintro value ⟨count, _, rfl⟩
  exact nDiameter_nonneg_of_subset_compact domain (closure domain) hnonempty subset_closure
    hbounded.isCompact_closure count

theorem betsakos_derivative_of_ratio_limit
    (hlimit : Tendsto (fun modulus : ℝ => 4 * Real.exp (-mu modulus) / modulus)
      (𝓝[>] 0) (𝓝 1))
    (hbets : ∀ (func : ℂ → ℂ), DifferentiableOn ℂ func (disk 1) →
      Bornology.IsBounded (func '' disk 1) → func 0 = 0 →
      (∃ first ∈ disk 1, ∃ second ∈ disk 1, func first ≠ func second) →
      ∀ point ∈ disk 1, point ≠ 0 →
        ‖func point‖ ≤ 4 * transfiniteDiameter (func '' disk 1) * Real.exp (-mu ‖point‖))
    (func : ℂ → ℂ) (hhol : DifferentiableOn ℂ func (disk 1))
    (hbounded : Bornology.IsBounded (func '' disk 1)) (hzero : func 0 = 0) :
    ‖deriv func 0‖ ≤ transfiniteDiameter (func '' disk 1) := by
  classical
  have hbase : (0 : ℂ) ∈ disk 1 := by simp [disk]
  have hnonneg := transfiniteDiameter_nonneg_of_bounded _ hbounded
    ⟨func 0, mem_image_of_mem func hbase⟩
  by_cases hnonconstant : ∃ first ∈ disk 1, ∃ second ∈ disk 1, func first ≠ func second
  · have hdiff : DifferentiableAt ℂ func 0 := hhol.differentiableAt (isOpen_ball.mem_nhds hbase)
    have hcont : ContinuousAt (fun point : ℂ => ‖dslope func 0 point‖) 0 :=
      (continuousAt_dslope_same.mpr hdiff).norm
    have hreal : Tendsto (fun modulus : ℝ => (modulus : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
      exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hleft : Tendsto (fun modulus : ℝ => ‖dslope func 0 (modulus : ℂ)‖)
        (𝓝[>] 0) (𝓝 ‖deriv func 0‖) := by
      simpa only [dslope_same, Function.comp_def] using hcont.tendsto.comp hreal
    have hright : Tendsto (fun modulus : ℝ => transfiniteDiameter (func '' disk 1) *
        (4 * Real.exp (-mu modulus) / modulus)) (𝓝[>] 0)
        (𝓝 (transfiniteDiameter (func '' disk 1))) := by
      simpa only [mul_one] using tendsto_const_nhds.mul hlimit
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with modulus hmodulus
    have hmodulus_ne : (modulus : ℂ) ≠ 0 := by exact_mod_cast hmodulus.1.ne'
    have hnorm : ‖(modulus : ℂ)‖ = modulus := by
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmodulus.1]
    have hmem : (modulus : ℂ) ∈ disk 1 := by
      change (modulus : ℂ) ∈ ball 0 1
      rw [mem_ball_zero_iff, hnorm]
      exact hmodulus.2
    have hbound := hbets func hhol hbounded hzero hnonconstant (modulus : ℂ) hmem hmodulus_ne
    rw [hnorm] at hbound
    have hdslope : dslope func 0 (modulus : ℂ) = func (modulus : ℂ) / (modulus : ℂ) := by
      rw [dslope_of_ne _ hmodulus_ne]
      simp [slope, hzero, div_eq_mul_inv, mul_comm]
    rw [hdslope, norm_div, hnorm]
    calc
      ‖func (modulus : ℂ)‖ / modulus ≤
          (4 * transfiniteDiameter (func '' disk 1) * Real.exp (-mu modulus)) / modulus :=
        div_le_div_of_nonneg_right hbound hmodulus.1.le
      _ = _ := by ring
  · push Not at hnonconstant
    have heq : func =ᶠ[𝓝 (0 : ℂ)] (fun _ : ℂ => func 0) := by
      filter_upwards [isOpen_ball.mem_nhds hbase] with point hpoint
      exact hnonconstant point hpoint 0 hbase
    rw [heq.deriv_eq, deriv_const, norm_zero]
    exact hnonneg

theorem betsakos_derivative_from_sources
    (hdlmf : ∀ modulus ∈ Ioo 0 1,
      Real.log ((1 + Real.sqrt (complement modulus))^2 / modulus) < mu modulus ∧
        mu modulus < Real.log (2 * (1 + complement modulus) / modulus))
    (hbets : ∀ (func : ℂ → ℂ), DifferentiableOn ℂ func (disk 1) →
      Bornology.IsBounded (func '' disk 1) → func 0 = 0 →
      (∃ first ∈ disk 1, ∃ second ∈ disk 1, func first ≠ func second) →
      ∀ point ∈ disk 1, point ≠ 0 →
        ‖func point‖ ≤ 4 * transfiniteDiameter (func '' disk 1) * Real.exp (-mu ‖point‖))
    (func : ℂ → ℂ) (hhol : DifferentiableOn ℂ func (disk 1))
    (hbounded : Bornology.IsBounded (func '' disk 1)) (hzero : func 0 = 0) :
    ‖deriv func 0‖ ≤ transfiniteDiameter (func '' disk 1) :=
  betsakos_derivative_of_ratio_limit (mu_exponential_limit_from_dlmf hdlmf)
    hbets func hhol hbounded hzero

end SmaleRate.Proofs


