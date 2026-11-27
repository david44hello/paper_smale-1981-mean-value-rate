/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.MuLimits

noncomputable section
namespace SmaleRate.Proofs
open Set Filter
open scoped Topology

section DLMF
variable (hdlmf : ∀ modulus ∈ Ioo 0 1,
  Real.log ((1 + Real.sqrt (complement modulus))^2 / modulus) < mu modulus ∧
    mu modulus < Real.log (2 * (1 + complement modulus) / modulus))
include hdlmf

theorem mu_small_error_pointwise (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 (1/2 : ℝ)) :
    |mu modulus - Real.log (4 / modulus)| ≤ 2 * modulus^2 := by
  have hmem : modulus ∈ Ioo 0 1 := ⟨hmodulus.1, by linarith [hmodulus.2]⟩
  have hmodpos : 0 < modulus := hmodulus.1
  have hcomp := complement_mem modulus hmem
  have harg : 0 ≤ 1 - modulus^2 := by nlinarith [hmem.1, hmem.2]
  have hcompsq : (complement modulus)^2 = 1 - modulus^2 := Real.sq_sqrt harg
  have hrootsq : (Real.sqrt (complement modulus))^2 = complement modulus := Real.sq_sqrt hcomp.1.le
  have hroot : 0 ≤ Real.sqrt (complement modulus) := Real.sqrt_nonneg _
  have hroot_lower : 1 - modulus^2 ≤ Real.sqrt (complement modulus) := by
    have hfirst : 1 - modulus^2 ≤ complement modulus := by nlinarith [hcomp.1, hcomp.2]
    have hsecond : complement modulus ≤ Real.sqrt (complement modulus) := by
      by_contra hnot
      have hlt : Real.sqrt (complement modulus) < complement modulus := lt_of_not_ge hnot
      nlinarith [mul_pos (sub_pos.mpr hlt) (add_pos_of_pos_of_nonneg hcomp.1 hroot)]
    exact hfirst.trans hsecond
  have hsmall : modulus^2 / 2 ∈ Icc (0 : ℝ) (1/2) := by
    constructor
    · positivity
    · nlinarith [hmodulus.1, hmodulus.2]
  have hlog := log_one_sub_half (modulus^2/2) hsmall
  have hbasepos : 0 < 1 - modulus^2/2 := by nlinarith [hmodulus.1, hmodulus.2]
  have hcompare : (4 / modulus) * (1-modulus^2/2)^2 ≤
      (1 + Real.sqrt (complement modulus))^2 / modulus := by
    apply (le_div_iff₀ hmodulus.1).2
    have hid : ((4 / modulus) * (1-modulus^2/2)^2) * modulus = (2-modulus^2)^2 := by
      field_simp [ne_of_gt hmodpos]
      ring
    rw [hid]
    nlinarith [hroot_lower, hroot]
  have hlogcompare := Real.log_le_log (mul_pos (div_pos (by norm_num : (0 : ℝ) < 4) hmodulus.1)
    (sq_pos_of_pos hbasepos)) hcompare
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlogcompare
  have hlower := (hdlmf modulus hmem).1
  have hupper := mu_log_upper_of_upper_dlmf modulus hmem (hdlmf modulus hmem).2
  rw [abs_of_nonpos (sub_nonpos.mpr hupper.le)]
  linarith

theorem mu_small_error_from_dlmf : ∃ constant ≥ (0 : ℝ), ∀ᶠ modulus in 𝓝[>] (0 : ℝ),
    |mu modulus - Real.log (4 / modulus)| ≤ constant * modulus^2 := by
  refine ⟨2, by norm_num, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1/2)] with modulus hmodulus
  exact mu_small_error_pointwise hdlmf modulus hmodulus

end DLMF
end SmaleRate.Proofs
