/-
SmaleRate — scalar Betsakos endpoint coverage and quadratic witness.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.MuExponentialLimit

set_option backward.proofsInPublic true

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology Polynomial

section DLMF
variable (hdlmf : ∀ modulus ∈ Ioo 0 1,
  Real.log ((1 + Real.sqrt (complement modulus))^2 / modulus) < mu modulus ∧
    mu modulus < Real.log (2 * (1 + complement modulus) / modulus))
include hdlmf

theorem betsakos_small_argument_proved (diameter : ℝ) :
    ∃ constant ≥ (0 : ℝ), ∀ᶠ modulus in 𝓝[>] (0 : ℝ),
      |4 * diameter * Real.exp (-mu modulus) - diameter * modulus| ≤ constant * |modulus|^3 := by
  refine ⟨4 * |diameter|, by positivity, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1/2)] with modulus hmodulus
  have hpositive : 0 < modulus := hmodulus.1
  let error : ℝ := Real.log (4 / modulus) - mu modulus
  have herror : |error| ≤ 2 * modulus^2 := by
    simpa only [error, abs_sub_comm] using mu_small_error_pointwise hdlmf modulus hmodulus
  have herror_one : |error| ≤ 1 := herror.trans (by nlinarith [hmodulus.1, hmodulus.2])
  have hexp : |Real.exp error - 1| ≤ 4 * modulus^2 :=
    (Real.abs_exp_sub_one_le herror_one).trans (by linarith)
  have hidentity : 4 * diameter * Real.exp (-mu modulus) - diameter * modulus =
      diameter * modulus * (Real.exp error - 1) := by
    dsimp [error]
    rw [Real.exp_sub, Real.exp_log (div_pos (by norm_num) hpositive), Real.exp_neg]
    field_simp
  rw [hidentity, abs_mul, abs_mul, abs_of_pos hpositive]
  calc
    |diameter| * modulus * |Real.exp error - 1| ≤ |diameter| * modulus * (4 * modulus^2) :=
      mul_le_mul_of_nonneg_left hexp (mul_nonneg (abs_nonneg _) hpositive.le)
    _ = 4 * |diameter| * modulus^3 := by ring

theorem betsakos_large_argument_proved (diameter : ℝ) :
    Tendsto (fun modulus : ℝ => 4 * diameter * Real.exp (-mu modulus))
      (𝓝[<] 1) (𝓝 (4 * diameter)) := by
  have hmu := (mu_endpoints_from_lower_dlmf (fun modulus hmodulus =>
    (hdlmf modulus hmodulus).1)).2
  have hexp : Tendsto (fun modulus : ℝ => Real.exp (-mu modulus)) (𝓝[<] 1) (𝓝 1) := by
    simpa only [Function.comp_def, neg_zero, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp hmu.neg
  simpa only [mul_one] using (tendsto_const_nhds.mul hexp :
    Tendsto (fun modulus : ℝ => (4 * diameter) * Real.exp (-mu modulus))
      (𝓝[<] 1) (𝓝 ((4 * diameter) * 1)))

theorem zero_betsakos_interpretation_proved (diameter : ℝ) :
    Tendsto (fun modulus : ℝ => 4 * diameter * Real.exp (-mu modulus))
      (𝓝[>] 0) (𝓝 0) := by
  have hmodulus : Tendsto (fun modulus : ℝ => modulus) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hproduct : Tendsto (fun modulus : ℝ => diameter *
      ((4 * Real.exp (-mu modulus) / modulus) * modulus)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [one_mul, mul_zero] using tendsto_const_nhds.mul
      ((mu_exponential_limit_from_dlmf hdlmf).mul hmodulus)
  apply hproduct.congr'
  filter_upwards [self_mem_nhdsWithin] with modulus hpositive
  have hne : modulus ≠ 0 := ne_of_gt hpositive
  field_simp

end DLMF

theorem figure2_example_proved : IsPd 2 ((2 : ℂ[X]) * X - X^2) ∧
    NormalizedCriticalValues ((2 : ℂ[X]) * X - X^2) 1 := by
  have hderivative : ∀ point : ℂ, (((2 : ℂ[X]) * X - X^2).derivative).eval point =
      2 - 2 * point := by
    intro point
    simp <;> ring_nf <;> simp
  have hcritical : ∀ point ∈ criticalPoints ((2 : ℂ[X]) * X - X^2), point = 1 := by
    intro point hpoint
    change (((2 : ℂ[X]) * X - X^2).derivative).eval point = 0 at hpoint
    rw [hderivative] at hpoint
    linear_combination -(1/2 : ℂ) * hpoint
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · compute_degree!
  · simp
  · rw [hderivative]
    norm_num
  · change (((2 : ℂ[X]) * X - X^2).derivative).eval 1 = 0
    rw [hderivative]
    norm_num
  · norm_num
  · intro point hpoint
    rw [hcritical point hpoint]
    norm_num

end SmaleRate.Proofs


