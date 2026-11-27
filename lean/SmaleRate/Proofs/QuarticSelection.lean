/-
SmaleRate — sharp three-root quartic selection.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Defs.Basic

set_option backward.proofsInPublic true

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs

def quarticNumerator (first second third : ℂ) : ℂ :=
  second * third - 2 * first * (second + third)

theorem quartic_numerator_norm_identity (first second third : ℂ) :
    ‖quarticNumerator first second third‖ ^ 2 +
      ‖quarticNumerator second first third‖ ^ 2 +
      ‖quarticNumerator third first second‖ ^ 2 =
      9 * (‖first‖ ^ 2 * ‖second‖ ^ 2 + ‖first‖ ^ 2 * ‖third‖ ^ 2 +
        ‖second‖ ^ 2 * ‖third‖ ^ 2) := by
  simp only [Complex.sq_norm, quarticNumerator, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im]
  norm_num
  <;> ring

theorem quartic_numerator_selection (first second third : ℂ) :
    ‖quarticNumerator first second third‖ ≤ 3 * ‖first‖ ^ 2 ∨
      ‖quarticNumerator second first third‖ ≤ 3 * ‖second‖ ^ 2 ∨
      ‖quarticNumerator third first second‖ ≤ 3 * ‖third‖ ^ 2 := by
  have hidentity := quartic_numerator_norm_identity first second third
  by_contra hnone
  push Not at hnone
  obtain ⟨hfirst, hsecond, hthird⟩ := hnone
  have hfirst_sq : (3 * ‖first‖ ^ 2) ^ 2 < ‖quarticNumerator first second third‖ ^ 2 :=
    (sq_lt_sq₀ (by positivity) (norm_nonneg _)).mpr hfirst
  have hsecond_sq : (3 * ‖second‖ ^ 2) ^ 2 < ‖quarticNumerator second first third‖ ^ 2 :=
    (sq_lt_sq₀ (by positivity) (norm_nonneg _)).mpr hsecond
  have hthird_sq : (3 * ‖third‖ ^ 2) ^ 2 < ‖quarticNumerator third first second‖ ^ 2 :=
    (sq_lt_sq₀ (by positivity) (norm_nonneg _)).mpr hthird
  nlinarith [sq_nonneg (‖first‖ ^ 2 - ‖second‖ ^ 2),
    sq_nonneg (‖first‖ ^ 2 - ‖third‖ ^ 2), sq_nonneg (‖second‖ ^ 2 - ‖third‖ ^ 2)]

def quarticRootRatio (first second third : ℂ) : ℂ :=
  1 / 2 - first * (1 / second + 1 / third) / 6 + first ^ 2 / (12 * second * third)

theorem quartic_root_ratio_reciprocal (first second third : ℂ)
    (hfirst : first ≠ 0) (hsecond : second ≠ 0) (hthird : third ≠ 0) :
    quarticRootRatio first second third = 1 / 2 +
      quarticNumerator first⁻¹ second⁻¹ third⁻¹ / (12 * (first⁻¹) ^ 2) := by
  unfold quarticRootRatio quarticNumerator
  field_simp [hfirst, hsecond, hthird]
  <;> ring

theorem quartic_root_ratio_bound (first second third : ℂ)
    (hfirst : first ≠ 0) (hsecond : second ≠ 0) (hthird : third ≠ 0)
    (hselected : ‖quarticNumerator first⁻¹ second⁻¹ third⁻¹‖ ≤ 3 * ‖first⁻¹‖ ^ 2) :
    ‖quarticRootRatio first second third - 1 / 2‖ ≤ (1 / 4 : ℝ) := by
  rw [quartic_root_ratio_reciprocal first second third hfirst hsecond hthird,
    add_sub_cancel_left, norm_div, norm_mul, norm_pow]
  rw [show ‖(12 : ℂ)‖ = (12 : ℝ) by norm_num]
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 12)
    (sq_pos_of_pos (norm_pos_iff.mpr (inv_ne_zero hfirst))))).mpr
  nlinarith

/-- Some root satisfies Tischler's shifted disk bound; repeated roots are allowed. -/
theorem quartic_shifted_selection (first second third : ℂ)
    (hfirst : first ≠ 0) (hsecond : second ≠ 0) (hthird : third ≠ 0) :
    ‖quarticRootRatio first second third - 1 / 2‖ ≤ (1 / 4 : ℝ) ∨
      ‖quarticRootRatio second first third - 1 / 2‖ ≤ (1 / 4 : ℝ) ∨
      ‖quarticRootRatio third first second - 1 / 2‖ ≤ (1 / 4 : ℝ) := by
  rcases quartic_numerator_selection first⁻¹ second⁻¹ third⁻¹ with hbound | hbound | hbound
  · exact Or.inl (quartic_root_ratio_bound first second third hfirst hsecond hthird hbound)
  · exact Or.inr (Or.inl (quartic_root_ratio_bound second first third hsecond hfirst hthird hbound))
  · exact Or.inr (Or.inr (quartic_root_ratio_bound third first second hthird hfirst hsecond hbound))

theorem quartic_ratio_bound_of_shifted (value : ℂ)
    (hvalue : ‖value - 1 / 2‖ ≤ (1 / 4 : ℝ)) : ‖value‖ ≤ (3 / 4 : ℝ) := by
  calc
    ‖value‖ = ‖(value - 1 / 2) + 1 / 2‖ := by congr 1; ring
    _ ≤ ‖value - 1 / 2‖ + ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
    _ ≤ 3 / 4 := by norm_num; linarith

end SmaleRate.Proofs

#check SmaleRate.Proofs.quartic_numerator_norm_identity
#check SmaleRate.Proofs.quartic_numerator_selection
#check SmaleRate.Proofs.quartic_shifted_selection
#check SmaleRate.Proofs.quartic_ratio_bound_of_shifted
#print axioms SmaleRate.Proofs.quartic_numerator_norm_identity
#print axioms SmaleRate.Proofs.quartic_numerator_selection
#print axioms SmaleRate.Proofs.quartic_shifted_selection
#print axioms SmaleRate.Proofs.quartic_ratio_bound_of_shifted
