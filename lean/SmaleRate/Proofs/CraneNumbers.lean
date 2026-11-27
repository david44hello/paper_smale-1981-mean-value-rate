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

theorem target_lt_from_log_upper (degree : ℕ) (cap bound : ℝ)
    (hellpos : 0 < ell degree) (hell : ell degree < cap)
    (hbound : bound < 4) (hcap : cap*(4-bound) ≤ 4) : target degree < bound := by
  have hproduct : ell degree*(4-bound) < 4 := by
    exact (mul_lt_mul_of_pos_right hell (by linarith)).trans_le hcap
  have hdivide : 4-bound < 4/ell degree := (lt_div_iff₀ hellpos).2 (by nlinarith)
  unfold target
  linarith

theorem small_crane_target (degree : ℕ) (hlower : 8 ≤ degree) (hupper : degree ≤ 16) :
    target degree < (13/5 : ℝ) := by
  have hdpos : 0 < (degree : ℝ) := by exact_mod_cast (by omega : 0 < degree)
  have hdhi : (degree : ℝ) ≤ 16 := by exact_mod_cast hupper
  have hlog16 : Real.log (16 : ℝ) = 4*Real.log 2 := by
    rw [show (16 : ℝ) = (2 : ℝ)^4 by norm_num, Real.log_pow]; norm_num
  have hcap : ell degree < (20/7 : ℝ) := by
    have h := Real.log_le_log hdpos hdhi
    rw [hlog16] at h
    unfold ell
    linarith [Real.log_two_lt_d9]
  exact target_lt_from_log_upper degree (20/7) (13/5)
    (by linarith [ell_gt_one degree hlower]) hcap (by norm_num) (by norm_num)

theorem large_crane_target_bounds : target 25 < (14/5 : ℝ) ∧
    target 100 < (16/5 : ℝ) ∧ (356/100 : ℝ) < target 10000 ∧
    target 10000 < (1783/500 : ℝ) := by
  have h25 : ell 25 = 2*Real.log 5 := by
    unfold ell
    norm_num only [Nat.cast_ofNat]
    rw [show (25 : ℝ) = (5 : ℝ)^2 by norm_num, Real.log_pow]; norm_num
  have h100 : ell 100 = 2*(Real.log 2+Real.log 5) := by
    unfold ell
    norm_num only [Nat.cast_ofNat]
    rw [show (100 : ℝ) = ((2 : ℝ)*5)^2 by norm_num, Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h10000 : ell 10000 = 4*(Real.log 2+Real.log 5) := by
    unfold ell
    norm_num only [Nat.cast_ofNat]
    rw [show (10000 : ℝ) = ((2 : ℝ)*5)^4 by norm_num, Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num)]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply target_lt_from_log_upper 25 (10/3) (14/5)
    · linarith [ell_gt_one 25 (by norm_num)]
    · rw [h25]; linarith [Real.log_five_lt_d9]
    · norm_num
    · norm_num
  · apply target_lt_from_log_upper 100 5 (16/5)
    · linarith [ell_gt_one 100 (by norm_num)]
    · rw [h100]; linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
    · norm_num
    · norm_num
  · apply target_gt_of_log_lower 10000 (91/10) (356/100)
    · linarith [ell_gt_one 10000 (by norm_num)]
    · rw [h10000]; linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
    · norm_num
    · norm_num
  · apply target_lt_from_log_upper 10000 (9211/1000) (1783/500)
    · linarith [ell_gt_one 10000 (by norm_num)]
    · rw [h10000]; linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
    · norm_num
    · norm_num

theorem crane_numeric_margins : ∀ entry ∈
    ([(8,3124),(9,3150),(10,3169),(11,3188),(12,3208),(16,3271),(25,3365),(100,3621),(10000,3955)] : List (ℕ × ℕ)),
    (389/1000 : ℝ) < (entry.2 : ℝ)/1000-target entry.1 ∧
      (entry.1 ≠ 10000 → (2/5 : ℝ) < (entry.2 : ℝ)/1000-target entry.1) := by
  have h8 := small_crane_target 8 (by norm_num) (by norm_num)
  have h9 := small_crane_target 9 (by norm_num) (by norm_num)
  have h10 := small_crane_target 10 (by norm_num) (by norm_num)
  have h11 := small_crane_target 11 (by norm_num) (by norm_num)
  have h12 := small_crane_target 12 (by norm_num) (by norm_num)
  have h16 := small_crane_target 16 (by norm_num) (by norm_num)
  have h25 := large_crane_target_bounds.1
  have h100 := large_crane_target_bounds.2.1
  have h10000 := large_crane_target_bounds.2.2.2
  intro entry hentry
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hentry
  rcases hentry with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    norm_num only [Prod.fst, Prod.snd, Nat.cast_ofNat]
    constructor
    · linarith
    · intro hne
      norm_num at hne <;> linarith

theorem crane_unique_minimum_proved : ∀ entry ∈
    ([(8,3124),(9,3150),(10,3169),(11,3188),(12,3208),(16,3271),(25,3365),(100,3621),(10000,3955)] : List (ℕ × ℕ)),
    (3955/1000 : ℝ)-target 10000 ≤ (entry.2 : ℝ)/1000-target entry.1 ∧
      (entry.1 ≠ 10000 → (3955/1000 : ℝ)-target 10000 < (entry.2 : ℝ)/1000-target entry.1) := by
  intro entry hentry
  have hlast : (3955/1000 : ℝ)-target 10000 < 2/5 := by
    linarith [large_crane_target_bounds.2.2.1]
  by_cases hne : entry.1 ≠ 10000
  · have hother := (crane_numeric_margins entry hentry).2 hne
    exact ⟨by linarith, fun _ => by linarith⟩
  · have heq : entry = (10000,3955) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hentry
      rcases hentry with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    subst entry
    norm_num

theorem crane_numeric_of_corollary
    (hcorollary : ∀ degree : ℕ, 8 ≤ degree → Kd degree < (target degree : EReal)) :
    ∀ entry ∈ ([(8,3124),(9,3150),(10,3169),(11,3188),(12,3208),(16,3271),(25,3365),(100,3621),(10000,3955)] : List (ℕ × ℕ)),
    Kd entry.1 < (((entry.2 : ℝ)/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < (entry.2 : ℝ)/1000-target entry.1 := by
  intro entry hentry
  have hdegree : 8 ≤ entry.1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hentry
    rcases hentry with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hmargin := (crane_numeric_margins entry hentry).1
  have hscalar : target entry.1 < (entry.2 : ℝ)/1000 := by linarith
  exact ⟨(hcorollary entry.1 hdegree).trans (by exact_mod_cast hscalar), hmargin⟩

end SmaleRate.Proofs

#check SmaleRate.Proofs.crane_numeric_margins
#print axioms SmaleRate.Proofs.crane_numeric_margins
#check SmaleRate.Proofs.crane_unique_minimum_proved
#print axioms SmaleRate.Proofs.crane_unique_minimum_proved
#check SmaleRate.Proofs.crane_numeric_of_corollary
#print axioms SmaleRate.Proofs.crane_numeric_of_corollary
