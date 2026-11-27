/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.EarlierComparisons

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter
open scoped Topology

theorem beardon_as_q (degree : ℕ) (hdegree : 2 ≤ degree) :
    beardon degree = 4*(4 : ℝ)^(-1/((degree : ℝ)-1)) := by
  have hd : (2 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hden : (degree : ℝ)-1 ≠ 0 := ne_of_gt (by linarith)
  unfold beardon
  have hid : ((degree : ℝ)-2)/((degree : ℝ)-1) = 1+(-1/((degree : ℝ)-1)) := by
    field_simp [hden]
    <;> ring
  rw [hid, Real.rpow_add (by norm_num)]
  simp

theorem first_four_gap_scaled (degree : ℕ) (hdegree : 8 ≤ degree) :
    (1 ≤ (4-beardon degree)*(degree : ℝ) ∧ (4-beardon degree)*(degree : ℝ) ≤ 16) ∧
    (1 ≤ (4-conte degree)*(degree : ℝ) ∧ (4-conte degree)*(degree : ℝ) ≤ 16) ∧
    (1 ≤ (4-fujikawa degree)*(degree : ℝ) ∧ (4-fujikawa degree)*(degree : ℝ) ≤ 16) ∧
    (1 ≤ (4-dubinin degree)*(degree : ℝ) ∧ (4-dubinin degree)*(degree : ℝ) ≤ 16) := by
  have hd : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hdpos : 0 < (degree : ℝ) := by linarith
  have hm : 0 < (degree : ℝ)-1 := by linarith
  have hp : 0 < (degree : ℝ)+1 := by linarith
  let quotient : ℝ := (4 : ℝ)^(-1/((degree : ℝ)-1))
  let loss : ℝ := 1-quotient
  have hqle : quotient ≤ 1 := earlier_q_le_one degree (by omega)
  have hqpos : 0 < quotient := Real.rpow_pos_of_pos (by norm_num) _
  have hloss : 0 ≤ loss := by dsimp [loss]; linarith
  have hloglo : (1 : ℝ) ≤ Real.log 4 := by rw [earlier_log_four]; linarith [Real.log_two_gt_d9]
  have hloghi : Real.log (4 : ℝ) ≤ 2 := by rw [earlier_log_four]; linarith [Real.log_two_lt_d9]
  have hlogpos : 0 ≤ Real.log (4 : ℝ) := by linarith
  have hu : 0 ≤ Real.log 4/((degree : ℝ)-1) := by positivity
  have huone : Real.log 4/((degree : ℝ)-1) ≤ 1 := (div_le_one hm).2 (by linarith)
  have hexp := exp_lower _ hu
  have hqlow : Real.log 4/((degree : ℝ)-1)/2 ≤ loss := by
    dsimp [loss, quotient]
    rw [earlier_q_exp]
    nlinarith [mul_nonneg hu (sub_nonneg.mpr huone)]
  have hqup : loss ≤ Real.log 4/((degree : ℝ)-1) := earlier_q_log_bound_proved degree (by omega)
  have hscaledlo : Real.log 4/2 ≤ loss*((degree : ℝ)-1) := by
    apply (div_le_iff₀ hm).1
    convert hqlow using 1 <;> ring
  have hscaledhi : loss*((degree : ℝ)-1) ≤ 2 :=
    ((le_div_iff₀ hm).1 hqup).trans hloghi
  have hbeardon : 4-beardon degree = 4*loss := by rw [beardon_as_q degree (by omega)]; dsimp [loss]; ring
  have hbeardonBounds : 1 ≤ (4-beardon degree)*(degree : ℝ) ∧
      (4-beardon degree)*(degree : ℝ) ≤ 16 := by
    rw [hbeardon]
    constructor
    · nlinarith
    · have h := mul_nonneg hloss (by linarith : 0 ≤ (degree : ℝ)-2)
      nlinarith
  have hconte : 4-conte degree = 8/((degree : ℝ)+1) := by
    unfold conte
    field_simp
    <;> ring
  have hconteBounds : 1 ≤ (4-conte degree)*(degree : ℝ) ∧
      (4-conte degree)*(degree : ℝ) ≤ 16 := by
    rw [hconte, div_mul_eq_mul_div]
    constructor
    · apply (le_div_iff₀ hp).2
      linarith
    · apply (div_le_iff₀ hp).2
      linarith
  let bracket : ℝ := ((degree : ℝ)-2)*loss+2
  have hbnonneg : 0 ≤ ((degree : ℝ)-2)*loss := mul_nonneg (by linarith) hloss
  have hbLower : 2 ≤ bracket := by dsimp [bracket]; linarith
  have hbUpper : bracket ≤ 4 := by
    have h := (earlier_bracket_bound_proved degree hdegree).1.trans (earlier_bracket_bound_proved degree hdegree).2
    change bracket < (339/100 : ℝ) at h
    linarith
  have hfujikawa : 4-fujikawa degree = 4*bracket/((degree : ℝ)+1) := by
    unfold fujikawa
    rw [Nat.cast_sub (by omega : 2 ≤ degree)]
    norm_num only [Nat.cast_ofNat]
    dsimp [bracket, loss, quotient]
    field_simp
    <;> ring
  have hfujikawaBounds : 1 ≤ (4-fujikawa degree)*(degree : ℝ) ∧
      (4-fujikawa degree)*(degree : ℝ) ≤ 16 := by
    rw [hfujikawa, div_mul_eq_mul_div]
    constructor
    · apply (le_div_iff₀ hp).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hbLower) hdpos.le]
    · apply (div_le_iff₀ hp).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hbUpper) hdpos.le]
  have hdubinin : (4-dubinin degree)*(degree : ℝ) = 4+4*loss*((degree : ℝ)-1) := by
    unfold dubinin
    rw [beardon_as_q degree (by omega)]
    dsimp [loss, quotient]
    field_simp [ne_of_gt hdpos]
    <;> ring
  have hdubininBounds : 1 ≤ (4-dubinin degree)*(degree : ℝ) ∧
      (4-dubinin degree)*(degree : ℝ) ≤ 16 := by
    rw [hdubinin]
    constructor <;> nlinarith [mul_nonneg hloss hm.le]
  exact ⟨hbeardonBounds, hconteBounds, hfujikawaBounds, hdubininBounds⟩

theorem first_four_order_proved : ∀ bound ∈ ([beardon, conte, fujikawa, dubinin] : List (ℕ → ℝ)),
    ∃ lower upper : ℝ, 0 < lower ∧ lower ≤ upper ∧ ∀ᶠ degree : ℕ in atTop,
      lower/(degree : ℝ) ≤ 4-bound degree ∧ 4-bound degree ≤ upper/degree := by
  intro bound hbound
  refine ⟨1, 16, by norm_num, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (8 : ℕ)] with degree hdegree
  have hdpos : 0 < (degree : ℝ) := by exact_mod_cast (by omega : 0 < degree)
  have h := first_four_gap_scaled degree hdegree
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hbound
  rcases hbound with rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals first | apply (div_le_iff₀ hdpos).2 | apply (le_div_iff₀ hdpos).2
  all_goals tauto

end SmaleRate.Proofs

#check SmaleRate.Proofs.first_four_gap_scaled
#print axioms SmaleRate.Proofs.first_four_gap_scaled
#check SmaleRate.Proofs.first_four_order_proved
#print axioms SmaleRate.Proofs.first_four_order_proved
