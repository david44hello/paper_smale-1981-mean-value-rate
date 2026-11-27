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
open scoped Topology

theorem earlier_log_four : Real.log (4 : ℝ) = 2*Real.log 2 := by
  rw [show (4 : ℝ) = (2 : ℝ)^2 by norm_num, Real.log_pow]
  norm_num

theorem earlier_q_exp (degree : ℕ) :
    (4 : ℝ)^(-1/((degree : ℝ)-1)) = Real.exp (-(Real.log 4/((degree : ℝ)-1))) := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  congr 1
  ring

theorem earlier_q_log_bound_proved (degree : ℕ) (hdegree : 2 ≤ degree) :
    1-(4 : ℝ)^(-1/((degree : ℝ)-1)) ≤ Real.log 4/((degree : ℝ)-1) := by
  have hd : (2 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hden : 0 < (degree : ℝ)-1 := by linarith
  have hlog : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  rw [earlier_q_exp]
  exact general_exp_upper _ (by positivity : (0 : ℝ) ≤ Real.log 4/((degree : ℝ)-1))

theorem earlier_q_le_one (degree : ℕ) (hdegree : 2 ≤ degree) :
    (4 : ℝ)^(-1/((degree : ℝ)-1)) ≤ 1 := by
  have hd : (2 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hden : 0 < (degree : ℝ)-1 := by linarith
  have hlog : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  rw [earlier_q_exp, Real.exp_le_one_iff]
  have h : 0 ≤ Real.log 4/((degree : ℝ)-1) := by positivity
  linarith

theorem earlier_q_half_proved (degree : ℕ) (hdegree : 3 ≤ degree) :
    (1/2 : ℝ) ≤ (4 : ℝ)^(-1/((degree : ℝ)-1)) := by
  have hd : (3 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hexponent : (-1/2 : ℝ) ≤ -1/((degree : ℝ)-1) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by linarith : 0 < (degree : ℝ)-1)).2
    linarith
  have hhalf : (4 : ℝ)^(-1/2 : ℝ) = 1/2 := by
    rw [Real.rpow_def_of_pos (by norm_num), earlier_log_four]
    rw [show 2*Real.log 2*(-1/2) = -Real.log 2 by ring, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rw [← hhalf]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent

theorem earlier_q_eight_proved (degree : ℕ) (hdegree : 8 ≤ degree) :
    (4 : ℝ)^(-1/7 : ℝ) ≤ (4 : ℝ)^(-1/((degree : ℝ)-1)) ∧
    (4/5 : ℝ) < (4 : ℝ)^(-1/7 : ℝ) ∧
    (degree : ℝ)/(2*(degree : ℝ)-1) < (4/5 : ℝ) := by
  have hd : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  constructor
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 7) (by linarith : 0 < (degree : ℝ)-1)).2
    linarith
  · constructor
    · rw [Real.rpow_def_of_pos (by norm_num)]
      have h := Real.add_one_le_exp (Real.log 4*(-1/7))
      rw [earlier_log_four] at h ⊢
      linarith [Real.log_two_lt_d9]
    · apply (div_lt_iff₀ (by linarith : 0 < 2*(degree : ℝ)-1)).2
      linarith

theorem earlier_bracket_bound_proved (degree : ℕ) (hdegree : 8 ≤ degree) :
    ((degree : ℝ)-2)*(1-(4 : ℝ)^(-1/((degree : ℝ)-1)))+2 < Real.log 4+2 ∧
      Real.log 4+2 < 339/100 := by
  have hd : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hlogpos : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hquotient : ((degree : ℝ)-2)*(Real.log 4/((degree : ℝ)-1)) < Real.log 4 := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by linarith : 0 < (degree : ℝ)-1)).2
    nlinarith
  constructor
  · have h := mul_le_mul_of_nonneg_left (earlier_q_log_bound_proved degree (by omega))
      (by linarith : 0 ≤ (degree : ℝ)-2)
    linarith
  · rw [earlier_log_four]
    linarith [Real.log_two_lt_d9]

theorem earlier_endpoint_eight_proved : (432/100 : ℝ) < 9/Real.log 8 := by
  have hpos : 0 < Real.log (8 : ℝ) := Real.log_pos (by norm_num)
  have hlog8 : Real.log (8 : ℝ) = 3*Real.log 2 := by
    rw [show (8 : ℝ) = (2 : ℝ)^3 by norm_num, Real.log_pow]
    norm_num
  apply (lt_div_iff₀ hpos).2
  rw [hlog8]
  linarith [Real.log_two_lt_d9]

theorem earlier_difference_formulas_proved (degree : ℕ) (hdegree : 8 ≤ degree) :
    let quotient : ℝ := (4 : ℝ)^(-1/((degree : ℝ)-1))
    conte degree-fujikawa degree = 4*((degree : ℝ)-2)*(1-quotient)/((degree : ℝ)+1) ∧
    beardon degree-fujikawa degree = 4*(3*quotient-1)/((degree : ℝ)+1) ∧
    dubinin degree-fujikawa degree = 4*((2*(degree : ℝ)-1)*quotient-degree)/((degree : ℝ)*((degree : ℝ)+1)) := by
  have hd : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hcast : ((degree-2 : ℕ) : ℝ) = (degree : ℝ)-2 := by
    exact_mod_cast (Nat.cast_sub (by omega : 2 ≤ degree) : ((degree-2 : ℕ) : ℝ) = _)
  have hbeardon : beardon degree = 4*(4 : ℝ)^(-1/((degree : ℝ)-1)) := by
    unfold beardon
    have hden : (degree : ℝ)-1 ≠ 0 := ne_of_gt (by linarith)
    have hid : ((degree : ℝ)-2)/((degree : ℝ)-1) = 1+(-1/((degree : ℝ)-1)) := by
      field_simp [hden]
      <;> ring
    rw [hid, Real.rpow_add (by norm_num)]
    simp
  dsimp
  rw [hbeardon]
  unfold conte fujikawa dubinin beardon
  rw [hcast]
  have hid : (4 : ℝ)^(((degree : ℝ)-2)/((degree : ℝ)-1)) = 4*(4 : ℝ)^(-1/((degree : ℝ)-1)) := hbeardon
  rw [hid]
  constructor
  · field_simp
    <;> ring
  · constructor <;> field_simp <;> ring

theorem earlier_three_comparisons_proved (degree : ℕ) (hdegree : 8 ≤ degree) :
    fujikawa degree ≤ conte degree ∧ fujikawa degree < beardon degree ∧ fujikawa degree < dubinin degree := by
  have hd : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hq := earlier_q_eight_proved degree hdegree
  have hqgt : (4/5 : ℝ) < (4 : ℝ)^(-1/((degree : ℝ)-1)) := hq.2.1.trans_le hq.1
  have hidentities := earlier_difference_formulas_proved degree hdegree
  dsimp at hidentities
  have hconte : 0 ≤ conte degree-fujikawa degree := by
    rw [hidentities.1]
    have hdminus : 0 ≤ (degree : ℝ)-2 := by linarith
    have hqnonneg : 0 ≤ 1-(4 : ℝ)^(-1/((degree : ℝ)-1)) :=
      sub_nonneg.mpr (earlier_q_le_one degree (by omega))
    exact div_nonneg (by positivity [sub_nonneg.mpr (earlier_q_le_one degree (by omega))]) (by linarith)
  have hbeardon : 0 < beardon degree-fujikawa degree := by
    rw [hidentities.2.1]
    exact div_pos (by nlinarith) (by linarith)
  have hdubinin : 0 < dubinin degree-fujikawa degree := by
    rw [hidentities.2.2]
    have hprod : 0 < (2*(degree : ℝ)-1)*(4 : ℝ)^(-1/((degree : ℝ)-1))-(degree : ℝ) := by
      have h := mul_lt_mul_of_pos_left hqgt (by linarith : 0 < 2*(degree : ℝ)-1)
      nlinarith
    exact div_pos (by positivity) (by positivity)
  exact ⟨by linarith, by linarith, by linarith⟩

theorem earlier_ratio_lower (degree : ℕ) (hdegree : 8 ≤ degree) :
    (339/100 : ℝ)*ell degree < (degree : ℝ)+1 := by
  have hd : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hdpos : 0 < (degree : ℝ) := by linarith
  have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (degree : ℝ)/8)
  rw [Real.log_div (ne_of_gt hdpos) (by norm_num)] at hlog
  change Real.log (degree : ℝ)-Real.log 8 ≤ (degree : ℝ)/8-1 at hlog
  unfold ell
  linarith [finite_log_endpoints.2.1]

theorem earlier_fujikawa_comparison_proved (degree : ℕ) (hdegree : 8 ≤ degree) :
    target degree < fujikawa degree := by
  have hd : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have he : 0 < ell degree := lt_trans (by norm_num) (ell_gt_one degree hdegree)
  have hbracket := (earlier_bracket_bound_proved degree hdegree).1.trans
    (earlier_bracket_bound_proved degree hdegree).2
  have hratio := earlier_ratio_lower degree hdegree
  have hcast : ((degree-2 : ℕ) : ℝ) = (degree : ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ degree)]
    norm_num
  have hgap : 4-fujikawa degree =
      4*(((degree : ℝ)-2)*(1-(4 : ℝ)^(-1/((degree : ℝ)-1)))+2)/((degree : ℝ)+1) := by
    unfold fujikawa
    rw [hcast]
    field_simp
    <;> ring
  have hfirst : 4-fujikawa degree < 4*(339/100 : ℝ)/((degree : ℝ)+1) := by
    rw [hgap]
    apply (div_lt_div_iff_of_pos_right (by linarith : 0 < (degree : ℝ)+1)).2
    linarith
  have hsecond : 4*(339/100 : ℝ)/((degree : ℝ)+1) < 4/ell degree := by
    apply (div_lt_div_iff₀ (by linarith : 0 < (degree : ℝ)+1) he).2
    linarith
  unfold target
  linarith

theorem sqrt_log_minimum_proved (value : ℝ) (hvalue : 1 < value) :
    Real.exp 1/2 ≤ Real.sqrt value/Real.log value ∧
    (Real.sqrt value/Real.log value = Real.exp 1/2 ↔ value = Real.exp 2) := by
  have hvpos : 0 < value := by linarith
  have hlog : 0 < Real.log value := Real.log_pos hvalue
  have hroot : Real.sqrt value = Real.exp (Real.log value/2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hvpos]
    congr 1
    ring
  have harg : (1 : ℝ)+(Real.log value/2-1) = Real.log value/2 := by ring
  have hscale := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (Real.log value/2-1)) (Real.exp_nonneg 1)
  rw [← Real.exp_add, harg, ← hroot] at hscale
  constructor
  · apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hlog).2
    nlinarith
  · constructor
    · intro heq
      by_contra hne
      have hlogne : Real.log value/2-1 ≠ 0 := by
        intro hzero
        apply hne
        rw [← Real.exp_log hvpos]
        congr 1
        linarith
      have hstrict := mul_lt_mul_of_pos_left (Real.add_one_lt_exp hlogne) (Real.exp_pos 1)
      rw [← Real.exp_add, harg, ← hroot] at hstrict
      have heqmul := (div_eq_div_iff (ne_of_gt hlog) (by norm_num : (2 : ℝ) ≠ 0)).1 heq
      nlinarith
    · rintro rfl
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      norm_num

theorem earlier_crane_comparison_proved (degree : ℕ) (hdegree : 8 ≤ degree) :
    target degree < crane degree := by
  have hd : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hdpos : 0 < (degree : ℝ) := by linarith
  have hsqrt : 0 < Real.sqrt (degree : ℝ) := Real.sqrt_pos.mpr hdpos
  have hlog : 0 < Real.log (degree : ℝ) := Real.log_pos (by linarith)
  have hmin := (sqrt_log_minimum_proved (degree : ℝ) (by linarith)).1
  have hminmul := (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hlog).1 hmin
  have hpositive : 0 < 2*Real.exp 1-(2263/1000 : ℝ) := by linarith [Real.exp_one_gt_d9]
  have hstrict : 0 < (2*Real.exp 1-(2263/1000 : ℝ))*Real.log (degree : ℝ) :=
    mul_pos hpositive hlog
  have hquotient : (2263/1000 : ℝ)/Real.sqrt (degree : ℝ) < 4/Real.log (degree : ℝ) := by
    apply (div_lt_div_iff₀ hsqrt hlog).2
    nlinarith
  unfold target crane ell
  linarith

theorem d_plus_one_log_increasing_proved :
    StrictMonoOn (fun value : ℝ => (value+1)/Real.log value) (Ici 4) := by
  have hderivative (value : ℝ) (hvalue : 4 ≤ value) :
      HasDerivAt (fun value : ℝ => (value+1)/Real.log value)
        ((Real.log value-(value+1)/value)/(Real.log value)^2) value := by
    have hvpos : 0 < value := by linarith
    have hlog : 0 < Real.log value := Real.log_pos (by linarith)
    convert ((hasDerivAt_id value).add_const 1).div (Real.hasDerivAt_log (ne_of_gt hvpos)) (ne_of_gt hlog) using 1
    · funext argument
      simp only [Pi.div_apply, id_eq] <;> ring
    · simp only [id_eq] <;> ring
  apply strictMonoOn_of_deriv_pos (convex_Ici 4)
  · intro value hvalue
    exact (hderivative value hvalue).continuousAt.continuousWithinAt
  · intro value hvalue
    have hv : 4 ≤ value := interior_subset hvalue
    have hvpos : 0 < value := by linarith
    have hlog : 0 < Real.log value := Real.log_pos (by linarith)
    rw [(hderivative value hv).deriv]
    apply div_pos _ (sq_pos_of_pos hlog)
    have hloglower : Real.log (4 : ℝ) ≤ Real.log value := Real.log_le_log (by norm_num) hv
    have hratio : (value+1)/value ≤ (5/4 : ℝ) := by
      apply (div_le_iff₀ hvpos).2
      linarith
    rw [earlier_log_four] at hloglower
    linarith [Real.log_two_gt_d9]

end SmaleRate.Proofs


