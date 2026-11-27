/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Defs.Basic

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Polynomial
open scoped Topology

/-- The first-order exponential inequality used after the uniform infimum bound. -/
theorem general_exp_upper (value : ℝ) (hvalue : 0 ≤ value) :
    1 - Real.exp (-value) ≤ value := by
  linarith [Real.add_one_le_exp (-value)]

/-- The quadratic exponential inequality of Corollary 1.2, Step 3. -/
theorem exp_lower (value : ℝ) (hvalue : 0 ≤ value) :
    value - value ^ 2 / 2 ≤ 1 - Real.exp (-value) := by
  have hderivative (point : ℝ) :
      HasDerivAt (fun argument : ℝ =>
        1 - argument + argument ^ 2 / 2 - Real.exp (-argument))
        (-1 + point + Real.exp (-point)) point := by
    convert (((hasDerivAt_const point (1 : ℝ)).sub (hasDerivAt_id point)).add
      (((hasDerivAt_id point).pow 2).div_const 2)).sub
      ((Real.hasDerivAt_exp (-point)).comp point (hasDerivAt_id point).neg) using 1
    · ext argument
      simp [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, Function.comp_def]
    · simp only [id_eq]
      ring
  have hmonotone := monotone_of_hasDerivAt_nonneg hderivative (by
    intro point
    change 0 ≤ -1 + point + Real.exp (-point)
    linarith [Real.add_one_le_exp (-point)])
  have hcomparison := hmonotone hvalue
  norm_num at hcomparison
  linarith

/-- Non-strict zero endpoint is useful for the proposition's sigma estimate. -/
theorem neg_log_one_sub_le (value : ℝ) (hzero : 0 ≤ value) (hone : value < 1) :
    -Real.log (1 - value) ≤ value / (1 - value) := by
  have hdenominator : 0 < 1 - value := sub_pos.mpr hone
  have hlog := Real.one_sub_inv_le_log_of_pos hdenominator
  have hidentity : (1 - value)⁻¹ - 1 = value / (1 - value) := by
    field_simp
    ring
  linarith

/-- The named logarithm inequality used in the tail proof. -/
theorem log_one_sub (value : ℝ) (hvalue : value ∈ Ioo 0 1) :
    -Real.log (1 - value) ≤ value / (1 - value) :=
  neg_log_one_sub_le value hvalue.1.le hvalue.2

/-- The half-interval logarithm estimate used in Proposition 3.4. -/
theorem log_one_sub_half (value : ℝ) (hvalue : value ∈ Icc 0 (1 / 2 : ℝ)) :
    -Real.log (1 - value) ≤ 2 * value := by
  have hone : value < 1 := by linarith [hvalue.2]
  refine (neg_log_one_sub_le value hvalue.1 hone).trans ?_
  apply (div_le_iff₀ (sub_pos.mpr hone)).2
  nlinarith [hvalue.1, hvalue.2]

/-- Arithmetic minimum of the printed margins, not an unrounded analytic minimum. -/
theorem table3_printed_minimum :
    ∀ entry ∈ ([(8,1733),(9,9090),(10,14865),(11,19526),(12,23372),
      (13,26604),(14,29361),(15,31743),(16,33823),(17,35655),(18,37283),
      (19,38740),(20,40052)] : List (ℕ × ℕ)),
      (1733 : ℕ) ≤ entry.2 ∧ (entry.2 = 1733 ↔ entry.1 = 8) := by
  intro entry hentry
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hentry
  rcases hentry with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> norm_num

theorem tail_log_correction_of_three (length : ℝ) (hlength : 3 ≤ length) :
    1 / (4 * length) - Real.log (1 - 1 / length) ≤ (7 / 4) / length := by
  have hpositive : 0 < length := by linarith
  have hminus : 0 < length - 1 := by linarith
  have hinverse : (1 / length : ℝ) ∈ Ioo 0 1 := by
    constructor
    · positivity
    · exact (div_lt_one hpositive).2 (by linarith)
  have hlog := log_one_sub (1 / length) hinverse
  have hidentity : (1 / length) / (1 - 1 / length) = 1 / (length - 1) := by
    field_simp
  have hrational : 1 / (length - 1) ≤ (3 / 2) / length := by
    apply (div_le_div_iff₀ hminus hpositive).2
    linarith
  have hsum : 1 / (4 * length) + (3 / 2) / length = (7 / 4) / length := by ring
  rw [hidentity] at hlog
  linarith

theorem log_twenty_one_gt_three : (3 : ℝ) < Real.log 21 := by
  have hsmall := Real.one_sub_inv_le_log_of_pos (show 0 < (7 / 8 : ℝ) by norm_num)
  have hidentity : Real.log 21 = 3 * Real.log 2 + Real.log 3 + Real.log (7 / 8) := by
    calc
      Real.log 21 = Real.log ((2 : ℝ) ^ 3 * 3 * (7 / 8)) := by norm_num
      _ = _ := by
        rw [Real.log_mul (by norm_num : (2 : ℝ)^3 * 3 ≠ 0) (by norm_num : (7/8 : ℝ) ≠ 0),
          Real.log_mul (by norm_num : (2 : ℝ)^3 ≠ 0) (by norm_num : (3 : ℝ) ≠ 0),
          Real.log_pow]
        norm_num
  norm_num at hsmall
  rw [hidentity]
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

theorem ell_three_le (degree : ℕ) (hdegree : 21 ≤ degree) : 3 ≤ ell degree := by
  have hcast : (21 : ℝ) ≤ degree := by exact_mod_cast hdegree
  exact log_twenty_one_gt_three.le.trans
    (Real.log_le_log (by norm_num) hcast)

theorem tail_log_correction (degree : ℕ) (hdegree : 21 ≤ degree) :
    1 / (4 * ell degree) - Real.log (1 - 1 / ell degree) ≤ (7 / 4) / ell degree :=
  tail_log_correction_of_three (ell degree) (ell_three_le degree hdegree)

theorem log_ninety_six_lt_five : Real.log 96 < (5 : ℝ) := by
  have hidentity : Real.log 96 = 5 * Real.log 2 + Real.log 3 := by
    calc
      Real.log 96 = Real.log ((2 : ℝ) ^ 5 * 3) := by norm_num
      _ = _ := by rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; norm_num
  rw [hidentity]
  linarith [Real.log_two_lt_d9, Real.log_three_lt_d9]

/-- A looser elementary bound suffices for closing the large-degree case. -/
theorem log_scaled_le_five_thirds (length : ℝ) (hlength : 3 ≤ length) :
    Real.log (32 * length) ≤ (5 / 3) * length := by
  have hpositive : 0 < length := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hpositive (by norm_num : (0:ℝ)<3))
  have hidentity : Real.log (32 * length) = Real.log 96 + Real.log (length / 3) := by
    rw [← Real.log_mul (by norm_num : (96 : ℝ) ≠ 0) (ne_of_gt (div_pos hpositive (by norm_num)))]
    congr 1
    ring
  rw [hidentity]
  linarith [log_ninety_six_lt_five]

/-- Step 1's reciprocal comparison, with each mu fact exposed separately. -/
theorem cor_step1_mu_of (degree : ℕ) (length : ℝ)
    (hpositive : 0 < mu (complement (radius degree length)))
    (hcomplement : mu (radius degree length) * mu (complement (radius degree length)) =
      Real.pi ^ 2 / 4)
    (hupper : mu (complement (radius degree length)) <
      Real.log (4 / complement (radius degree length))) :
    Real.pi ^ 2 / (4 * Real.log (4 / complement (radius degree length))) <
      mu (radius degree length) := by
  have hlogpositive := hpositive.trans hupper
  have hproduct : 0 < mu (radius degree length) * mu (complement (radius degree length)) := by
    rw [hcomplement]
    positivity
  have hmu := (mul_pos_iff_of_pos_right hpositive).mp hproduct
  apply (div_lt_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hlogpositive)).2
  nlinarith [mul_pos hmu (sub_pos.mpr hupper)]

theorem cor_step1_beta_lt_majorant_of (degree : ℕ)
    (hmu : Real.pi ^ 2 /
      (4 * Real.log (4 / complement (radius degree (Lchoice degree)))) <
        mu (radius degree (Lchoice degree))) :
    beta degree (Lchoice degree) < majorant degree := by
  unfold beta majorant
  apply mul_lt_mul_of_pos_left _ (by norm_num : (0:ℝ)<4)
  exact Real.exp_lt_exp.mpr (sub_lt_sub_left hmu (Lchoice degree))

theorem ell_gt_one (degree : ℕ) (hdegree : 8 ≤ degree) : 1 < ell degree := by
  have hlog : (1 : ℝ) < Real.log 8 := by
    rw [show (8 : ℝ) = (2 : ℝ)^3 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_gt_d9]
  have hcast : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  exact hlog.trans_le (Real.log_le_log (by norm_num) hcast)

theorem chosen_length_bounds (degree : ℕ) (hdegree : 8 ≤ degree) :
    0 < Lchoice degree ∧ Lchoice degree < (degree : ℝ) := by
  have hell := ell_gt_one degree hdegree
  have hcast : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  constructor
  · unfold Lchoice
    positivity
  · unfold Lchoice
    apply (div_lt_iff₀ (by linarith : 0 < 4 * ell degree)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ ell degree - 1)
      (by linarith : 0 ≤ (degree : ℝ) - 8)]

theorem lambda_chosen_identity (degree : ℕ) (hdegree : 8 ≤ degree) :
    lambda degree (Lchoice degree) = ell degree + Real.log (32 * ell degree) -
      Real.log (1 - Lchoice degree / degree) := by
  have hell := ell_gt_one degree hdegree
  have hcast : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hdpositive : 0 < (degree : ℝ) := by linarith
  have hlength := chosen_length_bounds degree hdegree
  have hlast : 0 < 1 - Lchoice degree / degree := by
    exact sub_pos.mpr ((div_lt_one hdpositive).2 hlength.2)
  have hidentity : 8 * (degree : ℝ) / (Lchoice degree * (1 - Lchoice degree / degree)) =
      (degree : ℝ) * (32 * ell degree) / (1 - Lchoice degree / degree) := by
    unfold Lchoice
    field_simp
    <;> ring
  unfold lambda
  rw [hidentity, Real.log_div (by positivity) (ne_of_gt hlast),
    Real.log_mul (ne_of_gt hdpositive) (by positivity)]
  rfl

/-- A slightly looser route than the printed 2.53 coefficient; enough for the same conclusion. -/
theorem tail_lambda_loose (degree : ℕ) (hdegree : 21 ≤ degree) :
    0 < lambda degree (Lchoice degree) ∧ lambda degree (Lchoice degree) ≤ (11 / 4) * ell degree := by
  have hd8 : 8 ≤ degree := by omega
  have hell := ell_three_le degree hdegree
  have hcast : (21 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hdpositive : 0 < (degree : ℝ) := by linarith
  have hlpositive : 0 < ell degree := by linarith
  have hratio_nonneg : 0 ≤ Lchoice degree / (degree : ℝ) := by
    unfold Lchoice
    positivity
  have hlarge : (12 : ℝ) ≤ 4 * ell degree * (degree : ℝ) := by
    calc
      (12 : ℝ) = 12 * 1 := by norm_num
      _ ≤ 4 * ell degree * (degree : ℝ) := by gcongr <;> linarith
  have hratio : Lchoice degree / (degree : ℝ) ≤ (1 / 12 : ℝ) := by
    unfold Lchoice
    rw [div_div]
    apply (div_le_iff₀ (by positivity : 0 < 4 * ell degree * (degree : ℝ))).2
    linarith
  have hlog := log_one_sub_half (Lchoice degree / (degree : ℝ))
    ⟨hratio_nonneg, by linarith⟩
  have hlast : 0 < 1 - Lchoice degree / (degree : ℝ) := by linarith
  have hnonpos : Real.log (1 - Lchoice degree / (degree : ℝ)) ≤ 0 := by
    exact Real.log_nonpos hlast.le (by linarith)
  have hnonneg : 0 ≤ Real.log (32 * ell degree) := Real.log_nonneg (by linarith)
  rw [lambda_chosen_identity degree hd8]
  constructor
  · linarith
  · linarith [log_scaled_le_five_thirds (ell degree) hell]

theorem tail_star (degree : ℕ) (hdegree : 21 ≤ degree) :
    1 / (4 * ell degree) - Real.log (1 - 1 / ell degree) ≤
      Real.pi ^ 2 / (2 * lambda degree (Lchoice degree)) := by
  have hell := ell_three_le degree hdegree
  have hpositive : 0 < ell degree := by linarith
  have hlambda := tail_lambda_loose degree hdegree
  have hpi : (77 / 8 : ℝ) < Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_d2, Real.pi_pos]
  refine (tail_log_correction degree hdegree).trans ?_
  apply (div_le_div_iff₀ hpositive (mul_pos (by norm_num : (0:ℝ)<2) hlambda.1)).2
  nlinarith [mul_pos (sub_pos.mpr hpi) hpositive]

theorem radius_mem (degree : ℕ) (hdegree : 2 ≤ degree) (length : ℝ) (hlength : 0 < length) :
    radius degree length ∈ Ioo 0 1 := by
  have hcast : (2 : ℝ) ≤ degree := by exact_mod_cast hdegree
  constructor
  · exact Real.exp_pos _
  · apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hlength) (by linarith)

theorem complement_mem (value : ℝ) (hvalue : value ∈ Ioo 0 1) :
    complement value ∈ Ioo 0 1 := by
  have harg : 0 < 1 - value ^ 2 := by nlinarith [hvalue.1, hvalue.2]
  have hpositive : 0 < complement value := Real.sqrt_pos.mpr harg
  have hsquare : (complement value)^2 = 1 - value^2 := Real.sq_sqrt harg.le
  exact ⟨hpositive, by nlinarith [hvalue.1]⟩

theorem radius_sq (degree : ℕ) (length : ℝ) :
    (radius degree length)^2 = Real.exp (-2 * (length / degree)) := by
  unfold radius
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem complement_radius_sq (degree : ℕ) (hdegree : 2 ≤ degree)
    (length : ℝ) (hlength : 0 < length) :
    (complement (radius degree length))^2 = 1 - Real.exp (-2 * (length / degree)) := by
  have hmem := radius_mem degree hdegree length hlength
  have harg : 0 ≤ 1 - (radius degree length)^2 := by nlinarith [hmem.1, hmem.2]
  unfold complement
  rw [Real.sq_sqrt harg, radius_sq]

theorem log_complement_le_half_lambda (degree : ℕ) (hdegree : 2 ≤ degree)
    (length : ℝ) (hlength : length ∈ Ioo 0 (degree : ℝ)) :
    0 < lambda degree length ∧
    Real.log (4 / complement (radius degree length)) ≤ lambda degree length / 2 := by
  have hdcast : (2 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hdpositive : 0 < (degree : ℝ) := by linarith
  have hratio : 0 < length / (degree : ℝ) := div_pos hlength.1 hdpositive
  have hone : 0 < 1 - length / (degree : ℝ) :=
    sub_pos.mpr ((div_lt_one hdpositive).2 hlength.2)
  have hcomp := complement_mem (radius degree length) (radius_mem degree hdegree length hlength.1)
  have hquadratic : 2 * (length / (degree : ℝ)) * (1 - length / (degree : ℝ)) ≤
      (complement (radius degree length))^2 := by
    rw [complement_radius_sq degree hdegree length hlength.1]
    have hexp := exp_lower (2 * (length / (degree : ℝ))) (by positivity)
    convert hexp using 1 <;> ring
  have hscaled := mul_le_mul_of_nonneg_left hquadratic
    (by positivity : (0 : ℝ) ≤ 8 * (degree : ℝ))
  have hid : 8 * (degree : ℝ) * (2 * (length / (degree : ℝ)) * (1 - length / (degree : ℝ))) =
      16 * (length * (1 - length / (degree : ℝ))) := by
    field_simp
    <;> ring
  rw [hid] at hscaled
  have hratio_bound : (4 / complement (radius degree length))^2 ≤
      8 * (degree : ℝ) / (length * (1 - length / (degree : ℝ))) := by
    rw [div_pow]
    norm_num only [show (4 : ℝ)^2 = 16 by norm_num]
    exact (div_le_div_iff₀ (sq_pos_of_pos hcomp.1) (mul_pos hlength.1 hone)).2 hscaled
  have hlog := Real.log_le_log (sq_pos_of_pos (div_pos (by norm_num : (0:ℝ)<4) hcomp.1)) hratio_bound
  rw [Real.log_pow] at hlog
  have hlogpositive : 0 < Real.log (4 / complement (radius degree length)) := by
    apply Real.log_pos
    apply (lt_div_iff₀ hcomp.1).2
    linarith [hcomp.2]
  change 2 * Real.log (4 / complement (radius degree length)) ≤ lambda degree length at hlog
  constructor <;> linarith

theorem majorant_le_elementary (degree : ℕ) (hdegree : 8 ≤ degree) :
    majorant degree ≤ 4 * Real.exp (Lchoice degree - Real.pi^2 / (2 * lambda degree (Lchoice degree))) := by
  have hd2 : 2 ≤ degree := by omega
  have hlength := chosen_length_bounds degree hdegree
  have hlog := log_complement_le_half_lambda degree hd2 (Lchoice degree) hlength
  have hcomp := complement_mem (radius degree (Lchoice degree))
    (radius_mem degree hd2 (Lchoice degree) hlength.1)
  have hpositive : 0 < Real.log (4 / complement (radius degree (Lchoice degree))) := by
    apply Real.log_pos
    apply (lt_div_iff₀ hcomp.1).2
    linarith [hcomp.2]
  have hdivision : Real.pi^2 / (2 * lambda degree (Lchoice degree)) ≤
      Real.pi^2 / (4 * Real.log (4 / complement (radius degree (Lchoice degree)))) := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hlog.1)
      (mul_pos (by norm_num : (0:ℝ)<4) hpositive)).2
    nlinarith [mul_nonneg (sq_nonneg Real.pi)
      (show 0 ≤ 2 * lambda degree (Lchoice degree) -
        4 * Real.log (4 / complement (radius degree (Lchoice degree))) by linarith [hlog.2])]
  unfold majorant
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_left hdivision (Lchoice degree)))
    (by norm_num : (0:ℝ) ≤ 4)

theorem cor_step3 (degree : ℕ) (hdegree : 21 ≤ degree) : majorant degree ≤ target degree := by
  have hell := ell_three_le degree hdegree
  have hpositive : 0 < ell degree := by linarith
  have htarget : 0 < 1 - 1 / ell degree := by
    exact sub_pos.mpr ((div_lt_one hpositive).2 (by linarith))
  have hstar := tail_star degree hdegree
  have hexponent : Lchoice degree - Real.pi^2 / (2 * lambda degree (Lchoice degree)) ≤
      Real.log (1 - 1 / ell degree) := by
    dsimp only [Lchoice] at hstar ⊢
    linarith
  refine (majorant_le_elementary degree (by omega)).trans ?_
  calc
    4 * Real.exp (Lchoice degree - Real.pi^2 / (2 * lambda degree (Lchoice degree))) ≤
        4 * Real.exp (Real.log (1 - 1 / ell degree)) := by gcongr
    _ = target degree := by rw [Real.exp_log htarget]; unfold target; ring

theorem exp_lower_eight (value : ℝ) (hvalue : |value| ≤ 1) :
    (∑ index ∈ Finset.range 8, value ^ index / (index.factorial : ℝ)) -
      |value|^8 * (9 / (40320 * 8)) ≤ Real.exp value := by
  have hbound := Real.exp_bound (x := value) (n := 8) hvalue (by norm_num)
  norm_num only [Nat.factorial] at hbound
  linarith [(abs_sub_le_iff.mp hbound).2]

theorem exp_three_tenths_lower : (1348 / 1000 : ℝ) ≤ Real.exp (3 / 10) := by
  have hbound := exp_lower_eight (3 / 10) (by norm_num)
  norm_num [Finset.sum_range_succ] at hbound
  linarith

theorem exp_eighty_one_hundredths_lower : (2247 / 1000 : ℝ) ≤ Real.exp (81 / 100) := by
  have hbound := exp_lower_eight (81 / 100) (by norm_num)
  norm_num [Finset.sum_range_succ] at hbound
  linarith

theorem exp_sixty_one_hundredths_lower : (184 / 100 : ℝ) ≤ Real.exp (61 / 100) := by
  have hbound := exp_lower_eight (61 / 100) (by norm_num)
  norm_num [Finset.sum_range_succ] at hbound
  linarith

theorem exp_sixty_six_hundredths_lower : (1933 / 1000 : ℝ) ≤ Real.exp (66 / 100) := by
  have hbound := exp_lower_eight (66 / 100) (by norm_num)
  norm_num [Finset.sum_range_succ] at hbound
  linarith

theorem exp_six_zero_nine_lower : (1838 / 1000 : ℝ) ≤ Real.exp (609 / 1000) := by
  have hbound := exp_lower_eight (609 / 1000) (by norm_num)
  norm_num [Finset.sum_range_succ] at hbound
  linarith

theorem exp_fifty_four_hundredths_lower : (171 / 100 : ℝ) ≤ Real.exp (54 / 100) := by
  have hbound := exp_lower_eight (54 / 100) (by norm_num)
  norm_num [Finset.sum_range_succ] at hbound
  linarith

theorem exp_integer_lower (index : ℕ) : (2718 / 1000 : ℝ)^index ≤ Real.exp index := by
  have hbase : (2718 / 1000 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hpower : (2718 / 1000 : ℝ)^index ≤ (Real.exp 1)^index := by gcongr
  simpa only [← Real.exp_nat_mul, mul_one] using hpower

theorem log_finite_caps : Real.log (542 : ℝ) < 63 / 10 ∧
    Real.log (900 : ℝ) < 681 / 100 ∧ Real.log (2000 : ℝ) < 761 / 100 := by
  have hfirst : (542 : ℝ) < Real.exp (63 / 10) := by
    calc
      (542 : ℝ) < (2718/1000 : ℝ)^6 * (1348/1000) := by norm_num
      _ ≤ Real.exp (6 : ℕ) * Real.exp (3/10) :=
        mul_le_mul (exp_integer_lower 6) exp_three_tenths_lower (by norm_num) (Real.exp_nonneg _)
      _ = Real.exp (63/10) := by rw [← Real.exp_add]; congr 1; norm_num
  have hsecond : (900 : ℝ) < Real.exp (681 / 100) := by
    calc
      (900 : ℝ) < (2718/1000 : ℝ)^6 * (2247/1000) := by norm_num
      _ ≤ Real.exp (6 : ℕ) * Real.exp (81/100) :=
        mul_le_mul (exp_integer_lower 6) exp_eighty_one_hundredths_lower (by norm_num) (Real.exp_nonneg _)
      _ = Real.exp (681/100) := by rw [← Real.exp_add]; congr 1; norm_num
  have hthird : (2000 : ℝ) < Real.exp (761 / 100) := by
    calc
      (2000 : ℝ) < (2718/1000 : ℝ)^7 * (184/100) := by norm_num
      _ ≤ Real.exp (7 : ℕ) * Real.exp (61/100) :=
        mul_le_mul (exp_integer_lower 7) exp_sixty_one_hundredths_lower (by norm_num) (Real.exp_nonneg _)
      _ = Real.exp (761/100) := by rw [← Real.exp_add]; congr 1; norm_num
  exact ⟨(Real.log_lt_iff_lt_exp (by norm_num)).2 hfirst,
    (Real.log_lt_iff_lt_exp (by norm_num)).2 hsecond,
    (Real.log_lt_iff_lt_exp (by norm_num)).2 hthird⟩

theorem exp_negative_finite_bounds : 4 * Real.exp (-(66/100 : ℝ)) < 207/100 ∧
    4 * Real.exp (-(609/1000 : ℝ)) < 1089/500 ∧
    4 * Real.exp (-(54/100 : ℝ)) < 47/20 := by
  constructor
  · rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (Real.exp_pos _)).2
    nlinarith [exp_sixty_six_hundredths_lower]
  · constructor
    · rw [Real.exp_neg, ← div_eq_mul_inv]
      apply (div_lt_iff₀ (Real.exp_pos _)).2
      nlinarith [exp_six_zero_nine_lower]
    · rw [Real.exp_neg, ← div_eq_mul_inv]
      apply (div_lt_iff₀ (Real.exp_pos _)).2
      nlinarith [exp_fifty_four_hundredths_lower]

theorem finite_log_endpoints :
    (83/40 : ℝ) ≤ Real.log 8 ∧ Real.log 8 ≤ 25/12 ∧
    (2197/1000 : ℝ) ≤ Real.log 9 ∧
    (62/25 : ℝ) ≤ Real.log 12 ∧ Real.log 12 ≤ 5/2 ∧ Real.log 20 ≤ 3 := by
  have height : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = (2 : ℝ)^3 by norm_num, Real.log_pow]; norm_num
  have hnine : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = (3 : ℝ)^2 by norm_num, Real.log_pow]; norm_num
  have htwelve : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12 : ℝ) = (2 : ℝ)^2 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; norm_num
  have htwenty : Real.log 20 = 2 * Real.log 2 + Real.log 5 := by
    rw [show (20 : ℝ) = (2 : ℝ)^2 * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; norm_num
  rw [height, hnine, htwelve, htwenty]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9,
    Real.log_three_gt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]

theorem chosen_length_interval (degree : ℕ) (lower upper : ℝ)
    (hpositive : 0 < ell degree) (hlower : lower * (4 * ell degree) ≤ 1)
    (hupper : 1 ≤ upper * (4 * ell degree)) :
    lower ≤ Lchoice degree ∧ Lchoice degree ≤ upper := by
  unfold Lchoice
  exact ⟨(le_div_iff₀ (by positivity)).2 hlower,
    (div_le_iff₀ (by positivity)).2 hupper⟩

theorem lambda_le_log_of_interval (degree : ℕ) (length lowerDegree upperDegree lowerLength upperLength cap : ℝ)
    (hdegree : 2 ≤ degree) (hdegreepos : 0 < lowerDegree)
    (hdegrees : lowerDegree ≤ (degree : ℝ) ∧ (degree : ℝ) ≤ upperDegree)
    (hlengthpos : 0 < lowerLength) (hlengths : lowerLength ≤ length ∧ length ≤ upperLength)
    (hsmall : upperLength < lowerDegree) (hcapnonneg : 0 ≤ cap)
    (hcap : 8 * upperDegree ≤ cap * (lowerLength * (1 - upperLength / lowerDegree))) :
    lambda degree length ≤ Real.log cap := by
  have hdpos : 0 < (degree : ℝ) := hdegreepos.trans_le hdegrees.1
  have hlpos : 0 < length := hlengthpos.trans_le hlengths.1
  have hupos : 0 < upperLength := hlpos.trans_le hlengths.2
  have hratio : length / (degree : ℝ) ≤ upperLength / lowerDegree := by
    apply (div_le_div_iff₀ hdpos hdegreepos).2
    exact (mul_le_mul_of_nonneg_right hlengths.2 hdegreepos.le).trans
      (mul_le_mul_of_nonneg_left hdegrees.1 hupos.le)
  have hunit : 0 < 1 - upperLength / lowerDegree :=
    sub_pos.mpr ((div_lt_one hdegreepos).2 hsmall)
  have hdenpos : 0 < length * (1 - length / (degree : ℝ)) := by
    exact mul_pos hlpos (by linarith)
  have hden : lowerLength * (1 - upperLength / lowerDegree) ≤
      length * (1 - length / (degree : ℝ)) :=
    mul_le_mul hlengths.1 (sub_le_sub_left hratio 1) hunit.le hlpos.le
  unfold lambda
  apply Real.log_le_log (div_pos (mul_pos (by norm_num : (0:ℝ)<8) hdpos) hdenpos)
  apply (div_le_iff₀ hdenpos).2
  exact (mul_le_mul_of_nonneg_left hdegrees.2 (by norm_num : (0:ℝ)≤8)).trans
    (hcap.trans (mul_le_mul_of_nonneg_left hden hcapnonneg))

theorem majorant_lt_of_parameters (degree : ℕ) (hdegree : 8 ≤ degree)
    (upperLength upperLambda decay bound : ℝ)
    (hlength : Lchoice degree ≤ upperLength)
    (hlambda : lambda degree (Lchoice degree) ≤ upperLambda)
    (hdecay : 0 ≤ upperLength + decay)
    (hpi : (upperLength + decay) * (2 * upperLambda) ≤ Real.pi^2)
    (hexp : 4 * Real.exp (-decay) < bound) : majorant degree < bound := by
  have hchosen := chosen_length_bounds degree hdegree
  have hlog := log_complement_le_half_lambda degree (by omega) (Lchoice degree) hchosen
  have hquotient : upperLength + decay ≤ Real.pi^2 / (2 * lambda degree (Lchoice degree)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hlog.1)).2
    exact (mul_le_mul_of_nonneg_left (by linarith :
      2 * lambda degree (Lchoice degree) ≤ 2 * upperLambda) hdecay).trans hpi
  refine lt_of_le_of_lt ((majorant_le_elementary degree hdegree).trans ?_) hexp
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤4)
  apply Real.exp_le_exp.mpr
  linarith

theorem target_gt_of_log_lower (degree : ℕ) (lower bound : ℝ)
    (hpositive : 0 < ell degree) (hlower : lower ≤ ell degree)
    (hbound : bound < 4) (hstrict : 4 < (4 - bound) * lower) : bound < target degree := by
  have hdivide : 4 / ell degree < 4 - bound := by
    apply (div_lt_iff₀ hpositive).2
    exact hstrict.trans_le (mul_le_mul_of_nonneg_left hlower (by linarith))
  unfold target
  linarith

theorem cor_finite_eight : majorant 8 < target 8 := by
  have hlow : (83/40 : ℝ) ≤ ell 8 := by simpa [ell] using finite_log_endpoints.1
  have hupp : ell 8 ≤ (25/12 : ℝ) := by simpa [ell] using finite_log_endpoints.2.1
  have hpos : 0 < ell 8 := by linarith
  have hlength := chosen_length_interval 8 (3/25) (121/1000) hpos
    (by linarith) (by linarith)
  have hlambda := lambda_le_log_of_interval 8 (Lchoice 8) 8 8 (3/25) (121/1000) 542
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlength
    (by norm_num) (by norm_num) (by norm_num)
  have hmajorant : majorant 8 < (207/100 : ℝ) :=
    majorant_lt_of_parameters 8 (by norm_num) (121/1000) (63/10) (66/100) (207/100)
      hlength.2 (hlambda.trans log_finite_caps.1.le) (by norm_num)
      (by nlinarith [Real.pi_gt_d2, Real.pi_pos]) exp_negative_finite_bounds.1
  exact hmajorant.trans (target_gt_of_log_lower 8 (83/40) (207/100)
    hpos hlow (by norm_num) (by norm_num))

theorem cor_finite_middle (degree : ℕ) (hlower : 9 ≤ degree) (hupper : degree ≤ 11) :
    majorant degree < target degree := by
  have hdlo : (9 : ℝ) ≤ degree := by exact_mod_cast hlower
  have hdhi : (degree : ℝ) ≤ 11 := by exact_mod_cast hupper
  have hlow : (2197/1000 : ℝ) ≤ ell degree :=
    finite_log_endpoints.2.2.1.trans (Real.log_le_log (by norm_num) hdlo)
  have hupp : ell degree ≤ (5/2 : ℝ) :=
    (Real.log_le_log (by linarith : 0 < (degree : ℝ)) (by linarith : (degree : ℝ) ≤ 12)).trans
      finite_log_endpoints.2.2.2.2.1
  have hpos : 0 < ell degree := by linarith
  have hlength := chosen_length_interval degree (1/10) (114/1000) hpos
    (by linarith) (by linarith)
  have hlambda := lambda_le_log_of_interval degree (Lchoice degree) 9 11 (1/10) (114/1000) 900
    (by omega) (by norm_num) ⟨hdlo, hdhi⟩ (by norm_num) hlength
    (by norm_num) (by norm_num) (by norm_num)
  have hmajorant : majorant degree < (1089/500 : ℝ) :=
    majorant_lt_of_parameters degree (by omega) (114/1000) (681/100) (609/1000) (1089/500)
      hlength.2 (hlambda.trans log_finite_caps.2.1.le) (by norm_num)
      (by nlinarith [Real.pi_gt_d2, Real.pi_pos]) exp_negative_finite_bounds.2.1
  exact hmajorant.trans (target_gt_of_log_lower degree (2197/1000) (1089/500)
    hpos hlow (by norm_num) (by norm_num))

theorem cor_finite_upper (degree : ℕ) (hlower : 12 ≤ degree) (hupper : degree ≤ 20) :
    majorant degree < target degree := by
  have hdlo : (12 : ℝ) ≤ degree := by exact_mod_cast hlower
  have hdhi : (degree : ℝ) ≤ 20 := by exact_mod_cast hupper
  have hlow : (62/25 : ℝ) ≤ ell degree :=
    finite_log_endpoints.2.2.2.1.trans (Real.log_le_log (by norm_num) hdlo)
  have hupp : ell degree ≤ (3 : ℝ) :=
    (Real.log_le_log (by linarith : 0 < (degree : ℝ)) hdhi).trans finite_log_endpoints.2.2.2.2.2
  have hpos : 0 < ell degree := by linarith
  have hlength := chosen_length_interval degree (1/12) (101/1000) hpos
    (by linarith) (by linarith)
  have hlambda := lambda_le_log_of_interval degree (Lchoice degree) 12 20 (1/12) (101/1000) 2000
    (by omega) (by norm_num) ⟨hdlo, hdhi⟩ (by norm_num) hlength
    (by norm_num) (by norm_num) (by norm_num)
  have hmajorant : majorant degree < (47/20 : ℝ) :=
    majorant_lt_of_parameters degree (by omega) (101/1000) (761/100) (54/100) (47/20)
      hlength.2 (hlambda.trans log_finite_caps.2.2.le) (by norm_num)
      (by nlinarith [Real.pi_gt_d2, Real.pi_pos]) exp_negative_finite_bounds.2.2
  exact hmajorant.trans (target_gt_of_log_lower degree (62/25) (47/20)
    hpos hlow (by norm_num) (by norm_num))

theorem cor_step2 (degree : ℕ) (hdegree : 8 ≤ degree) (hupper : degree ≤ 20) :
    majorant degree < target degree := by
  by_cases height : degree = 8
  · subst degree
    exact cor_finite_eight
  · by_cases hmiddle : degree ≤ 11
    · exact cor_finite_middle degree (by omega) hmiddle
    · exact cor_finite_upper degree (by omega) hupper

theorem majorant_le_target (degree : ℕ) (hdegree : 8 ≤ degree) : majorant degree ≤ target degree := by
  by_cases hsmall : degree ≤ 20
  · exact (cor_step2 degree hdegree hsmall).le
  · exact cor_step3 degree (by omega)

theorem ybound_exp_eq_beta (degree : ℕ) (length : ℝ) :
    yBound degree (Real.exp (-length)) = beta degree length := by
  have hradius : (Real.exp (-length))^(1/(degree : ℝ)) = radius degree length := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _) _, Real.log_exp]
    unfold radius
    congr 1
    ring
  calc
    yBound degree (Real.exp (-length)) =
        (4/Real.exp (-length))*Real.exp (-mu (radius degree length)) := by rw [yBound, hradius]
    _ = 4*Real.exp length*Real.exp (-mu (radius degree length)) := by
      rw [Real.exp_neg, div_inv_eq_mul]
    _ = beta degree length := by
      rw [mul_assoc, ← Real.exp_add]
      unfold beta
      congr 2

theorem beta_y_change (degree : ℕ) :
    yBound degree '' Ioo 0 1 = beta degree '' Ioi 0 := by
  ext value
  constructor
  · rintro ⟨height, hheight, rfl⟩
    refine ⟨-Real.log height, ?_, ?_⟩
    · exact neg_pos.mpr (Real.log_neg hheight.1 hheight.2)
    · have hexp : Real.exp (-(-Real.log height)) = height := by
        simp [Real.exp_log hheight.1]
      rw [← ybound_exp_eq_beta, hexp]
  · rintro ⟨length, hlength, rfl⟩
    refine ⟨Real.exp (-length), ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos hlength)⟩, ?_⟩
    exact ybound_exp_eq_beta degree length

theorem complement_involutive (value : ℝ) (hvalue : value ∈ Ioo 0 1) :
    complement (complement value) = value := by
  have harg : 0 ≤ 1 - value^2 := by nlinarith [hvalue.1, hvalue.2]
  have hsquare : (complement value)^2 = 1 - value^2 := Real.sq_sqrt harg
  change Real.sqrt (1 - (complement value)^2) = value
  rw [hsquare]
  have hid : 1 - (1 - value^2) = value^2 := by ring
  rw [hid, Real.sqrt_sq hvalue.1.le]

theorem mu_positive_of_lower_dlmf (value : ℝ) (hvalue : value ∈ Ioo 0 1)
    (hlower : Real.log ((1 + Real.sqrt (complement value))^2 / value) < mu value) :
    0 < mu value := by
  have harg : 1 < (1 + Real.sqrt (complement value))^2 / value := by
    apply (lt_div_iff₀ hvalue.1).2
    nlinarith [Real.sqrt_nonneg (complement value), hvalue.2]
  exact (Real.log_pos harg).trans hlower

theorem mu_log_upper_of_upper_dlmf (value : ℝ) (hvalue : value ∈ Ioo 0 1)
    (hupper : mu value < Real.log (2 * (1 + complement value) / value)) :
    mu value < Real.log (4 / value) := by
  have hcomp := complement_mem value hvalue
  have harg : 0 < 2 * (1 + complement value) / value := by
    have hradpos := hvalue.1
    have hcomppos := hcomp.1
    positivity
  have hcompare : 2 * (1 + complement value) / value < 4 / value :=
    div_lt_div_of_pos_right (by linarith [hcomp.2]) hvalue.1
  exact hupper.trans (Real.log_lt_log harg hcompare)

theorem mu_complement_of_positive (value : ℝ) (hvalue : value ∈ Ioo 0 1)
    (hfirst : 0 < mu value) (hsecond : 0 < mu (complement value)) :
    mu value * mu (complement value) = Real.pi^2/4 := by
  have hden : ellipticK value ≠ 0 := by
    intro hzero
    have hmu : mu value = 0 := by simp [mu, hzero]
    linarith
  have hdencomp : ellipticK (complement value) ≠ 0 := by
    intro hzero
    have hmu : mu (complement value) = 0 := by simp [mu, hzero]
    linarith
  unfold mu
  rw [complement_involutive value hvalue]
  field_simp
  <;> ring

theorem prop_log_complement_lower (degree : ℕ) (hdegree : 2 ≤ degree)
    (length : ℝ) (hlength : 0 < length) :
    (1/2) * Real.log (8 * (degree : ℝ) / length) ≤
      Real.log (4 / complement (radius degree length)) := by
  have hdcast : (2 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hdpos : 0 < (degree : ℝ) := by linarith
  have hcomp := complement_mem (radius degree length) (radius_mem degree hdegree length hlength)
  have hsquare : (complement (radius degree length))^2 ≤ 2 * (length / (degree : ℝ)) := by
    rw [complement_radius_sq degree hdegree length hlength]
    simpa only [neg_mul] using general_exp_upper (2 * (length / (degree : ℝ))) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hsquare (by positivity : (0:ℝ) ≤ 8 * (degree : ℝ))
  have hid : 8 * (degree : ℝ) * (2 * (length / (degree : ℝ))) = 16 * length := by
    field_simp
    <;> ring
  rw [hid] at hscaled
  have hratio : 8 * (degree : ℝ) / length ≤ (4 / complement (radius degree length))^2 := by
    rw [div_pow]
    norm_num only [show (4 : ℝ)^2 = 16 by norm_num]
    exact (div_le_div_iff₀ hlength (sq_pos_of_pos hcomp.1)).2 hscaled
  have hlog := Real.log_le_log (div_pos (by positivity : (0:ℝ)<8 * (degree : ℝ)) hlength) hratio
  rw [Real.log_pow] at hlog
  linarith

theorem prop_delta_elementary_lower (degree : ℕ) (hdegree : 8 ≤ degree)
    (length : ℝ) (hlength : length ∈ Ioo 0 2) :
    2 * Real.log (4 * (degree : ℝ)) - 8 / (degree : ℝ) < delta degree length := by
  have hdcast : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hdpos : 0 < (degree : ℝ) := by linarith
  have hratio : 4 * (degree : ℝ) < 8 * (degree : ℝ) / length := by
    apply (lt_div_iff₀ hlength.1).2
    nlinarith [mul_pos hdpos (sub_pos.mpr hlength.2)]
  have hlog := Real.log_lt_log (by positivity : (0:ℝ) < 4 * (degree : ℝ)) hratio
  have hdivide : 4 * length / (degree : ℝ) < 8 / (degree : ℝ) :=
    div_lt_div_of_pos_right (by linarith [hlength.2]) hdpos
  unfold delta
  linarith

theorem delta_gt_two_ell (degree : ℕ) (hdegree : 8 ≤ degree)
    (length : ℝ) (hlength : length ∈ Ioo 0 2) : 2 * ell degree < delta degree length := by
  have hdcast : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hdpos : 0 < (degree : ℝ) := by linarith
  have hratio : 8 / (degree : ℝ) ≤ 1 := (div_le_one hdpos).2 hdcast
  have hlogfour : (1/2 : ℝ) < Real.log 4 := by
    rw [Real.log_four_eq]
    linarith [Real.log_two_gt_d9]
  have hidentity : Real.log (4 * (degree : ℝ)) = Real.log 4 + ell degree := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hdpos)]
    rfl
  have hdelta := prop_delta_elementary_lower degree hdegree length hlength
  rw [hidentity] at hdelta
  linarith

section DLMF
variable (hdlmf : ∀ value : ℝ, value ∈ Ioo 0 1 →
  Real.log ((1 + Real.sqrt (complement value))^2 / value) < mu value ∧
    mu value < Real.log (2 * (1 + complement value) / value))
include hdlmf

theorem cor_step1_mu_from_dlmf (degree : ℕ) (hdegree : 2 ≤ degree)
    (length : ℝ) (hlength : 0 < length) :
    Real.pi^2 / (4 * Real.log (4 / complement (radius degree length))) < mu (radius degree length) := by
  have hmem := radius_mem degree hdegree length hlength
  have hcomp := complement_mem (radius degree length) hmem
  have hfirst := mu_positive_of_lower_dlmf (radius degree length) hmem (hdlmf _ hmem).1
  have hsecond := mu_positive_of_lower_dlmf (complement (radius degree length)) hcomp (hdlmf _ hcomp).1
  exact cor_step1_mu_of degree length hsecond
    (mu_complement_of_positive (radius degree length) hmem hfirst hsecond)
    (mu_log_upper_of_upper_dlmf (complement (radius degree length)) hcomp (hdlmf _ hcomp).2)

theorem cor_step1_majorant_from_dlmf (degree : ℕ) (hdegree : 8 ≤ degree) :
    beta degree (Lchoice degree) < majorant degree := by
  exact cor_step1_beta_lt_majorant_of degree
    (cor_step1_mu_from_dlmf hdlmf degree (by omega) (Lchoice degree) (chosen_length_bounds degree hdegree).1)

theorem general_L_majorant_from_dlmf (degree : ℕ) (hdegree : 2 ≤ degree)
    (length : ℝ) (hlength : length ∈ Ioo 0 (degree : ℝ)) :
    0 < lambda degree length ∧
    Real.log (4 / complement (radius degree length)) ≤ lambda degree length / 2 ∧
    beta degree length ≤ 4 * Real.exp (length - Real.pi^2 / (2 * lambda degree length)) := by
  have hlog := log_complement_le_half_lambda degree hdegree length hlength
  have hmem := radius_mem degree hdegree length hlength.1
  have hcomp := complement_mem (radius degree length) hmem
  have hpositive : 0 < Real.log (4 / complement (radius degree length)) := by
    apply Real.log_pos
    apply (lt_div_iff₀ hcomp.1).2
    linarith [hcomp.2]
  have hdivision : Real.pi^2 / (2 * lambda degree length) ≤
      Real.pi^2 / (4 * Real.log (4 / complement (radius degree length))) := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hlog.1)
      (mul_pos (by norm_num : (0:ℝ)<4) hpositive)).2
    nlinarith [mul_nonneg (sq_nonneg Real.pi)
      (show 0 ≤ 2 * lambda degree length -
        4 * Real.log (4 / complement (radius degree length)) by linarith [hlog.2])]
  have hmu := hdivision.trans_lt (cor_step1_mu_from_dlmf hdlmf degree hdegree length hlength.1)
  refine ⟨hlog.1, hlog.2, ?_⟩
  unfold beta
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (sub_le_sub_left hmu.le length)) (by norm_num : (0:ℝ)≤4)

theorem cor_1_2_of_ybound (degree : ℕ) (hdegree : 8 ≤ degree)
    (hbound : Kd degree ≤ (yBound degree (Real.exp (-Lchoice degree)) : EReal)) :
    Kd degree < (target degree : EReal) := by
  rw [ybound_exp_eq_beta] at hbound
  have hreal : beta degree (Lchoice degree) < target degree :=
    (cor_step1_majorant_from_dlmf hdlmf degree hdegree).trans_le (majorant_le_target degree hdegree)
  exact hbound.trans_lt (by exact_mod_cast hreal)

theorem prop_mu_complement_lower_from_dlmf (degree : ℕ) (hdegree : 2 ≤ degree)
    (length : ℝ) (hlength : 0 < length) :
    Real.log (4 / complement (radius degree length)) - length / degree <
      mu (complement (radius degree length)) := by
  have hmem := radius_mem degree hdegree length hlength
  have hcomp := complement_mem (radius degree length) hmem
  have hdcast : (2 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hdpos : 0 < (degree : ℝ) := by linarith
  let root : ℝ := Real.sqrt (radius degree length)
  have hroot : 0 ≤ root := Real.sqrt_nonneg _
  have hrootsquare : root^2 = radius degree length := Real.sq_sqrt hmem.1.le
  have hrootone : root < 1 := by nlinarith [hmem.2]
  have hden : 0 < 1 + root := by linarith
  have hlowerroot : 1 - length / (2 * (degree : ℝ)) ≤ root := by
    have hexp := Real.add_one_le_exp ((-length / (degree : ℝ)) / 2)
    rw [Real.exp_half] at hexp
    change (-length / (degree : ℝ))/2 + 1 ≤ root at hexp
    convert hexp using 1 <;> ring
  have hquotient : 2 / (1 + root) - 1 ≤ length / (2 * (degree : ℝ)) := by
    have hidentity : 2 / (1 + root) - 1 = (1 - root) / (1 + root) := by
      field_simp
      <;> ring
    rw [hidentity]
    have hfirst : (1 - root) / (1 + root) ≤ 1 - root := by
      apply (div_le_iff₀ hden).2
      nlinarith
    exact hfirst.trans (by linarith)
  have hlogquotient := Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0:ℝ)<2) hden)
  rw [Real.log_div (by norm_num) (ne_of_gt hden)] at hlogquotient
  have hlower := (hdlmf _ hcomp).1
  rw [complement_involutive (radius degree length) hmem,
    Real.log_div (by positivity) (ne_of_gt hcomp.1), Real.log_pow] at hlower
  change 2 * Real.log (1 + root) - Real.log (complement (radius degree length)) <
    mu (complement (radius degree length)) at hlower
  rw [Real.log_div (by norm_num) (ne_of_gt hcomp.1), Real.log_four_eq]
  have htwice : 2 * (length / (2 * (degree : ℝ))) = length / (degree : ℝ) := by ring
  linarith

theorem prop_delta_bound_from_dlmf (degree : ℕ) (hdegree : 8 ≤ degree)
    (length : ℝ) (hlength : length ∈ Ioo 0 2) :
    0 < delta degree length ∧ delta degree length < 4 * mu (complement (radius degree length)) ∧
      mu (radius degree length) < Real.pi^2 / delta degree length := by
  have hmem := radius_mem degree (by omega) length hlength.1
  have hcomp := complement_mem (radius degree length) hmem
  have hpositive := mu_positive_of_lower_dlmf (radius degree length) hmem (hdlmf _ hmem).1
  have hpositivecomp := mu_positive_of_lower_dlmf (complement (radius degree length)) hcomp (hdlmf _ hcomp).1
  have hproduct := mu_complement_of_positive (radius degree length) hmem hpositive hpositivecomp
  have hfirst : 0 < delta degree length := by
    have hell := ell_gt_one degree hdegree
    linarith [delta_gt_two_ell degree hdegree length hlength]
  have hsecond : delta degree length < 4 * mu (complement (radius degree length)) := by
    have hmu := prop_mu_complement_lower_from_dlmf hdlmf degree (by omega) length hlength.1
    have hlog := prop_log_complement_lower degree (by omega) length hlength.1
    unfold delta
    rw [show 4 * length / (degree : ℝ) = 4 * (length / (degree : ℝ)) by ring]
    linarith
  refine ⟨hfirst, hsecond, ?_⟩
  apply (lt_div_iff₀ hfirst).2
  nlinarith [mul_pos hpositive (sub_pos.mpr hsecond)]

theorem beta_simple_lower_small_from_dlmf (degree : ℕ) (hdegree : 8 ≤ degree)
    (length : ℝ) (hlength : length ∈ Ioo 0 2) :
    4 * Real.exp (-Real.pi^2 / (2 * ell degree)) < beta degree length := by
  have hdelta := prop_delta_bound_from_dlmf hdlmf degree hdegree length hlength
  have hellpos : 0 < ell degree := by linarith [ell_gt_one degree hdegree]
  have hdivide : Real.pi^2 / delta degree length ≤ Real.pi^2 / (2 * ell degree) := by
    apply (div_le_div_iff₀ hdelta.1 (mul_pos (by norm_num : (0:ℝ)<2) hellpos)).2
    nlinarith [mul_nonneg (sq_nonneg Real.pi)
      (show 0 ≤ delta degree length - 2 * ell degree by
        linarith [delta_gt_two_ell degree hdegree length hlength])]
  have hmu := hdelta.2.2.trans_le hdivide
  unfold beta
  apply mul_lt_mul_of_pos_left _ (by norm_num : (0:ℝ)<4)
  apply Real.exp_lt_exp.mpr
  rw [neg_div]
  linarith [hlength.1]

theorem beta_gt_four_large_from_dlmf (degree : ℕ) (hdegree : 8 ≤ degree)
    (length : ℝ) (hlength : 2 ≤ length) : 4 < beta degree length := by
  have hdcast : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hdpos : 0 < (degree : ℝ) := by linarith
  have hlpos : 0 < length := by linarith
  have hmem := radius_mem degree (by omega) length hlpos
  have hupper := mu_log_upper_of_upper_dlmf (radius degree length) hmem (hdlmf _ hmem).2
  have hlogradius : Real.log (radius degree length) = -length / (degree : ℝ) := by
    unfold radius
    rw [Real.log_exp]
  rw [Real.log_div (by norm_num) (ne_of_gt hmem.1), hlogradius] at hupper
  simp only [neg_div] at hupper
  have hratio : length / (degree : ℝ) ≤ length / 8 := by
    apply (div_le_div_iff₀ hdpos (by norm_num : (0:ℝ)<8)).2
    nlinarith [mul_nonneg hlpos.le (sub_nonneg.mpr hdcast)]
  have hlogfour : Real.log 4 < (7/4 : ℝ) := by
    rw [Real.log_four_eq]
    linarith [Real.log_two_lt_d9]
  have hexponent : 0 < length - mu (radius degree length) := by linarith
  have hexp := Real.one_lt_exp_iff.mpr hexponent
  unfold beta
  nlinarith

theorem beta_uniform_simple_from_dlmf (degree : ℕ) (hdegree : 8 ≤ degree)
    (length : ℝ) (hlength : 0 < length) :
    4 * Real.exp (-Real.pi^2 / (2 * ell degree)) ≤ beta degree length := by
  by_cases hsmall : length < 2
  · exact (beta_simple_lower_small_from_dlmf hdlmf degree hdegree length ⟨hlength, hsmall⟩).le
  · have hellpos : 0 < ell degree := by linarith [ell_gt_one degree hdegree]
    have hexp : Real.exp (-Real.pi^2 / (2 * ell degree)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
    have hfour : 4 * Real.exp (-Real.pi^2 / (2 * ell degree)) ≤ 4 := by linarith
    exact hfour.trans (beta_gt_four_large_from_dlmf hdlmf degree hdegree length (by linarith)).le

end DLMF

theorem bound_set_well_defined (degree : ℕ) :
    (yBound degree '' Ioo 0 1).Nonempty ∧ BddBelow (yBound degree '' Ioo 0 1) := by
  constructor
  · exact ⟨yBound degree (1/2), mem_image_of_mem _ (by norm_num : (1/2 : ℝ) ∈ Ioo 0 1)⟩
  · refine ⟨0, ?_⟩
    rintro value ⟨height, hheight, rfl⟩
    have hpositive := hheight.1
    unfold yBound
    positivity

theorem best_bound_nonneg (degree : ℕ) : 0 ≤ bestBound degree := by
  unfold bestBound
  apply le_csInf (bound_set_well_defined degree).1
  rintro value ⟨height, hheight, rfl⟩
  have hpositive := hheight.1
  unfold yBound
  positivity

theorem best_bound_le_beta (degree : ℕ) (length : ℝ) (hlength : 0 < length) :
    bestBound degree ≤ beta degree length := by
  unfold bestBound
  apply csInf_le (bound_set_well_defined degree).2
  rw [beta_y_change]
  exact mem_image_of_mem (beta degree) hlength

theorem best_bound_lower_of_beta (degree : ℕ) (lower : ℝ)
    (hlower : ∀ length : ℝ, 0 < length → lower ≤ beta degree length) : lower ≤ bestBound degree := by
  unfold bestBound
  apply le_csInf (bound_set_well_defined degree).1
  intro value hvalue
  rw [beta_y_change] at hvalue
  rcases hvalue with ⟨length, hlength, rfl⟩
  exact hlower length hlength

theorem prop_denominator_positive (degree : ℕ) (hdegree : 8 ≤ degree) :
    Real.pi^2 < (degree : ℝ) * (ell degree)^2 ∧
    0 < 2 * ell degree - 2 * Real.pi^2 / (ell degree * degree) := by
  have hdcast : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hdpositive : 0 < (degree : ℝ) := by linarith
  have hell : (2 : ℝ) ≤ ell degree := by
    have hlow : (2 : ℝ) ≤ Real.log 8 := by linarith [finite_log_endpoints.1]
    exact hlow.trans (Real.log_le_log (by norm_num) hdcast)
  have hlpositive : 0 < ell degree := by linarith
  have hlarge : (32 : ℝ) ≤ (degree : ℝ) * (ell degree)^2 := by
    calc
      (32 : ℝ) = 8 * 4 := by norm_num
      _ ≤ (degree : ℝ) * (ell degree)^2 := by gcongr <;> nlinarith
  have hfirst : Real.pi^2 < (degree : ℝ) * (ell degree)^2 := by
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  refine ⟨hfirst, ?_⟩
  have hfrac : Real.pi^2 / (ell degree * (degree : ℝ)) < ell degree := by
    apply (div_lt_iff₀ (mul_pos hlpositive hdpositive)).2
    nlinarith
  have hid : 2 * Real.pi^2 / (ell degree * (degree : ℝ)) =
      2 * (Real.pi^2 / (ell degree * (degree : ℝ))) := by ring
  rw [hid]
  linarith

theorem prop_upper_of_uniform (degree : ℕ) (hdegree : 8 ≤ degree)
    (hbound : uniformLower degree ≤ bestBound degree) :
    gap degree ≤ 2 * Real.pi^2 / (1 - Real.pi^2 / ((degree : ℝ) * (ell degree)^2)) := by
  have hdcast : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hdpositive : 0 < (degree : ℝ) := by linarith
  have hlpositive : 0 < ell degree := by linarith [ell_gt_one degree hdegree]
  have hden := prop_denominator_positive degree hdegree
  have hsmall : 0 < 1 - Real.pi^2 / ((degree : ℝ) * (ell degree)^2) := by
    apply sub_pos.mpr
    exact (div_lt_one (mul_pos hdpositive (sq_pos_of_pos hlpositive))).2 hden.1
  have hexp := general_exp_upper
    (Real.pi^2 / (2 * ell degree - 2 * Real.pi^2 / (ell degree * degree)))
    (div_nonneg (sq_nonneg _) hden.2.le)
  unfold uniformLower at hbound
  simp only [neg_div] at hbound
  have hbase : 4 - bestBound degree ≤
      4 * (Real.pi^2 / (2 * ell degree - 2 * Real.pi^2 / (ell degree * degree))) := by
    linarith
  calc
    gap degree ≤ (4 * (Real.pi^2 / (2 * ell degree - 2 * Real.pi^2 / (ell degree * degree)))) * ell degree :=
      mul_le_mul_of_nonneg_right hbase hlpositive.le
    _ = 2 * Real.pi^2 / (1 - Real.pi^2 / ((degree : ℝ) * (ell degree)^2)) := by
      field_simp
      <;> ring

theorem prop_gap_le_two_pi_of_beta (degree : ℕ) (hdegree : 8 ≤ degree)
    (hbeta : ∀ length : ℝ, 0 < length →
      4 * Real.exp (-Real.pi^2 / (2 * ell degree)) ≤ beta degree length) :
    gap degree ≤ 2 * Real.pi^2 := by
  have hellpos : 0 < ell degree := by linarith [ell_gt_one degree hdegree]
  have hbest := best_bound_lower_of_beta degree _ hbeta
  have hexp := general_exp_upper (Real.pi^2 / (2 * ell degree)) (by positivity)
  simp only [neg_div] at hbest
  have hbase : 4 - bestBound degree ≤ 4 * (Real.pi^2 / (2 * ell degree)) := by linarith
  calc
    gap degree ≤ (4 * (Real.pi^2 / (2 * ell degree))) * ell degree :=
      mul_le_mul_of_nonneg_right hbase hellpos.le
    _ = 2 * Real.pi^2 := by field_simp <;> ring_nf <;> norm_num

theorem prop_printed_upper_of_beta (degree : ℕ) (hdegree : 8 ≤ degree)
    (hbeta : ∀ length : ℝ, 0 < length →
      4 * Real.exp (-Real.pi^2 / (2 * ell degree)) ≤ beta degree length) :
    gap degree ≤ 2 * Real.pi^2 / (1 - Real.pi^2 / ((degree : ℝ) * (ell degree)^2)) := by
  have hdcast : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hdpos : 0 < (degree : ℝ) := by linarith
  have hellpos : 0 < ell degree := by linarith [ell_gt_one degree hdegree]
  have hden := prop_denominator_positive degree hdegree
  have hsmall : 0 < 1 - Real.pi^2 / ((degree : ℝ) * (ell degree)^2) :=
    sub_pos.mpr ((div_lt_one (mul_pos hdpos (sq_pos_of_pos hellpos))).2 hden.1)
  have hleone : 1 - Real.pi^2 / ((degree : ℝ) * (ell degree)^2) ≤ 1 := by
    have hnonneg : 0 ≤ Real.pi^2 / ((degree : ℝ) * (ell degree)^2) := by positivity
    linarith
  refine (prop_gap_le_two_pi_of_beta degree hdegree hbeta).trans ?_
  apply (le_div_iff₀ hsmall).2
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hleone (by positivity : (0:ℝ)≤2*Real.pi^2)

theorem prop_3_4_upper_from_dlmf
    (hdlmf : ∀ value : ℝ, value ∈ Ioo 0 1 →
      Real.log ((1 + Real.sqrt (complement value))^2 / value) < mu value ∧
        mu value < Real.log (2 * (1 + complement value) / value))
    (degree : ℕ) (hdegree : 8 ≤ degree) :
    gap degree ≤ 2 * Real.pi^2 / (1 - Real.pi^2 / ((degree : ℝ) * (ell degree)^2)) :=
  prop_printed_upper_of_beta degree hdegree (beta_uniform_simple_from_dlmf hdlmf degree hdegree)

theorem prop_gap_le_two_pi_from_dlmf
    (hdlmf : ∀ value : ℝ, value ∈ Ioo 0 1 →
      Real.log ((1 + Real.sqrt (complement value))^2 / value) < mu value ∧
        mu value < Real.log (2 * (1 + complement value) / value))
    (degree : ℕ) (hdegree : 8 ≤ degree) : gap degree ≤ 2 * Real.pi^2 :=
  prop_gap_le_two_pi_of_beta degree hdegree (beta_uniform_simple_from_dlmf hdlmf degree hdegree)

theorem uniform_lower_le_simple (degree : ℕ) (hdegree : 8 ≤ degree) :
    uniformLower degree ≤ 4 * Real.exp (-Real.pi^2 / (2 * ell degree)) := by
  have hdcast : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hdpos : 0 < (degree : ℝ) := by linarith
  have hellpos : 0 < ell degree := by linarith [ell_gt_one degree hdegree]
  have hden := prop_denominator_positive degree hdegree
  have hdenle : 2 * ell degree - 2 * Real.pi^2 / (ell degree * degree) ≤ 2 * ell degree := by
    have hnonneg : 0 ≤ 2 * Real.pi^2 / (ell degree * degree) := by positivity
    linarith
  unfold uniformLower
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤4)
  apply Real.exp_le_exp.mpr
  apply (div_le_div_iff₀ hden.2 (mul_pos (by norm_num : (0:ℝ)<2) hellpos)).2
  nlinarith [mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.mpr hdenle)]

theorem prop_uniform_lower_from_dlmf
    (hdlmf : ∀ value : ℝ, value ∈ Ioo 0 1 →
      Real.log ((1 + Real.sqrt (complement value))^2 / value) < mu value ∧
        mu value < Real.log (2 * (1 + complement value) / value))
    (degree : ℕ) (hdegree : 8 ≤ degree) : uniformLower degree ≤ bestBound degree :=
  (uniform_lower_le_simple degree hdegree).trans
    (best_bound_lower_of_beta degree _ (beta_uniform_simple_from_dlmf hdlmf degree hdegree))

theorem reciprocal_lower_of_interval (base excess value : ℝ) (hbase : 0 < base)
    (hexcess : 0 ≤ excess) (hvalue : base ≤ value ∧ value ≤ base + excess) :
    1 / base - excess / base^2 ≤ 1 / value := by
  have hpositive : 0 < value := hbase.trans_le hvalue.1
  have hidentity : 1 / base - excess / base^2 = (base - excess) / base^2 := by
    field_simp
    <;> ring
  rw [hidentity]
  apply (div_le_div_iff₀ (sq_pos_of_pos hbase) hpositive).2
  have hfirst := mul_le_mul_of_nonneg_left hvalue.2 hbase.le
  have hsecond := mul_le_mul_of_nonneg_left hvalue.1 hexcess
  nlinarith

theorem inverse_square_length_bounds (degree : ℕ) (hdegree : 8 ≤ degree) (hell : 8 ≤ ell degree) :
    0 < 1 / (ell degree)^2 ∧ 1 / (ell degree)^2 < (degree : ℝ) := by
  have hdcast : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hpositive : 0 < ell degree := by linarith
  constructor
  · positivity
  · apply (div_lt_iff₀ (sq_pos_of_pos hpositive)).2
    have hlarge : (64 : ℝ) ≤ (ell degree)^2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hdcast) (sub_nonneg.mpr hlarge)]

theorem lambda_inverse_square_identity (degree : ℕ) (hdegree : 8 ≤ degree) (hell : 8 ≤ ell degree) :
    lambda degree (1 / (ell degree)^2) = ell degree + Real.log 8 + 2 * Real.log (ell degree) -
      Real.log (1 - (1 / (ell degree)^2) / degree) := by
  have hlength := inverse_square_length_bounds degree hdegree hell
  have hdcast : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hdpos : 0 < (degree : ℝ) := by linarith
  have hlpos : 0 < ell degree := by linarith
  have hlast : 0 < 1 - (1 / (ell degree)^2) / (degree : ℝ) :=
    sub_pos.mpr ((div_lt_one hdpos).2 hlength.2)
  have hidentity : 8 * (degree : ℝ) / ((1 / (ell degree)^2) * (1 - (1 / (ell degree)^2) / degree)) =
      (degree : ℝ) * (8 * (ell degree)^2) / (1 - (1 / (ell degree)^2) / degree) := by
    field_simp
    <;> ring
  unfold lambda
  rw [hidentity, Real.log_div (by positivity) (ne_of_gt hlast),
    Real.log_mul (ne_of_gt hdpos) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  simp only [ell, Nat.cast_ofNat]
  ring

theorem lambda_inverse_square_bounds (degree : ℕ) (hdegree : 8 ≤ degree) (hell : 8 ≤ ell degree) :
    ell degree ≤ lambda degree (1 / (ell degree)^2) ∧
      lambda degree (1 / (ell degree)^2) ≤ ell degree + 4 * Real.log (ell degree) := by
  have hdcast : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hdpos : 0 < (degree : ℝ) := by linarith
  have hlpos : 0 < ell degree := by linarith
  have hlength := inverse_square_length_bounds degree hdegree hell
  have hleone : 1 / (ell degree)^2 ≤ 1 :=
    (div_le_one (sq_pos_of_pos hlpos)).2 (by nlinarith)
  have hratio : (1 / (ell degree)^2) / (degree : ℝ) ≤ (1/8 : ℝ) := by
    apply (div_le_div_iff₀ hdpos (by norm_num : (0:ℝ)<8)).2
    linarith
  have hratio_nonneg : 0 ≤ (1 / (ell degree)^2) / (degree : ℝ) := by positivity
  have hcorrection := log_one_sub_half ((1 / (ell degree)^2) / (degree : ℝ))
    ⟨hratio_nonneg, by linarith⟩
  have hlog_nonpos : Real.log (1 - (1 / (ell degree)^2) / (degree : ℝ)) ≤ 0 :=
    Real.log_nonpos (by linarith) (by linarith)
  have hlogorder : Real.log 8 ≤ Real.log (ell degree) := Real.log_le_log (by norm_num) hell
  have hlogone : (1 : ℝ) ≤ Real.log (ell degree) := by linarith [finite_log_endpoints.1]
  have hlogeight : (0 : ℝ) ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  rw [lambda_inverse_square_identity degree hdegree hell]
  constructor <;> linarith

/-- Pure real algebra behind the one-sided logarithmic error estimate. -/
theorem lower_error_algebra (base logBase denominator bound : ℝ)
    (hbase : 8 ≤ base) (hlog : 1 ≤ logBase)
    (hdenominator : base ≤ denominator ∧ denominator ≤ base + 4 * logBase)
    (hbound : bound ≤ 4 * Real.exp (1 / base^2 - Real.pi^2 / (2 * denominator))) :
    2 * Real.pi^2 - (4 + 8 * Real.pi^2 + Real.pi^4) * (logBase / base) ≤ (4 - bound) * base := by
  have hbpos : 0 < base := by linarith
  have hdpos : 0 < denominator := hbpos.trans_le hdenominator.1
  let quotient : ℝ := Real.pi^2 / (2 * base)
  let exponent : ℝ := 1 / base^2 - Real.pi^2 / (2 * denominator)
  have hqnonneg : 0 ≤ quotient := by dsimp [quotient]; positivity
  have hqone : quotient ≤ 1 := by
    dsimp [quotient]
    apply (div_le_one (by positivity : (0:ℝ)<2*base)).2
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hterm : 0 ≤ Real.pi^2 / (2 * denominator) := by positivity
  have htermupper : Real.pi^2 / (2 * denominator) ≤ quotient := by
    dsimp [quotient]
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<2*denominator) (by positivity : (0:ℝ)<2*base)).2
    nlinarith [mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.mpr hdenominator.1)]
  have hsmall : 1 / base^2 ≤ quotient := by
    dsimp [quotient]
    apply (div_le_div_iff₀ (sq_pos_of_pos hbpos) (by positivity : (0:ℝ)<2*base)).2
    have hsquare : base ≤ base^2 := by nlinarith
    have hpi : (2 : ℝ) ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three, Real.pi_pos]
    nlinarith [mul_nonneg (sq_nonneg base) (sub_nonneg.mpr hpi)]
  have hexponentlo : -quotient ≤ exponent := by
    dsimp [exponent]
    have hnonneg : (0:ℝ) ≤ 1 / base^2 := by positivity
    linarith
  have hexponenthi : exponent ≤ quotient := by dsimp [exponent]; linarith
  have habs : |exponent| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hsquare : exponent^2 ≤ quotient^2 := by
    nlinarith [mul_nonneg (show 0 ≤ quotient - exponent by linarith)
      (show 0 ≤ quotient + exponent by linarith)]
  have hexp := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le habs)).2
  change bound ≤ 4 * Real.exp exponent at hbound
  have hpoly : bound ≤ 4 + 4 * exponent + 4 * exponent^2 := by linarith
  have hreciprocal := reciprocal_lower_of_interval base (4 * logBase) denominator hbpos
    (by linarith) hdenominator
  have hquotientlower : quotient - 2 * Real.pi^2 * logBase / base^2 ≤
      Real.pi^2 / (2 * denominator) := by
    have hscaled := mul_le_mul_of_nonneg_left hreciprocal (by positivity : (0:ℝ)≤Real.pi^2/2)
    dsimp [quotient]
    convert hscaled using 1 <;> ring
  have hminus : quotient - (1 + 2 * Real.pi^2 * logBase) / base^2 ≤ -exponent := by
    dsimp [exponent]
    have hid : quotient - (1 + 2 * Real.pi^2 * logBase) / base^2 =
        quotient - 2 * Real.pi^2 * logBase / base^2 - 1 / base^2 := by ring
    rw [hid]
    linarith
  have hrough : 4 * quotient - 4 * (1 + 2 * Real.pi^2 * logBase) / base^2 -
      4 * quotient^2 ≤ 4 - bound := by
    rw [show 4 * (1 + 2 * Real.pi^2 * logBase) / base^2 =
      4 * ((1 + 2 * Real.pi^2 * logBase) / base^2) by ring]
    linarith
  have hid : 4 * quotient - 4 * (1 + 2 * Real.pi^2 * logBase) / base^2 -
      4 * quotient^2 = 2 * Real.pi^2 / base - (4 + 8 * Real.pi^2 * logBase + Real.pi^4) / base^2 := by
    dsimp [quotient]
    field_simp
    <;> ring
  rw [hid] at hrough
  have hscaled := mul_le_mul_of_nonneg_right hrough hbpos.le
  have hscaledid : (2 * Real.pi^2 / base - (4 + 8 * Real.pi^2 * logBase + Real.pi^4) / base^2) * base =
      2 * Real.pi^2 - (4 + 8 * Real.pi^2 * logBase + Real.pi^4) / base := by
    field_simp
    <;> ring
  rw [hscaledid] at hscaled
  have herror : (4 + 8 * Real.pi^2 * logBase + Real.pi^4) / base ≤
      (4 + 8 * Real.pi^2 + Real.pi^4) * (logBase / base) := by
    rw [show (4 + 8 * Real.pi^2 + Real.pi^4) * (logBase / base) =
      ((4 + 8 * Real.pi^2 + Real.pi^4) * logBase) / base by ring]
    apply (div_le_div_iff_of_pos_right hbpos).2
    nlinarith [mul_nonneg (show 0 ≤ 4 + Real.pi^4 by positivity) (sub_nonneg.mpr hlog)]
  linarith

section DLMFQuantitative
variable (hdlmf : ∀ value : ℝ, value ∈ Ioo 0 1 →
  Real.log ((1 + Real.sqrt (complement value))^2 / value) < mu value ∧
    mu value < Real.log (2 * (1 + complement value) / value))
include hdlmf

theorem prop_lower_error_pointwise (degree : ℕ) (hdegree : 8 ≤ degree) (hell : 8 ≤ ell degree) :
    2 * Real.pi^2 - (4 + 8 * Real.pi^2 + Real.pi^4) * (Real.log (ell degree) / ell degree) ≤ gap degree := by
  have hlength := inverse_square_length_bounds degree hdegree hell
  have hgeneral := general_L_majorant_from_dlmf hdlmf degree (by omega) (1 / (ell degree)^2) hlength
  have hbest := (best_bound_le_beta degree (1 / (ell degree)^2) hlength.1).trans hgeneral.2.2
  have hlambda := lambda_inverse_square_bounds degree hdegree hell
  have hlog : 1 ≤ Real.log (ell degree) := by
    have horder := Real.log_le_log (by norm_num : (0:ℝ)<8) hell
    linarith [finite_log_endpoints.1]
  exact lower_error_algebra (ell degree) (Real.log (ell degree))
    (lambda degree (1 / (ell degree)^2)) (bestBound degree) hell hlog hlambda hbest

theorem prop_3_4_lower_error_from_dlmf : ∃ constant ≥ (0 : ℝ), ∀ᶠ degree : ℕ in atTop,
    2 * Real.pi^2 - constant * (Real.log (ell degree) / ell degree) ≤ gap degree := by
  refine ⟨4 + 8 * Real.pi^2 + Real.pi^4, by positivity, ?_⟩
  have htop : Tendsto ell atTop atTop := by
    exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (8 : ℕ), htop.eventually (eventually_ge_atTop (8 : ℝ))]
    with degree hdegree hell
  exact prop_lower_error_pointwise hdlmf degree hdegree hell

theorem prop_3_4_limit_from_dlmf : Tendsto gap atTop (𝓝 (2 * Real.pi^2)) := by
  rcases prop_3_4_lower_error_from_dlmf hdlmf with ⟨constant, hconstant, hlower⟩
  have htop : Tendsto ell atTop atTop := by
    exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun degree : ℕ => Real.log (ell degree) / ell degree) atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp htop
  have hlowerlimit : Tendsto (fun degree : ℕ =>
      2 * Real.pi^2 - constant * (Real.log (ell degree) / ell degree)) atTop (𝓝 (2 * Real.pi^2)) := by
    simpa only [mul_zero, sub_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => 2 * Real.pi^2) atTop (𝓝 (2 * Real.pi^2))).sub
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => constant) atTop (𝓝 constant)).mul hratio))
  have hupper : ∀ᶠ degree : ℕ in atTop, gap degree ≤ 2 * Real.pi^2 := by
    filter_upwards [eventually_ge_atTop (8 : ℕ)] with degree hdegree
    exact prop_gap_le_two_pi_from_dlmf hdlmf degree hdegree
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowerlimit tendsto_const_nhds hlower hupper

end DLMFQuantitative

theorem log_six_hundred_lt_seven : Real.log (600 : ℝ) < 7 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).2
  exact lt_of_lt_of_le (by norm_num : (600 : ℝ) < (2718/1000 : ℝ)^7)
    (exp_integer_lower 7)

theorem small_degree_lambda (degree : ℕ) (hdegree : 2 ≤ degree) (hupper : degree ≤ 7) :
    lambda degree (1/10) < 7 := by
  have hdegrees : (2 : ℝ) ≤ degree ∧ (degree : ℝ) ≤ 7 := by
    constructor <;> exact_mod_cast (by omega : _)
  exact (lambda_le_log_of_interval degree (1/10) 2 7 (1/10) (1/10) 600 hdegree
    (by norm_num) hdegrees (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).trans_lt log_six_hundred_lt_seven

theorem four_five_sixths_bounds :
    (3 : ℝ) < (4 : ℝ)^(5/6 : ℝ) ∧ (4 : ℝ)^(5/6 : ℝ) < 39/10 := by
  have hlogfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ)^2 by norm_num, Real.log_pow]; norm_num
  have hlogthirteen : (3/13 : ℝ) ≤ Real.log (13/10 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 13/10)
    norm_num at h ⊢
    exact h
  have hlogthirtynine : Real.log (39/10 : ℝ) = Real.log 3 + Real.log (13/10 : ℝ) := by
    rw [show (39/10 : ℝ) = 3 * (13/10) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4)]
  constructor
  · rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3), Real.exp_lt_exp, hlogfour]
    linarith [Real.log_three_lt_d9, Real.log_two_gt_d9]
  · rw [← Real.exp_log (by norm_num : (0 : ℝ) < 39/10), Real.exp_lt_exp,
      hlogfour, hlogthirtynine]
    linarith [Real.log_three_gt_d9, Real.log_two_lt_d9]

section DLMFSmall
variable (hdlmf : ∀ value : ℝ, value ∈ Ioo 0 1 →
  Real.log ((1 + Real.sqrt (complement value))^2 / value) < mu value ∧
    mu value < Real.log (2 * (1 + complement value) / value))
include hdlmf

theorem small_degree_beta_from_dlmf (degree : ℕ) (hdegree : 2 ≤ degree) (hupper : degree ≤ 7) :
    beta degree (1/10) < 3 := by
  have hdreal : (2 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hgeneral := general_L_majorant_from_dlmf hdlmf degree hdegree (1/10)
    (by constructor <;> linarith : (1/10 : ℝ) ∈ Ioo 0 (degree : ℝ))
  have hlambda := small_degree_lambda degree hdegree hupper
  have hlambdapos := hgeneral.1
  have hpi : (314/100 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  have hquotient : (64/100 : ℝ) ≤ Real.pi^2 / (2 * lambda degree (1/10)) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith [Real.pi_pos]
  calc
    beta degree (1/10) ≤ 4 * Real.exp ((1/10 : ℝ) - Real.pi^2 / (2 * lambda degree (1/10))) :=
      hgeneral.2.2
    _ ≤ 4 * Real.exp (-(54/100 : ℝ)) := by gcongr; linarith
    _ < 47/20 := exp_negative_finite_bounds.2.2
    _ < 3 := by norm_num

theorem small_bound_below_39_of_ybound (degree : ℕ) (hdegree : 2 ≤ degree) (hupper : degree ≤ 7)
    (hbound : Kd degree ≤ (yBound degree (Real.exp (-(1/10 : ℝ))) : EReal)) :
    Kd degree ≤ ((Real.rpow 4 (5/6) : ℝ) : EReal) ∧ (4 : ℝ)^(5/6 : ℝ) < 39/10 := by
  rw [ybound_exp_eq_beta] at hbound
  refine ⟨hbound.trans ?_, four_five_sixths_bounds.2⟩
  exact_mod_cast ((small_degree_beta_from_dlmf hdlmf degree hdegree hupper).trans
    four_five_sixths_bounds.1).le

end DLMFSmall

theorem exp_forty_gt_degree_threshold : (2 * 10^17 : ℝ) < Real.exp 40 := by
  exact lt_of_lt_of_le (by norm_num : (2 * 10^17 : ℝ) < (2718/1000 : ℝ)^40)
    (exp_integer_lower 40)

theorem bounds_below_39_of_corollary (degree : ℕ) (hdegree : 8 ≤ degree)
    (hupper : (degree : ℝ) ≤ Real.exp 40) (hbound : Kd degree < (target degree : EReal)) :
    Kd degree < ((39/10 : ℝ) : EReal) := by
  have hdreal : (0 : ℝ) < degree := by exact_mod_cast (by omega : 0 < degree)
  have hell : ell degree ≤ 40 := by
    exact (Real.log_le_iff_le_exp hdreal).2 hupper
  have hpositive : 0 < ell degree := lt_trans (by norm_num) (ell_gt_one degree hdegree)
  have hdivide : (1/10 : ℝ) ≤ 4 / ell degree := by
    apply (le_div_iff₀ hpositive).2
    linarith
  have htarget : target degree ≤ (39/10 : ℝ) := by unfold target; linarith
  exact hbound.trans_le (by exact_mod_cast htarget)

theorem s_le_kd (degree : ℕ) (poly : ℂ[X]) (hpoly : IsPd degree poly) :
    (S poly : EReal) ≤ Kd degree := by
  exact le_iSup_of_le ⟨poly, hpoly⟩ le_rfl

theorem degree_example_39_of_bounds
    (hsmall : ∀ degree : ℕ, 2 ≤ degree → degree ≤ 7 → Kd degree < ((39/10 : ℝ) : EReal))
    (hcorollary : ∀ degree : ℕ, 8 ≤ degree → Kd degree < (target degree : EReal))
    (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (hlarge : 39/10 ≤ S poly) : 2 * 10^17 < degree := by
  by_contra hnot
  have hupper : degree ≤ 2 * 10^17 := by omega
  have hrealupper : (degree : ℝ) ≤ 2 * 10^17 := by exact_mod_cast hupper
  have hKd : Kd degree < ((39/10 : ℝ) : EReal) := by
    by_cases hsmallDegree : degree ≤ 7
    · exact hsmall degree hdegree hsmallDegree
    · exact bounds_below_39_of_corollary degree (by omega)
        (hrealupper.trans exp_forty_gt_degree_threshold.le) (hcorollary degree (by omega))
  have hpolybound : S poly < (39/10 : ℝ) := by
    exact_mod_cast ((s_le_kd degree poly hpoly).trans_lt hKd)
  linarith

end SmaleRate.Proofs



