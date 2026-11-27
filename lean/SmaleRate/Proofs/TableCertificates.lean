/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.Elementary

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Polynomial
open scoped Topology

theorem exp_small_bounds (value : ℝ) (hvalue : |value| ≤ 1) :
    (∑ index ∈ Finset.range 20, value^index / (index.factorial : ℝ)) -
      |value|^20 * (21/(2432902008176640000*20)) ≤ Real.exp value ∧
    Real.exp value ≤ (∑ index ∈ Finset.range 20, value^index / (index.factorial : ℝ)) +
      |value|^20 * (21/(2432902008176640000*20)) := by
  have h := Real.exp_bound (x := value) (n := 20) hvalue (by norm_num)
  norm_num only [Nat.factorial] at h
  exact ⟨by linarith [(abs_sub_le_iff.mp h).2], by linarith [(abs_sub_le_iff.mp h).1]⟩

theorem exp_bounds_from_eighth (value lower upper : ℝ) (hlower : 0 ≤ lower)
    (hbound : lower ≤ Real.exp (value/8) ∧ Real.exp (value/8) ≤ upper) :
    lower^8 ≤ Real.exp value ∧ Real.exp value ≤ upper^8 := by
  have hpower : (Real.exp (value/8))^8 = Real.exp value := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  constructor
  · rw [← hpower]; gcongr; exact hbound.1
  · rw [← hpower]; gcongr; exact hbound.2

theorem table_log_interval (degree : ℕ) (lower upper : ℝ) (hlower : 0 < lower)
    (hdegree : 0 < (degree : ℝ))
    (hbound : Real.exp lower ≤ degree ∧ (degree : ℝ) ≤ Real.exp upper) :
    lower ≤ ell degree ∧ ell degree ≤ upper := by
  exact ⟨(Real.le_log_iff_exp_le hdegree).2 hbound.1,
    (Real.log_le_iff_le_exp hdegree).2 hbound.2⟩

theorem table_length_interval (degree : ℕ) (lower upper : ℝ) (hlower : 0 < lower)
    (hbound : lower ≤ ell degree ∧ ell degree ≤ upper) :
    1/(4*upper) ≤ Lchoice degree ∧ Lchoice degree ≤ 1/(4*lower) := by
  have hell : 0 < ell degree := hlower.trans_le hbound.1
  have hupper : 0 < upper := hell.trans_le hbound.2
  unfold Lchoice
  constructor <;> apply one_div_le_one_div_of_le (by positivity) <;> linarith [hbound.1, hbound.2]

theorem table_complement_interval (degree : ℕ) (hdegree : 8 ≤ degree)
    (ellLower ellUpper zLower zUpper compLower compUpper : ℝ)
    (hellLower : 0 < ellLower) (hell : ellLower ≤ ell degree ∧ ell degree ≤ ellUpper)
    (hzLower : zLower ≤ -2/(4*ellLower*(degree : ℝ)))
    (hzUpper : -2/(4*ellUpper*(degree : ℝ)) ≤ zUpper)
    (hexpLower : 1-compUpper ≤ Real.exp zLower)
    (hexpUpper : Real.exp zUpper ≤ 1-compLower) :
    compLower ≤ (complement (radius degree (Lchoice degree)))^2 ∧
      (complement (radius degree (Lchoice degree)))^2 ≤ compUpper := by
  have hd : 0 < (degree : ℝ) := by exact_mod_cast (by omega : 0 < degree)
  have hlength := table_length_interval degree ellLower ellUpper hellLower hell
  have hchosen := chosen_length_bounds degree hdegree
  have hidentity := complement_radius_sq degree (by omega) (Lchoice degree) hchosen.1
  rw [show -2*(Lchoice degree/(degree : ℝ)) = -2*Lchoice degree/(degree : ℝ) by ring] at hidentity
  have hz : zLower ≤ -2*Lchoice degree/(degree : ℝ) ∧
      -2*Lchoice degree/(degree : ℝ) ≤ zUpper := by
    constructor
    · apply hzLower.trans
      calc
        -2/(4*ellLower*(degree : ℝ)) = -2*(1/(4*ellLower))/(degree : ℝ) := by ring
        _ ≤ -2*Lchoice degree/(degree : ℝ) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonpos_left hlength.2 (by norm_num)) hd.le
    · apply le_trans _ hzUpper
      calc
        -2*Lchoice degree/(degree : ℝ) ≤ -2*(1/(4*ellUpper))/(degree : ℝ) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonpos_left hlength.1 (by norm_num)) hd.le
        _ = -2/(4*ellUpper*(degree : ℝ)) := by ring
  rw [hidentity]
  constructor
  · linarith [(Real.exp_le_exp.mpr hz.2).trans hexpUpper]
  · linarith [hexpLower.trans (Real.exp_le_exp.mpr hz.1)]

theorem table_denominator_interval (degree : ℕ) (hdegree : 8 ≤ degree)
    (compLower compUpper logLower logUpper : ℝ) (hcompLower : 0 < compLower)
    (hcomp : compLower ≤ (complement (radius degree (Lchoice degree)))^2 ∧
      (complement (radius degree (Lchoice degree)))^2 ≤ compUpper)
    (hlogLower : Real.exp logLower ≤ compLower)
    (hlogUpper : compUpper ≤ Real.exp logUpper) :
    4*((13862943606/10000000000 : ℝ)-logUpper/2) ≤
      4*Real.log (4/complement (radius degree (Lchoice degree))) ∧
    4*Real.log (4/complement (radius degree (Lchoice degree))) ≤
      4*((13862943616/10000000000 : ℝ)-logLower/2) := by
  have hchosen := chosen_length_bounds degree hdegree
  have hmem := complement_mem (radius degree (Lchoice degree))
    (radius_mem degree (by omega) (Lchoice degree) hchosen.1)
  have hpositive := hmem.1
  have hlog : logLower ≤ Real.log ((complement (radius degree (Lchoice degree)))^2) ∧
      Real.log ((complement (radius degree (Lchoice degree)))^2) ≤ logUpper := by
    refine ⟨(Real.le_log_iff_exp_le (by positivity)).2 (hlogLower.trans hcomp.1),
      (Real.log_le_iff_le_exp (by positivity)).2 (hcomp.2.trans hlogUpper)⟩
  have hlogfour : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ)^2 by norm_num, Real.log_pow]; norm_num
  rw [Real.log_div (by norm_num) (ne_of_gt hmem.1), hlogfour]
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, hlog.1, hlog.2]

theorem table_majorant_exponent_interval (degree : ℕ)
    (ellLower ellUpper denLower denUpper uLower uUpper : ℝ)
    (hellLower : 0 < ellLower) (hell : ellLower ≤ ell degree ∧ ell degree ≤ ellUpper)
    (hdenLower : 0 < denLower)
    (hden : denLower ≤ 4*Real.log (4/complement (radius degree (Lchoice degree))) ∧
      4*Real.log (4/complement (radius degree (Lchoice degree))) ≤ denUpper)
    (huLower : uLower ≤ 1/(4*ellUpper) - (314159265358979323847/100000000000000000000 : ℝ)^2/denLower)
    (huUpper : 1/(4*ellLower) - (314159265358979323846/100000000000000000000 : ℝ)^2/denUpper ≤ uUpper) :
    uLower ≤ Lchoice degree - Real.pi^2/(4*Real.log (4/complement (radius degree (Lchoice degree)))) ∧
    Lchoice degree - Real.pi^2/(4*Real.log (4/complement (radius degree (Lchoice degree)))) ≤ uUpper := by
  have hlength := table_length_interval degree ellLower ellUpper hellLower hell
  have hdenpos : 0 < 4*Real.log (4/complement (radius degree (Lchoice degree))) :=
    hdenLower.trans_le hden.1
  have hupperpos : 0 < denUpper := hdenpos.trans_le hden.2
  have hpiLower : (314159265358979323846/100000000000000000000 : ℝ)^2 ≤ Real.pi^2 := by
    nlinarith [Real.pi_gt_d20, Real.pi_pos]
  have hpiUpper : Real.pi^2 ≤ (314159265358979323847/100000000000000000000 : ℝ)^2 := by
    nlinarith [Real.pi_lt_d20, Real.pi_pos]
  have hquotientLower : (314159265358979323846/100000000000000000000 : ℝ)^2/denUpper ≤
      Real.pi^2/(4*Real.log (4/complement (radius degree (Lchoice degree)))) := by
    exact div_le_div₀ (by positivity) hpiLower hdenpos hden.2
  have hquotientUpper : Real.pi^2/(4*Real.log (4/complement (radius degree (Lchoice degree)))) ≤
      (314159265358979323847/100000000000000000000 : ℝ)^2/denLower := by
    exact div_le_div₀ (sq_nonneg _) hpiUpper hdenLower hden.1
  constructor <;> linarith [hlength.1, hlength.2]

theorem table_majorant_bounds (degree : ℕ) (uLower uUpper lower upper : ℝ)
    (hu : uLower ≤ Lchoice degree - Real.pi^2/(4*Real.log (4/complement (radius degree (Lchoice degree)))) ∧
      Lchoice degree - Real.pi^2/(4*Real.log (4/complement (radius degree (Lchoice degree)))) ≤ uUpper)
    (hexpLower : lower/4 < Real.exp uLower) (hexpUpper : Real.exp uUpper ≤ upper/4) :
    lower < majorant degree ∧ majorant degree ≤ upper := by
  unfold majorant
  constructor
  · linarith [(Real.exp_le_exp.mpr hu.1)]
  · linarith [(Real.exp_le_exp.mpr hu.2)]

theorem table_target_bounds (degree : ℕ) (ellLower ellUpper lower upper : ℝ)
    (hellLower : 0 < ellLower) (hell : ellLower ≤ ell degree ∧ ell degree ≤ ellUpper)
    (hLower : lower ≤ 4-4/ellLower) (hUpper : 4-4/ellUpper < upper) :
    lower ≤ target degree ∧ target degree < upper := by
  have hellpos : 0 < ell degree := hellLower.trans_le hell.1
  have heUpper : 0 < ellUpper := hellpos.trans_le hell.2
  have hdivLower : 4/ell degree ≤ 4/ellLower :=
    div_le_div_of_nonneg_left (by norm_num) hellLower hell.1
  have hdivUpper : 4/ellUpper ≤ 4/ell degree :=
    div_le_div_of_nonneg_left (by norm_num) hellpos hell.2
  unfold target
  constructor <;> linarith

-- Verified Table 3 rational bounds.
-- Version 0.10. Every literal still requires a kernel proof.
-- Degree 8
def d8_ell_low : ℝ := (2079441541679/1000000000000 : ℝ)
def d8_ell_high : ℝ := (25993019271/12500000000 : ℝ)
def d8_z_low : ℝ := (-15028073343/500000000000 : ℝ)
def d8_z_high : ℝ := (-6011229337/200000000000 : ℝ)
def d8_comp_low : ℝ := (29608952221/1000000000000 : ℝ)
def d8_comp_high : ℝ := (29608952223/1000000000000 : ℝ)
def d8_log_low : ℝ := (-87991963087/25000000000 : ℝ)
def d8_log_high : ℝ := (-3519678523411/1000000000000 : ℝ)
def d8_u_low : ℝ := (-664039973029/1000000000000 : ℝ)
def d8_u_high : ℝ := (-66403997277/100000000000 : ℝ)
theorem d8_exp_ell_low :
    (1296839554650874157/1000000000000000000 : ℝ) ≤ Real.exp ((2079441541679/1000000000000 : ℝ)/8) ∧
    Real.exp ((2079441541679/1000000000000 : ℝ)/8) ≤ (648419777325437079/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((2079441541679/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d8_exp_ell_high :
    (648419777325518131/500000000000000000 : ℝ) ≤ Real.exp ((25993019271/12500000000 : ℝ)/8) ∧
    Real.exp ((25993019271/12500000000 : ℝ)/8) ≤ (1296839554651036263/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((25993019271/12500000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d8_exp_z_low :
    (996250030427430363/1000000000000000000 : ℝ) ≤ Real.exp ((-15028073343/500000000000 : ℝ)/8) ∧
    Real.exp ((-15028073343/500000000000 : ℝ)/8) ≤ (249062507606857591/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-15028073343/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d8_exp_z_high :
    (498125015213777447/500000000000000000 : ℝ) ≤ Real.exp ((-6011229337/200000000000 : ℝ)/8) ∧
    Real.exp ((-6011229337/200000000000 : ℝ)/8) ≤ (199250006085510979/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-6011229337/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d8_exp_log_low :
    (161015575481642119/250000000000000000 : ℝ) ≤ Real.exp ((-87991963087/25000000000 : ℝ)/8) ∧
    Real.exp ((-87991963087/25000000000 : ℝ)/8) ≤ (644062301926568477/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-87991963087/25000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d8_exp_log_high :
    (644062301932123513/1000000000000000000 : ℝ) ≤ Real.exp ((-3519678523411/1000000000000 : ℝ)/8) ∧
    Real.exp ((-3519678523411/1000000000000 : ℝ)/8) ≤ (322031150966061757/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3519678523411/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d8_exp_u_low :
    (184069309715745263/200000000000000000 : ℝ) ≤ Real.exp ((-664039973029/1000000000000 : ℝ)/8) ∧
    Real.exp ((-664039973029/1000000000000 : ℝ)/8) ≤ (230086637144681579/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-664039973029/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d8_exp_u_high :
    (184069309721704507/200000000000000000 : ℝ) ≤ Real.exp ((-66403997277/100000000000 : ℝ)/8) ∧
    Real.exp ((-66403997277/100000000000 : ℝ)/8) ≤ (115043318576065317/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66403997277/100000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith

theorem table3_rounding_eight :
    ((205906/100000 : ℝ) < majorant 8 ∧ majorant 8 ≤ 205907/100000) ∧
      ((207640/100000 : ℝ) ≤ target 8 ∧ target 8 < 207641/100000) := by
  have helo := exp_bounds_from_eighth _ _ _ (by norm_num) d8_exp_ell_low
  have hehi := exp_bounds_from_eighth _ _ _ (by norm_num) d8_exp_ell_high
  have hzlo := exp_bounds_from_eighth _ _ _ (by norm_num) d8_exp_z_low
  have hzhi := exp_bounds_from_eighth _ _ _ (by norm_num) d8_exp_z_high
  have hloglo := exp_bounds_from_eighth _ _ _ (by norm_num) d8_exp_log_low
  have hloghi := exp_bounds_from_eighth _ _ _ (by norm_num) d8_exp_log_high
  have hulow := exp_bounds_from_eighth _ _ _ (by norm_num) d8_exp_u_low
  have huhi := exp_bounds_from_eighth _ _ _ (by norm_num) d8_exp_u_high
  have hell := table_log_interval 8 d8_ell_low d8_ell_high (by norm_num [d8_ell_low]) (by norm_num)
    ⟨helo.2.trans (by norm_num), le_trans (by norm_num) hehi.1⟩
  have hcomp := table_complement_interval 8 (by norm_num) d8_ell_low d8_ell_high
    d8_z_low d8_z_high d8_comp_low d8_comp_high (by norm_num [d8_ell_low]) hell
    (by norm_num [d8_z_low, d8_ell_low]) (by norm_num [d8_z_high, d8_ell_high])
    (le_trans (by norm_num [d8_comp_high]) hzlo.1)
    (hzhi.2.trans (by norm_num [d8_comp_low]))
  have hden := table_denominator_interval 8 (by norm_num)
    d8_comp_low d8_comp_high d8_log_low d8_log_high (by norm_num [d8_comp_low]) hcomp
    (hloglo.2.trans (by norm_num [d8_comp_low]))
    (le_trans (by norm_num [d8_comp_high]) hloghi.1)
  let denLower : ℝ := 4*((13862943606/10000000000 : ℝ)-d8_log_high/2)
  let denUpper : ℝ := 4*((13862943616/10000000000 : ℝ)-d8_log_low/2)
  have hu := table_majorant_exponent_interval 8 d8_ell_low d8_ell_high denLower denUpper
    d8_u_low d8_u_high (by norm_num [d8_ell_low]) hell
    (by norm_num [denLower, d8_log_high]) hden
    (by norm_num [d8_u_low, d8_ell_high, denLower, d8_log_high])
    (by norm_num [d8_u_high, d8_ell_low, denUpper, d8_log_low])
  constructor
  · exact table_majorant_bounds 8 d8_u_low d8_u_high (205906/100000) (205907/100000) hu
      (lt_of_lt_of_le (by norm_num) hulow.1) (huhi.2.trans (by norm_num))
  · exact table_target_bounds 8 d8_ell_low d8_ell_high (207640/100000) (207641/100000)
      (by norm_num [d8_ell_low]) hell (by norm_num [d8_ell_low]) (by norm_num [d8_ell_high])

-- Degree 9
def d9_ell_low : ℝ := (274653072167/125000000000 : ℝ)
def d9_ell_high : ℝ := (2197224577337/1000000000000 : ℝ)
def d9_z_low : ℝ := (-12642211481/500000000000 : ℝ)
def d9_z_high : ℝ := (-25284422961/1000000000000 : ℝ)
def d9_comp_low : ℝ := (12483724529/500000000000 : ℝ)
def d9_comp_high : ℝ := (1248372453/50000000000 : ℝ)
def d9_log_low : ℝ := (-1845091170091/500000000000 : ℝ)
def d9_log_high : ℝ := (-3690182340101/1000000000000 : ℝ)
def d9_u_low : ℝ := (-649793825919/1000000000000 : ℝ)
def d9_u_high : ℝ := (-81224228209/125000000000 : ℝ)
theorem d9_exp_ell_low :
    (131607401295245637/100000000000000000 : ℝ) ≤ Real.exp ((274653072167/125000000000 : ℝ)/8) ∧
    Real.exp ((274653072167/125000000000 : ℝ)/8) ≤ (1316074012952456371/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((274653072167/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d9_exp_ell_high :
    (1316074012952620879/1000000000000000000 : ℝ) ≤ Real.exp ((2197224577337/1000000000000 : ℝ)/8) ∧
    Real.exp ((2197224577337/1000000000000 : ℝ)/8) ≤ (16450925161907761/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((2197224577337/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d9_exp_z_low :
    (996844436419284259/1000000000000000000 : ℝ) ≤ Real.exp ((-12642211481/500000000000 : ℝ)/8) ∧
    Real.exp ((-12642211481/500000000000 : ℝ)/8) ≤ (49842221820964213/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-12642211481/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d9_exp_z_high :
    (199368887283881773/200000000000000000 : ℝ) ≤ Real.exp ((-25284422961/1000000000000 : ℝ)/8) ∧
    Real.exp ((-25284422961/1000000000000 : ℝ)/8) ≤ (498422218209704433/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-25284422961/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d9_exp_log_low :
    (630480663526323417/1000000000000000000 : ℝ) ≤ Real.exp ((-1845091170091/500000000000 : ℝ)/8) ∧
    Real.exp ((-1845091170091/500000000000 : ℝ)/8) ≤ (315240331763161709/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1845091170091/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d9_exp_log_high :
    (315240331766353517/500000000000000000 : ℝ) ≤ Real.exp ((-3690182340101/1000000000000 : ℝ)/8) ∧
    Real.exp ((-3690182340101/1000000000000 : ℝ)/8) ≤ (126096132706541407/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3690182340101/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d9_exp_u_low :
    (23049673318944653/25000000000000000 : ℝ) ≤ Real.exp ((-649793825919/1000000000000 : ℝ)/8) ∧
    Real.exp ((-649793825919/1000000000000 : ℝ)/8) ≤ (921986932757786121/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-649793825919/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d9_exp_u_high :
    (460993466393126233/500000000000000000 : ℝ) ≤ Real.exp ((-81224228209/125000000000 : ℝ)/8) ∧
    Real.exp ((-81224228209/125000000000 : ℝ)/8) ≤ (921986932786252467/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-81224228209/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
-- Degree 10
def d10_ell_low : ℝ := (1151292546497/500000000000 : ℝ)
def d10_ell_high : ℝ := (460517018599/200000000000 : ℝ)
def d10_z_low : ℝ := (-84823141/3906250000 : ℝ)
def d10_z_high : ℝ := (-4342944819/200000000000 : ℝ)
def d10_comp_low : ℝ := (2148065677/100000000000 : ℝ)
def d10_comp_high : ℝ := (5370164193/250000000000 : ℝ)
def d10_log_low : ℝ := (-153624097357/40000000000 : ℝ)
def d10_log_high : ℝ := (-3840602433831/1000000000000 : ℝ)
def d10_u_low : ℝ := (-3985201693/6250000000 : ℝ)
def d10_u_high : ℝ := (-637632270643/1000000000000 : ℝ)
theorem d10_exp_ell_low :
    (133352143216331641/100000000000000000 : ℝ) ≤ Real.exp ((1151292546497/500000000000 : ℝ)/8) ∧
    Real.exp ((1151292546497/500000000000 : ℝ)/8) ≤ (1333521432163316411/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((1151292546497/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d10_exp_ell_high :
    (13335214321634831/10000000000000000 : ℝ) ≤ Real.exp ((460517018599/200000000000 : ℝ)/8) ∧
    Real.exp ((460517018599/200000000000 : ℝ)/8) ≤ (1333521432163483101/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((460517018599/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d10_exp_z_low :
    (498644669989709393/500000000000000000 : ℝ) ≤ Real.exp ((-84823141/3906250000 : ℝ)/8) ∧
    Real.exp ((-84823141/3906250000 : ℝ)/8) ≤ (997289339979418787/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-84823141/3906250000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d10_exp_z_high :
    (124661167497442931/125000000000000000 : ℝ) ≤ Real.exp ((-4342944819/200000000000 : ℝ)/8) ∧
    Real.exp ((-4342944819/200000000000 : ℝ)/8) ≤ (997289339979543449/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4342944819/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d10_exp_log_low :
    (309368398273570923/500000000000000000 : ℝ) ≤ Real.exp ((-153624097357/40000000000 : ℝ)/8) ∧
    Real.exp ((-153624097357/40000000000 : ℝ)/8) ≤ (618736796547141847/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-153624097357/40000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d10_exp_log_high :
    (618736796554412003/1000000000000000000 : ℝ) ≤ Real.exp ((-3840602433831/1000000000000 : ℝ)/8) ∧
    Real.exp ((-3840602433831/1000000000000 : ℝ)/8) ≤ (154684199138603001/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3840602433831/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d10_exp_u_low :
    (36935583920122607/40000000000000000 : ℝ) ≤ Real.exp ((-3985201693/6250000000 : ℝ)/8) ∧
    Real.exp ((-3985201693/6250000000 : ℝ)/8) ≤ (115423699750383147/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3985201693/6250000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d10_exp_u_high :
    (57711849876901287/62500000000000000 : ℝ) ≤ Real.exp ((-637632270643/1000000000000 : ℝ)/8) ∧
    Real.exp ((-637632270643/1000000000000 : ℝ)/8) ≤ (923389598030420593/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-637632270643/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
-- Degree 11
def d11_ell_low : ℝ := (1198947636399/500000000000 : ℝ)
def d11_ell_high : ℝ := (2397895272799/1000000000000 : ℝ)
def d11_z_low : ℝ := (-18956017793/1000000000000 : ℝ)
def d11_z_high : ℝ := (-148093889/7812500000 : ℝ)
def d11_comp_low : ℝ := (18777482373/1000000000000 : ℝ)
def d11_comp_high : ℝ := (150219859/8000000000 : ℝ)
def d11_log_low : ℝ := (-795019374627/200000000000 : ℝ)
def d11_log_high : ℝ := (-3975096873027/1000000000000 : ℝ)
def d11_u_low : ℝ := (-627074465233/1000000000000 : ℝ)
def d11_u_high : ℝ := (-156768616251/250000000000 : ℝ)
theorem d11_exp_ell_low :
    (84343982419967449/62500000000000000 : ℝ) ≤ Real.exp ((1198947636399/500000000000 : ℝ)/8) ∧
    Real.exp ((1198947636399/500000000000 : ℝ)/8) ≤ (269900743743895837/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((1198947636399/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d11_exp_ell_high :
    (10542997802497249/7812500000000000 : ℝ) ≤ Real.exp ((2397895272799/1000000000000 : ℝ)/8) ∧
    Real.exp ((2397895272799/1000000000000 : ℝ)/8) ≤ (1349503718719647873/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((2397895272799/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d11_exp_z_low :
    (99763330283030509/100000000000000000 : ℝ) ≤ Real.exp ((-18956017793/1000000000000 : ℝ)/8) ∧
    Real.exp ((-18956017793/1000000000000 : ℝ)/8) ≤ (997633302830305091/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-18956017793/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d11_exp_z_high :
    (498816651415214897/500000000000000000 : ℝ) ≤ Real.exp ((-148093889/7812500000 : ℝ)/8) ∧
    Real.exp ((-148093889/7812500000 : ℝ)/8) ≤ (199526660566085959/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-148093889/7812500000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d11_exp_log_low :
    (608421665178237907/1000000000000000000 : ℝ) ≤ Real.exp ((-795019374627/200000000000 : ℝ)/8) ∧
    Real.exp ((-795019374627/200000000000 : ℝ)/8) ≤ (152105416294559477/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-795019374627/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d11_exp_log_high :
    (1521054162966129/2500000000000000 : ℝ) ≤ Real.exp ((-3975096873027/1000000000000 : ℝ)/8) ∧
    Real.exp ((-3975096873027/1000000000000 : ℝ)/8) ≤ (608421665186451601/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3975096873027/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d11_exp_u_low :
    (184921804693733417/200000000000000000 : ℝ) ≤ Real.exp ((-627074465233/1000000000000 : ℝ)/8) ∧
    Real.exp ((-627074465233/1000000000000 : ℝ)/8) ≤ (462304511734333543/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-627074465233/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d11_exp_u_high :
    (462304511747567009/500000000000000000 : ℝ) ≤ Real.exp ((-156768616251/250000000000 : ℝ)/8) ∧
    Real.exp ((-156768616251/250000000000 : ℝ)/8) ≤ (924609023495134019/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-156768616251/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
-- Degree 12
def d12_ell_low : ℝ := (621226662447/250000000000 : ℝ)
def d12_ell_high : ℝ := (2484906649789/1000000000000 : ℝ)
def d12_z_low : ℝ := (-16767900183/1000000000000 : ℝ)
def d12_z_high : ℝ := (-8383950091/500000000000 : ℝ)
def d12_comp_low : ℝ := (16628101411/1000000000000 : ℝ)
def d12_comp_high : ℝ := (16628101413/1000000000000 : ℝ)
def d12_log_low : ℝ := (-2048330579401/500000000000 : ℝ)
def d12_log_high : ℝ := (-102416528967/25000000000 : ℝ)
def d12_u_low : ℝ := (-308891428967/500000000000 : ℝ)
def d12_u_high : ℝ := (-38611428607/62500000000 : ℝ)
theorem d12_exp_ell_low :
    (341065400455341469/250000000000000000 : ℝ) ≤ Real.exp ((621226662447/250000000000 : ℝ)/8) ∧
    Real.exp ((621226662447/250000000000 : ℝ)/8) ≤ (1364261601821365877/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((621226662447/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d12_exp_ell_high :
    (1364261601821536409/1000000000000000000 : ℝ) ≤ Real.exp ((2484906649789/1000000000000 : ℝ)/8) ∧
    Real.exp ((2484906649789/1000000000000 : ℝ)/8) ≤ (136426160182153641/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((2484906649789/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d12_exp_z_low :
    (498953103762553733/500000000000000000 : ℝ) ≤ Real.exp ((-16767900183/1000000000000 : ℝ)/8) ∧
    Real.exp ((-16767900183/1000000000000 : ℝ)/8) ≤ (997906207525107467/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16767900183/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d12_exp_z_high :
    (249476551881308051/250000000000000000 : ℝ) ≤ Real.exp ((-8383950091/500000000000 : ℝ)/8) ∧
    Real.exp ((-8383950091/500000000000 : ℝ)/8) ≤ (199581241505046441/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8383950091/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d12_exp_log_low :
    (29962313059074327/50000000000000000 : ℝ) ≤ Real.exp ((-2048330579401/500000000000 : ℝ)/8) ∧
    Real.exp ((-2048330579401/500000000000 : ℝ)/8) ≤ (599246261181486541/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2048330579401/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d12_exp_log_high :
    (119849252238125009/200000000000000000 : ℝ) ≤ Real.exp ((-102416528967/25000000000 : ℝ)/8) ∧
    Real.exp ((-102416528967/25000000000 : ℝ)/8) ≤ (299623130595312523/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-102416528967/25000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d12_exp_u_low :
    (115710441917271291/125000000000000000 : ℝ) ≤ Real.exp ((-308891428967/500000000000 : ℝ)/8) ∧
    Real.exp ((-308891428967/500000000000 : ℝ)/8) ≤ (925683535338170329/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-308891428967/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d12_exp_u_high :
    (462841767681929023/500000000000000000 : ℝ) ≤ Real.exp ((-38611428607/62500000000 : ℝ)/8) ∧
    Real.exp ((-38611428607/62500000000 : ℝ)/8) ≤ (925683535363858047/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-38611428607/62500000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
-- Degree 13
def d13_ell_low : ℝ := (2564949357461/1000000000000 : ℝ)
def d13_ell_high : ℝ := (1282474678731/500000000000 : ℝ)
def d13_z_low : ℝ := (-2999009579/200000000000 : ℝ)
def d13_z_high : ℝ := (-7497523947/500000000000 : ℝ)
def d13_comp_low : ℝ := (7441591003/500000000000 : ℝ)
def d13_comp_high : ℝ := (1860397751/125000000000 : ℝ)
def d13_log_low : ℝ := (-84150468559/20000000000 : ℝ)
def d13_log_high : ℝ := (-841504685563/200000000000 : ℝ)
def d13_u_low : ℝ := (-609512548773/1000000000000 : ℝ)
def d13_u_high : ℝ := (-121902509711/200000000000 : ℝ)
theorem d13_exp_ell_low :
    (688990007568267819/500000000000000000 : ℝ) ≤ Real.exp ((2564949357461/1000000000000 : ℝ)/8) ∧
    Real.exp ((2564949357461/1000000000000 : ℝ)/8) ≤ (1377980015136535639/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((2564949357461/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d13_exp_ell_high :
    (275596003027341577/200000000000000000 : ℝ) ≤ Real.exp ((1282474678731/500000000000 : ℝ)/8) ∧
    Real.exp ((1282474678731/500000000000 : ℝ)/8) ≤ (688990007568353943/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((1282474678731/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d13_exp_z_low :
    (249531843642034007/250000000000000000 : ℝ) ≤ Real.exp ((-2999009579/200000000000 : ℝ)/8) ∧
    Real.exp ((-2999009579/200000000000 : ℝ)/8) ≤ (998127374568136029/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2999009579/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d13_exp_z_high :
    (499063687284130397/500000000000000000 : ℝ) ≤ Real.exp ((-7497523947/500000000000 : ℝ)/8) ∧
    Real.exp ((-7497523947/500000000000 : ℝ)/8) ≤ (199625474913652159/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-7497523947/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d13_exp_log_low :
    (590999310352035093/1000000000000000000 : ℝ) ≤ Real.exp ((-84150468559/20000000000 : ℝ)/8) ∧
    Real.exp ((-84150468559/20000000000 : ℝ)/8) ≤ (295499655176017547/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-84150468559/20000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d13_exp_log_high :
    (590999310362008207/1000000000000000000 : ℝ) ≤ Real.exp ((-841504685563/200000000000 : ℝ)/8) ∧
    Real.exp ((-841504685563/200000000000 : ℝ)/8) ≤ (36937456897625513/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-841504685563/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d13_exp_u_low :
    (926640991284253787/1000000000000000000 : ℝ) ≤ Real.exp ((-609512548773/1000000000000 : ℝ)/8) ∧
    Real.exp ((-609512548773/1000000000000 : ℝ)/8) ≤ (231660247821063447/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-609512548773/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d13_exp_u_high :
    (463320495654752377/500000000000000000 : ℝ) ≤ Real.exp ((-121902509711/200000000000 : ℝ)/8) ∧
    Real.exp ((-121902509711/200000000000 : ℝ)/8) ≤ (185328198261900951/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-121902509711/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
-- Degree 14
def d14_ell_low : ℝ := (527811465923/200000000000 : ℝ)
def d14_ell_high : ℝ := (164941083101/62500000000 : ℝ)
def d14_z_low : ℝ := (-541318831/40000000000 : ℝ)
def d14_z_high : ℝ := (-6766485387/500000000000 : ℝ)
def d14_comp_low : ℝ := (2688362361/200000000000 : ℝ)
def d14_comp_high : ℝ := (13441811807/1000000000000 : ℝ)
def d14_log_low : ℝ := (-2154692573027/500000000000 : ℝ)
def d14_log_high : ℝ := (-269336571619/62500000000 : ℝ)
def d14_u_low : ℝ := (-301040448819/500000000000 : ℝ)
def d14_u_high : ℝ := (-301040448713/500000000000 : ℝ)
theorem d14_exp_ell_low :
    (1390804235062413177/1000000000000000000 : ℝ) ≤ Real.exp ((527811465923/200000000000 : ℝ)/8) ∧
    Real.exp ((527811465923/200000000000 : ℝ)/8) ≤ (695402117531206589/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((527811465923/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d14_exp_ell_high :
    (1390804235062587027/1000000000000000000 : ℝ) ≤ Real.exp ((164941083101/62500000000 : ℝ)/8) ∧
    Real.exp ((164941083101/62500000000 : ℝ)/8) ≤ (347701058765646757/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((164941083101/62500000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d14_exp_z_low :
    (998309808638070927/1000000000000000000 : ℝ) ≤ Real.exp ((-541318831/40000000000 : ℝ)/8) ∧
    Real.exp ((-541318831/40000000000 : ℝ)/8) ≤ (62394363039879433/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-541318831/40000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d14_exp_z_high :
    (199661961727639143/200000000000000000 : ℝ) ≤ Real.exp ((-6766485387/500000000000 : ℝ)/8) ∧
    Real.exp ((-6766485387/500000000000 : ℝ)/8) ≤ (249577452159548929/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-6766485387/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d14_exp_log_low :
    (291760994513800329/500000000000000000 : ℝ) ≤ Real.exp ((-2154692573027/500000000000 : ℝ)/8) ∧
    Real.exp ((-2154692573027/500000000000 : ℝ)/8) ≤ (583521989027600659/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2154692573027/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d14_exp_log_high :
    (116704397807708339/200000000000000000 : ℝ) ≤ Real.exp ((-269336571619/62500000000 : ℝ)/8) ∧
    Real.exp ((-269336571619/62500000000 : ℝ)/8) ≤ (4558765539363607/7812500000000000 : ℝ) := by
  have h := exp_small_bounds ((-269336571619/62500000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d14_exp_u_low :
    (115937775038370183/125000000000000000 : ℝ) ≤ Real.exp ((-301040448819/500000000000 : ℝ)/8) ∧
    Real.exp ((-301040448819/500000000000 : ℝ)/8) ≤ (185500440061392293/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-301040448819/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d14_exp_u_high :
    (57968887520721267/62500000000000000 : ℝ) ≤ Real.exp ((-301040448713/500000000000 : ℝ)/8) ∧
    Real.exp ((-301040448713/500000000000 : ℝ)/8) ≤ (927502200331540273/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-301040448713/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
-- Degree 15
def d15_ell_low : ℝ := (1354025100551/500000000000 : ℝ)
def d15_ell_high : ℝ := (2708050201103/1000000000000 : ℝ)
def d15_z_low : ℝ := (-12308979103/1000000000000 : ℝ)
def d15_z_high : ℝ := (-6154489551/500000000000 : ℝ)
def d15_comp_low : ℝ := (764595843/62500000000 : ℝ)
def d15_comp_high : ℝ := (1223353349/100000000000 : ℝ)
def d15_log_low : ℝ := (-4403574451307/1000000000000 : ℝ)
def d15_log_high : ℝ := (-4403574451143/1000000000000 : ℝ)
def d15_u_low : ℝ := (-297674243117/500000000000 : ℝ)
def d15_u_high : ℝ := (-297674243013/500000000000 : ℝ)
theorem d15_exp_ell_low :
    (1402850552006637329/1000000000000000000 : ℝ) ≤ Real.exp ((1354025100551/500000000000 : ℝ)/8) ∧
    Real.exp ((1354025100551/500000000000 : ℝ)/8) ≤ (140285055200663733/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((1354025100551/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d15_exp_ell_high :
    (280570110401362537/200000000000000000 : ℝ) ≤ Real.exp ((2708050201103/1000000000000 : ℝ)/8) ∧
    Real.exp ((2708050201103/1000000000000 : ℝ)/8) ≤ (701425276003406343/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((2708050201103/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d15_exp_z_low :
    (249615640171176531/250000000000000000 : ℝ) ≤ Real.exp ((-12308979103/1000000000000 : ℝ)/8) ∧
    Real.exp ((-12308979103/1000000000000 : ℝ)/8) ≤ (7987700485477649/8000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-12308979103/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d15_exp_z_high :
    (249615640171207733/250000000000000000 : ℝ) ≤ Real.exp ((-6154489551/500000000000 : ℝ)/8) ∧
    Real.exp ((-6154489551/500000000000 : ℝ)/8) ≤ (998462560684830933/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-6154489551/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d15_exp_log_low :
    (576692083086404789/1000000000000000000 : ℝ) ≤ Real.exp ((-4403574451307/1000000000000 : ℝ)/8) ∧
    Real.exp ((-4403574451307/1000000000000 : ℝ)/8) ≤ (57669208308640479/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4403574451307/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d15_exp_log_high :
    (18021627596819593/31250000000000000 : ℝ) ≤ Real.exp ((-4403574451143/1000000000000 : ℝ)/8) ∧
    Real.exp ((-4403574451143/1000000000000 : ℝ)/8) ≤ (576692083098226977/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4403574451143/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d15_exp_u_low :
    (928283069630545493/1000000000000000000 : ℝ) ≤ Real.exp ((-297674243117/500000000000 : ℝ)/8) ∧
    Real.exp ((-297674243117/500000000000 : ℝ)/8) ≤ (464141534815272747/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-297674243117/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d15_exp_u_high :
    (928283069654680853/1000000000000000000 : ℝ) ≤ Real.exp ((-297674243013/500000000000 : ℝ)/8) ∧
    Real.exp ((-297674243013/500000000000 : ℝ)/8) ≤ (464141534827340427/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-297674243013/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
-- Degree 16
def d16_ell_low : ℝ := (2772588722239/1000000000000 : ℝ)
def d16_ell_high : ℝ := (8664339757/3125000000 : ℝ)
def d16_z_low : ℝ := (-11271055007/1000000000000 : ℝ)
def d16_z_high : ℝ := (-5635527503/500000000000 : ℝ)
def d16_comp_low : ℝ := (5603887317/500000000000 : ℝ)
def d16_comp_high : ℝ := (2801943659/250000000000 : ℝ)
def d16_log_low : ℝ := (-561393447219/125000000000 : ℝ)
def d16_log_high : ℝ := (-1122786894393/250000000000 : ℝ)
def d16_u_low : ℝ := (-589206746153/1000000000000 : ℝ)
def d16_u_high : ℝ := (-147301686487/250000000000 : ℝ)
theorem d16_exp_ell_low :
    (88388347648309809/62500000000000000 : ℝ) ≤ Real.exp ((2772588722239/1000000000000 : ℝ)/8) ∧
    Real.exp ((2772588722239/1000000000000 : ℝ)/8) ≤ (282842712474591389/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((2772588722239/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d16_exp_ell_high :
    (35355339059328343/25000000000000000 : ℝ) ≤ Real.exp ((8664339757/3125000000 : ℝ)/8) ∧
    Real.exp ((8664339757/3125000000 : ℝ)/8) ≤ (1414213562373133721/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((8664339757/3125000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d16_exp_z_low :
    (199718422026453259/200000000000000000 : ℝ) ≤ Real.exp ((-11271055007/1000000000000 : ℝ)/8) ∧
    Real.exp ((-11271055007/1000000000000 : ℝ)/8) ≤ (124824013766533287/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-11271055007/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d16_exp_z_high :
    (998592110132391119/1000000000000000000 : ℝ) ≤ Real.exp ((-5635527503/500000000000 : ℝ)/8) ∧
    Real.exp ((-5635527503/500000000000 : ℝ)/8) ≤ (12482401376654889/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5635527503/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d16_exp_log_low :
    (285206834233384997/500000000000000000 : ℝ) ≤ Real.exp ((-561393447219/125000000000 : ℝ)/8) ∧
    Real.exp ((-561393447219/125000000000 : ℝ)/8) ≤ (114082733693353999/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-561393447219/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d16_exp_log_high :
    (285206834239802151/500000000000000000 : ℝ) ≤ Real.exp ((-1122786894393/250000000000 : ℝ)/8) ∧
    Real.exp ((-1122786894393/250000000000 : ℝ)/8) ≤ (570413668479604303/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1122786894393/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d16_exp_u_low :
    (928996002427933197/1000000000000000000 : ℝ) ≤ Real.exp ((-589206746153/1000000000000 : ℝ)/8) ∧
    Real.exp ((-589206746153/1000000000000 : ℝ)/8) ≤ (464498001213966599/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-589206746153/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d16_exp_u_high :
    (5806225015323367/6250000000000000 : ℝ) ≤ Real.exp ((-147301686487/250000000000 : ℝ)/8) ∧
    Real.exp ((-147301686487/250000000000 : ℝ)/8) ≤ (928996002451738721/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-147301686487/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
-- Degree 17
def d17_ell_low : ℝ := (354151668007/125000000000 : ℝ)
def d17_ell_high : ℝ := (2833213344057/1000000000000 : ℝ)
def d17_z_low : ℝ := (-10381062467/1000000000000 : ℝ)
def d17_z_high : ℝ := (-5190531233/500000000000 : ℝ)
def d17_comp_low : ℝ := (10327365209/1000000000000 : ℝ)
def d17_comp_high : ℝ := (10327365211/1000000000000 : ℝ)
def d17_log_low : ℝ := (-4572958090437/1000000000000 : ℝ)
def d17_log_high : ℝ := (-4572958090243/1000000000000 : ℝ)
def d17_u_low : ℝ := (-145892415433/250000000000 : ℝ)
def d17_u_high : ℝ := (-58356966153/100000000000 : ℝ)
theorem d17_exp_ell_low :
    (142497129264726629/100000000000000000 : ℝ) ≤ Real.exp ((354151668007/125000000000 : ℝ)/8) ∧
    Real.exp ((354151668007/125000000000 : ℝ)/8) ≤ (1424971292647266291/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((354151668007/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d17_exp_ell_high :
    (1424971292647444411/1000000000000000000 : ℝ) ≤ Real.exp ((2833213344057/1000000000000 : ℝ)/8) ∧
    Real.exp ((2833213344057/1000000000000 : ℝ)/8) ≤ (356242823161861103/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((2833213344057/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d17_exp_z_low :
    (249675802188256441/250000000000000000 : ℝ) ≤ Real.exp ((-10381062467/1000000000000 : ℝ)/8) ∧
    Real.exp ((-10381062467/1000000000000 : ℝ)/8) ≤ (199740641750605153/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10381062467/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d17_exp_z_high :
    (499351604376575301/500000000000000000 : ℝ) ≤ Real.exp ((-5190531233/500000000000 : ℝ)/8) ∧
    Real.exp ((-5190531233/500000000000 : ℝ)/8) ≤ (998703208753150603/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5190531233/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d17_exp_log_low :
    (70576270492572617/125000000000000000 : ℝ) ≤ Real.exp ((-4572958090437/1000000000000 : ℝ)/8) ∧
    Real.exp ((-4572958090437/1000000000000 : ℝ)/8) ≤ (564610163940580937/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4572958090437/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d17_exp_log_high :
    (141152540988568183/250000000000000000 : ℝ) ≤ Real.exp ((-4572958090243/1000000000000 : ℝ)/8) ∧
    Real.exp ((-4572958090243/1000000000000 : ℝ)/8) ≤ (564610163954272733/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4572958090243/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d17_exp_u_low :
    (929650836722158431/1000000000000000000 : ℝ) ≤ Real.exp ((-145892415433/250000000000 : ℝ)/8) ∧
    Real.exp ((-145892415433/250000000000 : ℝ)/8) ≤ (29051588647567451/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-145892415433/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d17_exp_u_high :
    (185930167349126423/200000000000000000 : ℝ) ≤ Real.exp ((-58356966153/100000000000 : ℝ)/8) ∧
    Real.exp ((-58356966153/100000000000 : ℝ)/8) ≤ (232412709186408029/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-58356966153/100000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
-- Degree 18
def d18_ell_low : ℝ := (361296469737/125000000000 : ℝ)
def d18_ell_high : ℝ := (2890371757897/1000000000000 : ℝ)
def d18_z_low : ℝ := (-9610451563/1000000000000 : ℝ)
def d18_z_high : ℝ := (-4805225781/500000000000 : ℝ)
def d18_comp_low : ℝ := (1912883751/200000000000 : ℝ)
def d18_comp_high : ℝ := (9564418757/1000000000000 : ℝ)
def d18_log_low : ℝ := (-4649705445841/1000000000000 : ℝ)
def d18_log_high : ℝ := (-4649705445631/1000000000000 : ℝ)
def d18_u_low : ℝ := (-57836805129/100000000000 : ℝ)
def d18_u_high : ℝ := (-578368051091/1000000000000 : ℝ)
theorem d18_exp_ell_low :
    (358797221971114987/250000000000000000 : ℝ) ≤ Real.exp ((361296469737/125000000000 : ℝ)/8) ∧
    Real.exp ((361296469737/125000000000 : ℝ)/8) ≤ (1435188887884459949/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((361296469737/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d18_exp_ell_high :
    (1435188887884639347/1000000000000000000 : ℝ) ≤ Real.exp ((2890371757897/1000000000000 : ℝ)/8) ∧
    Real.exp ((2890371757897/1000000000000 : ℝ)/8) ≤ (358797221971159837/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((2890371757897/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d18_exp_z_low :
    (49939970741717897/50000000000000000 : ℝ) ≤ Real.exp ((-9610451563/1000000000000 : ℝ)/8) ∧
    Real.exp ((-9610451563/1000000000000 : ℝ)/8) ≤ (998799414834357941/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9610451563/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d18_exp_z_high :
    (99879941483448279/100000000000000000 : ℝ) ≤ Real.exp ((-4805225781/500000000000 : ℝ)/8) ∧
    Real.exp ((-4805225781/500000000000 : ℝ)/8) ≤ (998799414834482791/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4805225781/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d18_exp_log_low :
    (279609760260493607/500000000000000000 : ℝ) ≤ Real.exp ((-4649705445841/1000000000000 : ℝ)/8) ∧
    Real.exp ((-4649705445841/1000000000000 : ℝ)/8) ≤ (111843904104197443/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4649705445841/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d18_exp_log_high :
    (559219520535666727/1000000000000000000 : ℝ) ≤ Real.exp ((-4649705445631/1000000000000 : ℝ)/8) ∧
    Real.exp ((-4649705445631/1000000000000 : ℝ)/8) ≤ (69902440066958341/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4649705445631/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d18_exp_u_low :
    (930255493462620727/1000000000000000000 : ℝ) ≤ Real.exp ((-57836805129/100000000000 : ℝ)/8) ∧
    Real.exp ((-57836805129/100000000000 : ℝ)/8) ≤ (116281936682827591/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-57836805129/100000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d18_exp_u_high :
    (930255493485760833/1000000000000000000 : ℝ) ≤ Real.exp ((-578368051091/1000000000000 : ℝ)/8) ∧
    Real.exp ((-578368051091/1000000000000 : ℝ)/8) ≤ (465127746742880417/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-578368051091/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
-- Degree 19
def d19_ell_low : ℝ := (1472219489583/500000000000 : ℝ)
def d19_ell_high : ℝ := (2944438979167/1000000000000 : ℝ)
def d19_z_low : ℝ := (-2234363631/250000000000 : ℝ)
def d19_z_high : ℝ := (-8937454523/1000000000000 : ℝ)
def d19_comp_low : ℝ := (1779526839/200000000000 : ℝ)
def d19_comp_high : ℝ := (8897634197/1000000000000 : ℝ)
def d19_log_low : ℝ := (-73780779037/15625000000 : ℝ)
def d19_log_high : ℝ := (-2360984929071/500000000000 : ℝ)
def d19_u_low : ℝ := (-286772765101/500000000000 : ℝ)
def d19_u_high : ℝ := (-114709106001/200000000000 : ℝ)
theorem d19_exp_ell_low :
    (361230330773318199/250000000000000000 : ℝ) ≤ Real.exp ((1472219489583/500000000000 : ℝ)/8) ∧
    Real.exp ((1472219489583/500000000000 : ℝ)/8) ≤ (1444921323093272797/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((1472219489583/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d19_exp_ell_high :
    (1444921323093453411/1000000000000000000 : ℝ) ≤ Real.exp ((2944438979167/1000000000000 : ℝ)/8) ∧
    Real.exp ((2944438979167/1000000000000 : ℝ)/8) ≤ (361230330773363353/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((2944438979167/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d19_exp_z_low :
    (249720860499944447/250000000000000000 : ℝ) ≤ Real.exp ((-2234363631/250000000000 : ℝ)/8) ∧
    Real.exp ((-2234363631/250000000000 : ℝ)/8) ≤ (998883441999777789/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2234363631/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d19_exp_z_high :
    (124860430249987831/125000000000000000 : ℝ) ≤ Real.exp ((-8937454523/1000000000000 : ℝ)/8) ∧
    Real.exp ((-8937454523/1000000000000 : ℝ)/8) ≤ (998883441999902649/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8937454523/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d19_exp_log_low :
    (138547702064399773/250000000000000000 : ℝ) ≤ Real.exp ((-73780779037/15625000000 : ℝ)/8) ∧
    Real.exp ((-73780779037/15625000000 : ℝ)/8) ≤ (554190808257599093/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-73780779037/15625000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d19_exp_log_high :
    (554190808273254983/1000000000000000000 : ℝ) ≤ Real.exp ((-2360984929071/500000000000 : ℝ)/8) ∧
    Real.exp ((-2360984929071/500000000000 : ℝ)/8) ≤ (69273851034156873/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2360984929071/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d19_exp_u_low :
    (930816434609347453/1000000000000000000 : ℝ) ≤ Real.exp ((-286772765101/500000000000 : ℝ)/8) ∧
    Real.exp ((-286772765101/500000000000 : ℝ)/8) ≤ (465408217304673727/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-286772765101/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d19_exp_u_high :
    (116352054329033601/125000000000000000 : ℝ) ≤ Real.exp ((-114709106001/200000000000 : ℝ)/8) ∧
    Real.exp ((-114709106001/200000000000 : ℝ)/8) ≤ (930816434632268809/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-114709106001/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
-- Degree 20
def d20_ell_low : ℝ := (2995732273553/1000000000000 : ℝ)
def d20_ell_high : ℝ := (1497866136777/500000000000 : ℝ)
def d20_z_low : ℝ := (-4172602509/500000000000 : ℝ)
def d20_z_high : ℝ := (-8345205017/1000000000000 : ℝ)
def d20_comp_low : ℝ := (1662096091/200000000000 : ℝ)
def d20_comp_high : ℝ := (8310480457/1000000000000 : ℝ)
def d20_log_low : ℝ := (-47902378553/10000000000 : ℝ)
def d20_log_high : ℝ := (-4790237855059/1000000000000 : ℝ)
def d20_u_low : ℝ := (-71131950043/125000000000 : ℝ)
def d20_u_high : ℝ := (-11381112003/20000000000 : ℝ)
theorem d20_exp_ell_low :
    (1454215433448773543/1000000000000000000 : ℝ) ≤ Real.exp ((2995732273553/1000000000000 : ℝ)/8) ∧
    Real.exp ((2995732273553/1000000000000 : ℝ)/8) ≤ (181776929181096693/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((2995732273553/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d20_exp_ell_high :
    (36355385836223883/25000000000000000 : ℝ) ≤ Real.exp ((1497866136777/500000000000 : ℝ)/8) ∧
    Real.exp ((1497866136777/500000000000 : ℝ)/8) ≤ (1454215433448955321/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((1497866136777/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d20_exp_z_low :
    (998957393265228533/1000000000000000000 : ℝ) ≤ Real.exp ((-4172602509/500000000000 : ℝ)/8) ∧
    Real.exp ((-4172602509/500000000000 : ℝ)/8) ≤ (499478696632614267/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4172602509/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d20_exp_z_high :
    (998957393265353403/1000000000000000000 : ℝ) ≤ Real.exp ((-8345205017/1000000000000 : ℝ)/8) ∧
    Real.exp ((-8345205017/1000000000000 : ℝ)/8) ≤ (249739348316338351/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8345205017/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d20_exp_log_low :
    (109896348438198259/200000000000000000 : ℝ) ≤ Real.exp ((-47902378553/10000000000 : ℝ)/8) ∧
    Real.exp ((-47902378553/10000000000 : ℝ)/8) ≤ (8585652221734239/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-47902378553/10000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d20_exp_log_high :
    (549481742207544433/1000000000000000000 : ℝ) ≤ Real.exp ((-4790237855059/1000000000000 : ℝ)/8) ∧
    Real.exp ((-4790237855059/1000000000000 : ℝ)/8) ≤ (274740871103772217/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4790237855059/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d20_exp_u_low :
    (37253559751970847/40000000000000000 : ℝ) ≤ Real.exp ((-71131950043/125000000000 : ℝ)/8) ∧
    Real.exp ((-71131950043/125000000000 : ℝ)/8) ≤ (116417374224908897/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-71131950043/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem d20_exp_u_high :
    (186267798764371229/200000000000000000 : ℝ) ≤ Real.exp ((-11381112003/20000000000 : ℝ)/8) ∧
    Real.exp ((-11381112003/20000000000 : ℝ)/8) ≤ (465669496910928073/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-11381112003/20000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith

theorem table3_rounding_9 :
    (((2.08862-1/100000) : ℝ) < majorant 9 ∧ majorant 9 ≤ 2.08862) ∧
      ((2.17952 : ℝ) ≤ target 9 ∧ target 9 < (2.17952+1/100000)) := by
  have helo := exp_bounds_from_eighth _ _ _ (by norm_num) d9_exp_ell_low
  have hehi := exp_bounds_from_eighth _ _ _ (by norm_num) d9_exp_ell_high
  have hzlo := exp_bounds_from_eighth _ _ _ (by norm_num) d9_exp_z_low
  have hzhi := exp_bounds_from_eighth _ _ _ (by norm_num) d9_exp_z_high
  have hloglo := exp_bounds_from_eighth _ _ _ (by norm_num) d9_exp_log_low
  have hloghi := exp_bounds_from_eighth _ _ _ (by norm_num) d9_exp_log_high
  have hulow := exp_bounds_from_eighth _ _ _ (by norm_num) d9_exp_u_low
  have huhi := exp_bounds_from_eighth _ _ _ (by norm_num) d9_exp_u_high
  have hell := table_log_interval 9 d9_ell_low d9_ell_high (by norm_num [d9_ell_low]) (by norm_num)
    ⟨helo.2.trans (by norm_num), le_trans (by norm_num) hehi.1⟩
  have hcomp := table_complement_interval 9 (by norm_num) d9_ell_low d9_ell_high
    d9_z_low d9_z_high d9_comp_low d9_comp_high (by norm_num [d9_ell_low]) hell
    (by norm_num [d9_z_low, d9_ell_low]) (by norm_num [d9_z_high, d9_ell_high])
    (le_trans (by norm_num [d9_comp_high]) hzlo.1)
    (hzhi.2.trans (by norm_num [d9_comp_low]))
  have hden := table_denominator_interval 9 (by norm_num)
    d9_comp_low d9_comp_high d9_log_low d9_log_high (by norm_num [d9_comp_low]) hcomp
    (hloglo.2.trans (by norm_num [d9_comp_low]))
    (le_trans (by norm_num [d9_comp_high]) hloghi.1)
  let denLower : ℝ := 4*((13862943606/10000000000 : ℝ)-d9_log_high/2)
  let denUpper : ℝ := 4*((13862943616/10000000000 : ℝ)-d9_log_low/2)
  have hu := table_majorant_exponent_interval 9 d9_ell_low d9_ell_high denLower denUpper
    d9_u_low d9_u_high (by norm_num [d9_ell_low]) hell
    (by norm_num [denLower, d9_log_high]) hden
    (by norm_num [d9_u_low, d9_ell_high, denLower, d9_log_high])
    (by norm_num [d9_u_high, d9_ell_low, denUpper, d9_log_low])
  constructor
  · exact table_majorant_bounds 9 d9_u_low d9_u_high ((2.08862-1/100000)) (2.08862) hu
      (lt_of_lt_of_le (by norm_num) hulow.1) (huhi.2.trans (by norm_num))
  · exact table_target_bounds 9 d9_ell_low d9_ell_high (2.17952) ((2.17952+1/100000))
      (by norm_num [d9_ell_low]) hell (by norm_num [d9_ell_low]) (by norm_num [d9_ell_high])

theorem table3_rounding_10 :
    (((2.11417-1/100000) : ℝ) < majorant 10 ∧ majorant 10 ≤ 2.11417) ∧
      ((2.26282 : ℝ) ≤ target 10 ∧ target 10 < (2.26282+1/100000)) := by
  have helo := exp_bounds_from_eighth _ _ _ (by norm_num) d10_exp_ell_low
  have hehi := exp_bounds_from_eighth _ _ _ (by norm_num) d10_exp_ell_high
  have hzlo := exp_bounds_from_eighth _ _ _ (by norm_num) d10_exp_z_low
  have hzhi := exp_bounds_from_eighth _ _ _ (by norm_num) d10_exp_z_high
  have hloglo := exp_bounds_from_eighth _ _ _ (by norm_num) d10_exp_log_low
  have hloghi := exp_bounds_from_eighth _ _ _ (by norm_num) d10_exp_log_high
  have hulow := exp_bounds_from_eighth _ _ _ (by norm_num) d10_exp_u_low
  have huhi := exp_bounds_from_eighth _ _ _ (by norm_num) d10_exp_u_high
  have hell := table_log_interval 10 d10_ell_low d10_ell_high (by norm_num [d10_ell_low]) (by norm_num)
    ⟨helo.2.trans (by norm_num), le_trans (by norm_num) hehi.1⟩
  have hcomp := table_complement_interval 10 (by norm_num) d10_ell_low d10_ell_high
    d10_z_low d10_z_high d10_comp_low d10_comp_high (by norm_num [d10_ell_low]) hell
    (by norm_num [d10_z_low, d10_ell_low]) (by norm_num [d10_z_high, d10_ell_high])
    (le_trans (by norm_num [d10_comp_high]) hzlo.1)
    (hzhi.2.trans (by norm_num [d10_comp_low]))
  have hden := table_denominator_interval 10 (by norm_num)
    d10_comp_low d10_comp_high d10_log_low d10_log_high (by norm_num [d10_comp_low]) hcomp
    (hloglo.2.trans (by norm_num [d10_comp_low]))
    (le_trans (by norm_num [d10_comp_high]) hloghi.1)
  let denLower : ℝ := 4*((13862943606/10000000000 : ℝ)-d10_log_high/2)
  let denUpper : ℝ := 4*((13862943616/10000000000 : ℝ)-d10_log_low/2)
  have hu := table_majorant_exponent_interval 10 d10_ell_low d10_ell_high denLower denUpper
    d10_u_low d10_u_high (by norm_num [d10_ell_low]) hell
    (by norm_num [denLower, d10_log_high]) hden
    (by norm_num [d10_u_low, d10_ell_high, denLower, d10_log_high])
    (by norm_num [d10_u_high, d10_ell_low, denUpper, d10_log_low])
  constructor
  · exact table_majorant_bounds 10 d10_u_low d10_u_high ((2.11417-1/100000)) (2.11417) hu
      (lt_of_lt_of_le (by norm_num) hulow.1) (huhi.2.trans (by norm_num))
  · exact table_target_bounds 10 d10_ell_low d10_ell_high (2.26282) ((2.26282+1/100000))
      (by norm_num [d10_ell_low]) hell (by norm_num [d10_ell_low]) (by norm_num [d10_ell_high])

theorem table3_rounding_11 :
    (((2.13661-1/100000) : ℝ) < majorant 11 ∧ majorant 11 ≤ 2.13661) ∧
      ((2.33187 : ℝ) ≤ target 11 ∧ target 11 < (2.33187+1/100000)) := by
  have helo := exp_bounds_from_eighth _ _ _ (by norm_num) d11_exp_ell_low
  have hehi := exp_bounds_from_eighth _ _ _ (by norm_num) d11_exp_ell_high
  have hzlo := exp_bounds_from_eighth _ _ _ (by norm_num) d11_exp_z_low
  have hzhi := exp_bounds_from_eighth _ _ _ (by norm_num) d11_exp_z_high
  have hloglo := exp_bounds_from_eighth _ _ _ (by norm_num) d11_exp_log_low
  have hloghi := exp_bounds_from_eighth _ _ _ (by norm_num) d11_exp_log_high
  have hulow := exp_bounds_from_eighth _ _ _ (by norm_num) d11_exp_u_low
  have huhi := exp_bounds_from_eighth _ _ _ (by norm_num) d11_exp_u_high
  have hell := table_log_interval 11 d11_ell_low d11_ell_high (by norm_num [d11_ell_low]) (by norm_num)
    ⟨helo.2.trans (by norm_num), le_trans (by norm_num) hehi.1⟩
  have hcomp := table_complement_interval 11 (by norm_num) d11_ell_low d11_ell_high
    d11_z_low d11_z_high d11_comp_low d11_comp_high (by norm_num [d11_ell_low]) hell
    (by norm_num [d11_z_low, d11_ell_low]) (by norm_num [d11_z_high, d11_ell_high])
    (le_trans (by norm_num [d11_comp_high]) hzlo.1)
    (hzhi.2.trans (by norm_num [d11_comp_low]))
  have hden := table_denominator_interval 11 (by norm_num)
    d11_comp_low d11_comp_high d11_log_low d11_log_high (by norm_num [d11_comp_low]) hcomp
    (hloglo.2.trans (by norm_num [d11_comp_low]))
    (le_trans (by norm_num [d11_comp_high]) hloghi.1)
  let denLower : ℝ := 4*((13862943606/10000000000 : ℝ)-d11_log_high/2)
  let denUpper : ℝ := 4*((13862943616/10000000000 : ℝ)-d11_log_low/2)
  have hu := table_majorant_exponent_interval 11 d11_ell_low d11_ell_high denLower denUpper
    d11_u_low d11_u_high (by norm_num [d11_ell_low]) hell
    (by norm_num [denLower, d11_log_high]) hden
    (by norm_num [d11_u_low, d11_ell_high, denLower, d11_log_high])
    (by norm_num [d11_u_high, d11_ell_low, denUpper, d11_log_low])
  constructor
  · exact table_majorant_bounds 11 d11_u_low d11_u_high ((2.13661-1/100000)) (2.13661) hu
      (lt_of_lt_of_le (by norm_num) hulow.1) (huhi.2.trans (by norm_num))
  · exact table_target_bounds 11 d11_ell_low d11_ell_high (2.33187) ((2.33187+1/100000))
      (by norm_num [d11_ell_low]) hell (by norm_num [d11_ell_low]) (by norm_num [d11_ell_high])

theorem table3_rounding_12 :
    (((2.15656-1/100000) : ℝ) < majorant 12 ∧ majorant 12 ≤ 2.15656) ∧
      ((2.39028 : ℝ) ≤ target 12 ∧ target 12 < (2.39028+1/100000)) := by
  have helo := exp_bounds_from_eighth _ _ _ (by norm_num) d12_exp_ell_low
  have hehi := exp_bounds_from_eighth _ _ _ (by norm_num) d12_exp_ell_high
  have hzlo := exp_bounds_from_eighth _ _ _ (by norm_num) d12_exp_z_low
  have hzhi := exp_bounds_from_eighth _ _ _ (by norm_num) d12_exp_z_high
  have hloglo := exp_bounds_from_eighth _ _ _ (by norm_num) d12_exp_log_low
  have hloghi := exp_bounds_from_eighth _ _ _ (by norm_num) d12_exp_log_high
  have hulow := exp_bounds_from_eighth _ _ _ (by norm_num) d12_exp_u_low
  have huhi := exp_bounds_from_eighth _ _ _ (by norm_num) d12_exp_u_high
  have hell := table_log_interval 12 d12_ell_low d12_ell_high (by norm_num [d12_ell_low]) (by norm_num)
    ⟨helo.2.trans (by norm_num), le_trans (by norm_num) hehi.1⟩
  have hcomp := table_complement_interval 12 (by norm_num) d12_ell_low d12_ell_high
    d12_z_low d12_z_high d12_comp_low d12_comp_high (by norm_num [d12_ell_low]) hell
    (by norm_num [d12_z_low, d12_ell_low]) (by norm_num [d12_z_high, d12_ell_high])
    (le_trans (by norm_num [d12_comp_high]) hzlo.1)
    (hzhi.2.trans (by norm_num [d12_comp_low]))
  have hden := table_denominator_interval 12 (by norm_num)
    d12_comp_low d12_comp_high d12_log_low d12_log_high (by norm_num [d12_comp_low]) hcomp
    (hloglo.2.trans (by norm_num [d12_comp_low]))
    (le_trans (by norm_num [d12_comp_high]) hloghi.1)
  let denLower : ℝ := 4*((13862943606/10000000000 : ℝ)-d12_log_high/2)
  let denUpper : ℝ := 4*((13862943616/10000000000 : ℝ)-d12_log_low/2)
  have hu := table_majorant_exponent_interval 12 d12_ell_low d12_ell_high denLower denUpper
    d12_u_low d12_u_high (by norm_num [d12_ell_low]) hell
    (by norm_num [denLower, d12_log_high]) hden
    (by norm_num [d12_u_low, d12_ell_high, denLower, d12_log_high])
    (by norm_num [d12_u_high, d12_ell_low, denUpper, d12_log_low])
  constructor
  · exact table_majorant_bounds 12 d12_u_low d12_u_high ((2.15656-1/100000)) (2.15656) hu
      (lt_of_lt_of_le (by norm_num) hulow.1) (huhi.2.trans (by norm_num))
  · exact table_target_bounds 12 d12_ell_low d12_ell_high (2.39028) ((2.39028+1/100000))
      (by norm_num [d12_ell_low]) hell (by norm_num [d12_ell_low]) (by norm_num [d12_ell_high])

theorem table3_rounding_13 :
    (((2.17447-1/100000) : ℝ) < majorant 13 ∧ majorant 13 ≤ 2.17447) ∧
      ((2.44051 : ℝ) ≤ target 13 ∧ target 13 < (2.44051+1/100000)) := by
  have helo := exp_bounds_from_eighth _ _ _ (by norm_num) d13_exp_ell_low
  have hehi := exp_bounds_from_eighth _ _ _ (by norm_num) d13_exp_ell_high
  have hzlo := exp_bounds_from_eighth _ _ _ (by norm_num) d13_exp_z_low
  have hzhi := exp_bounds_from_eighth _ _ _ (by norm_num) d13_exp_z_high
  have hloglo := exp_bounds_from_eighth _ _ _ (by norm_num) d13_exp_log_low
  have hloghi := exp_bounds_from_eighth _ _ _ (by norm_num) d13_exp_log_high
  have hulow := exp_bounds_from_eighth _ _ _ (by norm_num) d13_exp_u_low
  have huhi := exp_bounds_from_eighth _ _ _ (by norm_num) d13_exp_u_high
  have hell := table_log_interval 13 d13_ell_low d13_ell_high (by norm_num [d13_ell_low]) (by norm_num)
    ⟨helo.2.trans (by norm_num), le_trans (by norm_num) hehi.1⟩
  have hcomp := table_complement_interval 13 (by norm_num) d13_ell_low d13_ell_high
    d13_z_low d13_z_high d13_comp_low d13_comp_high (by norm_num [d13_ell_low]) hell
    (by norm_num [d13_z_low, d13_ell_low]) (by norm_num [d13_z_high, d13_ell_high])
    (le_trans (by norm_num [d13_comp_high]) hzlo.1)
    (hzhi.2.trans (by norm_num [d13_comp_low]))
  have hden := table_denominator_interval 13 (by norm_num)
    d13_comp_low d13_comp_high d13_log_low d13_log_high (by norm_num [d13_comp_low]) hcomp
    (hloglo.2.trans (by norm_num [d13_comp_low]))
    (le_trans (by norm_num [d13_comp_high]) hloghi.1)
  let denLower : ℝ := 4*((13862943606/10000000000 : ℝ)-d13_log_high/2)
  let denUpper : ℝ := 4*((13862943616/10000000000 : ℝ)-d13_log_low/2)
  have hu := table_majorant_exponent_interval 13 d13_ell_low d13_ell_high denLower denUpper
    d13_u_low d13_u_high (by norm_num [d13_ell_low]) hell
    (by norm_num [denLower, d13_log_high]) hden
    (by norm_num [d13_u_low, d13_ell_high, denLower, d13_log_high])
    (by norm_num [d13_u_high, d13_ell_low, denUpper, d13_log_low])
  constructor
  · exact table_majorant_bounds 13 d13_u_low d13_u_high ((2.17447-1/100000)) (2.17447) hu
      (lt_of_lt_of_le (by norm_num) hulow.1) (huhi.2.trans (by norm_num))
  · exact table_target_bounds 13 d13_ell_low d13_ell_high (2.44051) ((2.44051+1/100000))
      (by norm_num [d13_ell_low]) hell (by norm_num [d13_ell_low]) (by norm_num [d13_ell_high])

theorem table3_rounding_14 :
    (((2.19069-1/100000) : ℝ) < majorant 14 ∧ majorant 14 ≤ 2.19069) ∧
      ((2.48430 : ℝ) ≤ target 14 ∧ target 14 < (2.48430+1/100000)) := by
  have helo := exp_bounds_from_eighth _ _ _ (by norm_num) d14_exp_ell_low
  have hehi := exp_bounds_from_eighth _ _ _ (by norm_num) d14_exp_ell_high
  have hzlo := exp_bounds_from_eighth _ _ _ (by norm_num) d14_exp_z_low
  have hzhi := exp_bounds_from_eighth _ _ _ (by norm_num) d14_exp_z_high
  have hloglo := exp_bounds_from_eighth _ _ _ (by norm_num) d14_exp_log_low
  have hloghi := exp_bounds_from_eighth _ _ _ (by norm_num) d14_exp_log_high
  have hulow := exp_bounds_from_eighth _ _ _ (by norm_num) d14_exp_u_low
  have huhi := exp_bounds_from_eighth _ _ _ (by norm_num) d14_exp_u_high
  have hell := table_log_interval 14 d14_ell_low d14_ell_high (by norm_num [d14_ell_low]) (by norm_num)
    ⟨helo.2.trans (by norm_num), le_trans (by norm_num) hehi.1⟩
  have hcomp := table_complement_interval 14 (by norm_num) d14_ell_low d14_ell_high
    d14_z_low d14_z_high d14_comp_low d14_comp_high (by norm_num [d14_ell_low]) hell
    (by norm_num [d14_z_low, d14_ell_low]) (by norm_num [d14_z_high, d14_ell_high])
    (le_trans (by norm_num [d14_comp_high]) hzlo.1)
    (hzhi.2.trans (by norm_num [d14_comp_low]))
  have hden := table_denominator_interval 14 (by norm_num)
    d14_comp_low d14_comp_high d14_log_low d14_log_high (by norm_num [d14_comp_low]) hcomp
    (hloglo.2.trans (by norm_num [d14_comp_low]))
    (le_trans (by norm_num [d14_comp_high]) hloghi.1)
  let denLower : ℝ := 4*((13862943606/10000000000 : ℝ)-d14_log_high/2)
  let denUpper : ℝ := 4*((13862943616/10000000000 : ℝ)-d14_log_low/2)
  have hu := table_majorant_exponent_interval 14 d14_ell_low d14_ell_high denLower denUpper
    d14_u_low d14_u_high (by norm_num [d14_ell_low]) hell
    (by norm_num [denLower, d14_log_high]) hden
    (by norm_num [d14_u_low, d14_ell_high, denLower, d14_log_high])
    (by norm_num [d14_u_high, d14_ell_low, denUpper, d14_log_low])
  constructor
  · exact table_majorant_bounds 14 d14_u_low d14_u_high ((2.19069-1/100000)) (2.19069) hu
      (lt_of_lt_of_le (by norm_num) hulow.1) (huhi.2.trans (by norm_num))
  · exact table_target_bounds 14 d14_ell_low d14_ell_high (2.48430) ((2.48430+1/100000))
      (by norm_num [d14_ell_low]) hell (by norm_num [d14_ell_low]) (by norm_num [d14_ell_high])

theorem table3_rounding_15 :
    (((2.20549-1/100000) : ℝ) < majorant 15 ∧ majorant 15 ≤ 2.20549) ∧
      ((2.52292 : ℝ) ≤ target 15 ∧ target 15 < (2.52292+1/100000)) := by
  have helo := exp_bounds_from_eighth _ _ _ (by norm_num) d15_exp_ell_low
  have hehi := exp_bounds_from_eighth _ _ _ (by norm_num) d15_exp_ell_high
  have hzlo := exp_bounds_from_eighth _ _ _ (by norm_num) d15_exp_z_low
  have hzhi := exp_bounds_from_eighth _ _ _ (by norm_num) d15_exp_z_high
  have hloglo := exp_bounds_from_eighth _ _ _ (by norm_num) d15_exp_log_low
  have hloghi := exp_bounds_from_eighth _ _ _ (by norm_num) d15_exp_log_high
  have hulow := exp_bounds_from_eighth _ _ _ (by norm_num) d15_exp_u_low
  have huhi := exp_bounds_from_eighth _ _ _ (by norm_num) d15_exp_u_high
  have hell := table_log_interval 15 d15_ell_low d15_ell_high (by norm_num [d15_ell_low]) (by norm_num)
    ⟨helo.2.trans (by norm_num), le_trans (by norm_num) hehi.1⟩
  have hcomp := table_complement_interval 15 (by norm_num) d15_ell_low d15_ell_high
    d15_z_low d15_z_high d15_comp_low d15_comp_high (by norm_num [d15_ell_low]) hell
    (by norm_num [d15_z_low, d15_ell_low]) (by norm_num [d15_z_high, d15_ell_high])
    (le_trans (by norm_num [d15_comp_high]) hzlo.1)
    (hzhi.2.trans (by norm_num [d15_comp_low]))
  have hden := table_denominator_interval 15 (by norm_num)
    d15_comp_low d15_comp_high d15_log_low d15_log_high (by norm_num [d15_comp_low]) hcomp
    (hloglo.2.trans (by norm_num [d15_comp_low]))
    (le_trans (by norm_num [d15_comp_high]) hloghi.1)
  let denLower : ℝ := 4*((13862943606/10000000000 : ℝ)-d15_log_high/2)
  let denUpper : ℝ := 4*((13862943616/10000000000 : ℝ)-d15_log_low/2)
  have hu := table_majorant_exponent_interval 15 d15_ell_low d15_ell_high denLower denUpper
    d15_u_low d15_u_high (by norm_num [d15_ell_low]) hell
    (by norm_num [denLower, d15_log_high]) hden
    (by norm_num [d15_u_low, d15_ell_high, denLower, d15_log_high])
    (by norm_num [d15_u_high, d15_ell_low, denUpper, d15_log_low])
  constructor
  · exact table_majorant_bounds 15 d15_u_low d15_u_high ((2.20549-1/100000)) (2.20549) hu
      (lt_of_lt_of_le (by norm_num) hulow.1) (huhi.2.trans (by norm_num))
  · exact table_target_bounds 15 d15_ell_low d15_ell_high (2.52292) ((2.52292+1/100000))
      (by norm_num [d15_ell_low]) hell (by norm_num [d15_ell_low]) (by norm_num [d15_ell_high])

theorem table3_rounding_16 :
    (((2.21907-1/100000) : ℝ) < majorant 16 ∧ majorant 16 ≤ 2.21907) ∧
      ((2.55730 : ℝ) ≤ target 16 ∧ target 16 < (2.55730+1/100000)) := by
  have helo := exp_bounds_from_eighth _ _ _ (by norm_num) d16_exp_ell_low
  have hehi := exp_bounds_from_eighth _ _ _ (by norm_num) d16_exp_ell_high
  have hzlo := exp_bounds_from_eighth _ _ _ (by norm_num) d16_exp_z_low
  have hzhi := exp_bounds_from_eighth _ _ _ (by norm_num) d16_exp_z_high
  have hloglo := exp_bounds_from_eighth _ _ _ (by norm_num) d16_exp_log_low
  have hloghi := exp_bounds_from_eighth _ _ _ (by norm_num) d16_exp_log_high
  have hulow := exp_bounds_from_eighth _ _ _ (by norm_num) d16_exp_u_low
  have huhi := exp_bounds_from_eighth _ _ _ (by norm_num) d16_exp_u_high
  have hell := table_log_interval 16 d16_ell_low d16_ell_high (by norm_num [d16_ell_low]) (by norm_num)
    ⟨helo.2.trans (by norm_num), le_trans (by norm_num) hehi.1⟩
  have hcomp := table_complement_interval 16 (by norm_num) d16_ell_low d16_ell_high
    d16_z_low d16_z_high d16_comp_low d16_comp_high (by norm_num [d16_ell_low]) hell
    (by norm_num [d16_z_low, d16_ell_low]) (by norm_num [d16_z_high, d16_ell_high])
    (le_trans (by norm_num [d16_comp_high]) hzlo.1)
    (hzhi.2.trans (by norm_num [d16_comp_low]))
  have hden := table_denominator_interval 16 (by norm_num)
    d16_comp_low d16_comp_high d16_log_low d16_log_high (by norm_num [d16_comp_low]) hcomp
    (hloglo.2.trans (by norm_num [d16_comp_low]))
    (le_trans (by norm_num [d16_comp_high]) hloghi.1)
  let denLower : ℝ := 4*((13862943606/10000000000 : ℝ)-d16_log_high/2)
  let denUpper : ℝ := 4*((13862943616/10000000000 : ℝ)-d16_log_low/2)
  have hu := table_majorant_exponent_interval 16 d16_ell_low d16_ell_high denLower denUpper
    d16_u_low d16_u_high (by norm_num [d16_ell_low]) hell
    (by norm_num [denLower, d16_log_high]) hden
    (by norm_num [d16_u_low, d16_ell_high, denLower, d16_log_high])
    (by norm_num [d16_u_high, d16_ell_low, denUpper, d16_log_low])
  constructor
  · exact table_majorant_bounds 16 d16_u_low d16_u_high ((2.21907-1/100000)) (2.21907) hu
      (lt_of_lt_of_le (by norm_num) hulow.1) (huhi.2.trans (by norm_num))
  · exact table_target_bounds 16 d16_ell_low d16_ell_high (2.55730) ((2.55730+1/100000))
      (by norm_num [d16_ell_low]) hell (by norm_num [d16_ell_low]) (by norm_num [d16_ell_high])

theorem table3_rounding_17 :
    (((2.23162-1/100000) : ℝ) < majorant 17 ∧ majorant 17 ≤ 2.23162) ∧
      ((2.58817 : ℝ) ≤ target 17 ∧ target 17 < (2.58817+1/100000)) := by
  have helo := exp_bounds_from_eighth _ _ _ (by norm_num) d17_exp_ell_low
  have hehi := exp_bounds_from_eighth _ _ _ (by norm_num) d17_exp_ell_high
  have hzlo := exp_bounds_from_eighth _ _ _ (by norm_num) d17_exp_z_low
  have hzhi := exp_bounds_from_eighth _ _ _ (by norm_num) d17_exp_z_high
  have hloglo := exp_bounds_from_eighth _ _ _ (by norm_num) d17_exp_log_low
  have hloghi := exp_bounds_from_eighth _ _ _ (by norm_num) d17_exp_log_high
  have hulow := exp_bounds_from_eighth _ _ _ (by norm_num) d17_exp_u_low
  have huhi := exp_bounds_from_eighth _ _ _ (by norm_num) d17_exp_u_high
  have hell := table_log_interval 17 d17_ell_low d17_ell_high (by norm_num [d17_ell_low]) (by norm_num)
    ⟨helo.2.trans (by norm_num), le_trans (by norm_num) hehi.1⟩
  have hcomp := table_complement_interval 17 (by norm_num) d17_ell_low d17_ell_high
    d17_z_low d17_z_high d17_comp_low d17_comp_high (by norm_num [d17_ell_low]) hell
    (by norm_num [d17_z_low, d17_ell_low]) (by norm_num [d17_z_high, d17_ell_high])
    (le_trans (by norm_num [d17_comp_high]) hzlo.1)
    (hzhi.2.trans (by norm_num [d17_comp_low]))
  have hden := table_denominator_interval 17 (by norm_num)
    d17_comp_low d17_comp_high d17_log_low d17_log_high (by norm_num [d17_comp_low]) hcomp
    (hloglo.2.trans (by norm_num [d17_comp_low]))
    (le_trans (by norm_num [d17_comp_high]) hloghi.1)
  let denLower : ℝ := 4*((13862943606/10000000000 : ℝ)-d17_log_high/2)
  let denUpper : ℝ := 4*((13862943616/10000000000 : ℝ)-d17_log_low/2)
  have hu := table_majorant_exponent_interval 17 d17_ell_low d17_ell_high denLower denUpper
    d17_u_low d17_u_high (by norm_num [d17_ell_low]) hell
    (by norm_num [denLower, d17_log_high]) hden
    (by norm_num [d17_u_low, d17_ell_high, denLower, d17_log_high])
    (by norm_num [d17_u_high, d17_ell_low, denUpper, d17_log_low])
  constructor
  · exact table_majorant_bounds 17 d17_u_low d17_u_high ((2.23162-1/100000)) (2.23162) hu
      (lt_of_lt_of_le (by norm_num) hulow.1) (huhi.2.trans (by norm_num))
  · exact table_target_bounds 17 d17_ell_low d17_ell_high (2.58817) ((2.58817+1/100000))
      (by norm_num [d17_ell_low]) hell (by norm_num [d17_ell_low]) (by norm_num [d17_ell_high])

theorem table3_rounding_18 :
    (((2.24326-1/100000) : ℝ) < majorant 18 ∧ majorant 18 ≤ 2.24326) ∧
      ((2.61609 : ℝ) ≤ target 18 ∧ target 18 < (2.61609+1/100000)) := by
  have helo := exp_bounds_from_eighth _ _ _ (by norm_num) d18_exp_ell_low
  have hehi := exp_bounds_from_eighth _ _ _ (by norm_num) d18_exp_ell_high
  have hzlo := exp_bounds_from_eighth _ _ _ (by norm_num) d18_exp_z_low
  have hzhi := exp_bounds_from_eighth _ _ _ (by norm_num) d18_exp_z_high
  have hloglo := exp_bounds_from_eighth _ _ _ (by norm_num) d18_exp_log_low
  have hloghi := exp_bounds_from_eighth _ _ _ (by norm_num) d18_exp_log_high
  have hulow := exp_bounds_from_eighth _ _ _ (by norm_num) d18_exp_u_low
  have huhi := exp_bounds_from_eighth _ _ _ (by norm_num) d18_exp_u_high
  have hell := table_log_interval 18 d18_ell_low d18_ell_high (by norm_num [d18_ell_low]) (by norm_num)
    ⟨helo.2.trans (by norm_num), le_trans (by norm_num) hehi.1⟩
  have hcomp := table_complement_interval 18 (by norm_num) d18_ell_low d18_ell_high
    d18_z_low d18_z_high d18_comp_low d18_comp_high (by norm_num [d18_ell_low]) hell
    (by norm_num [d18_z_low, d18_ell_low]) (by norm_num [d18_z_high, d18_ell_high])
    (le_trans (by norm_num [d18_comp_high]) hzlo.1)
    (hzhi.2.trans (by norm_num [d18_comp_low]))
  have hden := table_denominator_interval 18 (by norm_num)
    d18_comp_low d18_comp_high d18_log_low d18_log_high (by norm_num [d18_comp_low]) hcomp
    (hloglo.2.trans (by norm_num [d18_comp_low]))
    (le_trans (by norm_num [d18_comp_high]) hloghi.1)
  let denLower : ℝ := 4*((13862943606/10000000000 : ℝ)-d18_log_high/2)
  let denUpper : ℝ := 4*((13862943616/10000000000 : ℝ)-d18_log_low/2)
  have hu := table_majorant_exponent_interval 18 d18_ell_low d18_ell_high denLower denUpper
    d18_u_low d18_u_high (by norm_num [d18_ell_low]) hell
    (by norm_num [denLower, d18_log_high]) hden
    (by norm_num [d18_u_low, d18_ell_high, denLower, d18_log_high])
    (by norm_num [d18_u_high, d18_ell_low, denUpper, d18_log_low])
  constructor
  · exact table_majorant_bounds 18 d18_u_low d18_u_high ((2.24326-1/100000)) (2.24326) hu
      (lt_of_lt_of_le (by norm_num) hulow.1) (huhi.2.trans (by norm_num))
  · exact table_target_bounds 18 d18_ell_low d18_ell_high (2.61609) ((2.61609+1/100000))
      (by norm_num [d18_ell_low]) hell (by norm_num [d18_ell_low]) (by norm_num [d18_ell_high])

theorem table3_rounding_19 :
    (((2.25410-1/100000) : ℝ) < majorant 19 ∧ majorant 19 ≤ 2.25410) ∧
      ((2.64150 : ℝ) ≤ target 19 ∧ target 19 < (2.64150+1/100000)) := by
  have helo := exp_bounds_from_eighth _ _ _ (by norm_num) d19_exp_ell_low
  have hehi := exp_bounds_from_eighth _ _ _ (by norm_num) d19_exp_ell_high
  have hzlo := exp_bounds_from_eighth _ _ _ (by norm_num) d19_exp_z_low
  have hzhi := exp_bounds_from_eighth _ _ _ (by norm_num) d19_exp_z_high
  have hloglo := exp_bounds_from_eighth _ _ _ (by norm_num) d19_exp_log_low
  have hloghi := exp_bounds_from_eighth _ _ _ (by norm_num) d19_exp_log_high
  have hulow := exp_bounds_from_eighth _ _ _ (by norm_num) d19_exp_u_low
  have huhi := exp_bounds_from_eighth _ _ _ (by norm_num) d19_exp_u_high
  have hell := table_log_interval 19 d19_ell_low d19_ell_high (by norm_num [d19_ell_low]) (by norm_num)
    ⟨helo.2.trans (by norm_num), le_trans (by norm_num) hehi.1⟩
  have hcomp := table_complement_interval 19 (by norm_num) d19_ell_low d19_ell_high
    d19_z_low d19_z_high d19_comp_low d19_comp_high (by norm_num [d19_ell_low]) hell
    (by norm_num [d19_z_low, d19_ell_low]) (by norm_num [d19_z_high, d19_ell_high])
    (le_trans (by norm_num [d19_comp_high]) hzlo.1)
    (hzhi.2.trans (by norm_num [d19_comp_low]))
  have hden := table_denominator_interval 19 (by norm_num)
    d19_comp_low d19_comp_high d19_log_low d19_log_high (by norm_num [d19_comp_low]) hcomp
    (hloglo.2.trans (by norm_num [d19_comp_low]))
    (le_trans (by norm_num [d19_comp_high]) hloghi.1)
  let denLower : ℝ := 4*((13862943606/10000000000 : ℝ)-d19_log_high/2)
  let denUpper : ℝ := 4*((13862943616/10000000000 : ℝ)-d19_log_low/2)
  have hu := table_majorant_exponent_interval 19 d19_ell_low d19_ell_high denLower denUpper
    d19_u_low d19_u_high (by norm_num [d19_ell_low]) hell
    (by norm_num [denLower, d19_log_high]) hden
    (by norm_num [d19_u_low, d19_ell_high, denLower, d19_log_high])
    (by norm_num [d19_u_high, d19_ell_low, denUpper, d19_log_low])
  constructor
  · exact table_majorant_bounds 19 d19_u_low d19_u_high ((2.25410-1/100000)) (2.25410) hu
      (lt_of_lt_of_le (by norm_num) hulow.1) (huhi.2.trans (by norm_num))
  · exact table_target_bounds 19 d19_ell_low d19_ell_high (2.64150) ((2.64150+1/100000))
      (by norm_num [d19_ell_low]) hell (by norm_num [d19_ell_low]) (by norm_num [d19_ell_high])

theorem table3_rounding_20 :
    (((2.26424-1/100000) : ℝ) < majorant 20 ∧ majorant 20 ≤ 2.26424) ∧
      ((2.66476 : ℝ) ≤ target 20 ∧ target 20 < (2.66476+1/100000)) := by
  have helo := exp_bounds_from_eighth _ _ _ (by norm_num) d20_exp_ell_low
  have hehi := exp_bounds_from_eighth _ _ _ (by norm_num) d20_exp_ell_high
  have hzlo := exp_bounds_from_eighth _ _ _ (by norm_num) d20_exp_z_low
  have hzhi := exp_bounds_from_eighth _ _ _ (by norm_num) d20_exp_z_high
  have hloglo := exp_bounds_from_eighth _ _ _ (by norm_num) d20_exp_log_low
  have hloghi := exp_bounds_from_eighth _ _ _ (by norm_num) d20_exp_log_high
  have hulow := exp_bounds_from_eighth _ _ _ (by norm_num) d20_exp_u_low
  have huhi := exp_bounds_from_eighth _ _ _ (by norm_num) d20_exp_u_high
  have hell := table_log_interval 20 d20_ell_low d20_ell_high (by norm_num [d20_ell_low]) (by norm_num)
    ⟨helo.2.trans (by norm_num), le_trans (by norm_num) hehi.1⟩
  have hcomp := table_complement_interval 20 (by norm_num) d20_ell_low d20_ell_high
    d20_z_low d20_z_high d20_comp_low d20_comp_high (by norm_num [d20_ell_low]) hell
    (by norm_num [d20_z_low, d20_ell_low]) (by norm_num [d20_z_high, d20_ell_high])
    (le_trans (by norm_num [d20_comp_high]) hzlo.1)
    (hzhi.2.trans (by norm_num [d20_comp_low]))
  have hden := table_denominator_interval 20 (by norm_num)
    d20_comp_low d20_comp_high d20_log_low d20_log_high (by norm_num [d20_comp_low]) hcomp
    (hloglo.2.trans (by norm_num [d20_comp_low]))
    (le_trans (by norm_num [d20_comp_high]) hloghi.1)
  let denLower : ℝ := 4*((13862943606/10000000000 : ℝ)-d20_log_high/2)
  let denUpper : ℝ := 4*((13862943616/10000000000 : ℝ)-d20_log_low/2)
  have hu := table_majorant_exponent_interval 20 d20_ell_low d20_ell_high denLower denUpper
    d20_u_low d20_u_high (by norm_num [d20_ell_low]) hell
    (by norm_num [denLower, d20_log_high]) hden
    (by norm_num [d20_u_low, d20_ell_high, denLower, d20_log_high])
    (by norm_num [d20_u_high, d20_ell_low, denUpper, d20_log_low])
  constructor
  · exact table_majorant_bounds 20 d20_u_low d20_u_high ((2.26424-1/100000)) (2.26424) hu
      (lt_of_lt_of_le (by norm_num) hulow.1) (huhi.2.trans (by norm_num))
  · exact table_target_bounds 20 d20_ell_low d20_ell_high (2.66476) ((2.66476+1/100000))
      (by norm_num [d20_ell_low]) hell (by norm_num [d20_ell_low]) (by norm_num [d20_ell_high])

end SmaleRate.Proofs













