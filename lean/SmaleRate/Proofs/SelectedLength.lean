/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.Elementary

noncomputable section
namespace SmaleRate.Proofs
open Set Filter
open scoped Topology

theorem selected_length_bounds (degree : ℕ) (hdegree : 8 ≤ degree) (hell : 8 ≤ ell degree) :
    0 < Real.pi^2/(2*(ell degree)^2) ∧
      Real.pi^2/(2*(ell degree)^2) ≤ 1 ∧
      Real.pi^2/(2*(ell degree)^2) < (degree : ℝ) := by
  have hd : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have he : 0 < ell degree := by linarith
  have hpi : Real.pi^2 < (16 : ℝ) := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hbound : Real.pi^2/(2*(ell degree)^2) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    nlinarith
  exact ⟨by positivity, hbound, hbound.trans_lt (by linarith)⟩

theorem selected_lambda_upper (degree : ℕ) (hdegree : 8 ≤ degree) (hell : 8 ≤ ell degree) :
    lambda degree (Real.pi^2/(2*(ell degree)^2)) ≤ ell degree + 4*Real.log (ell degree) := by
  have hd : (8 : ℝ) ≤ degree := by exact_mod_cast hdegree
  have hdpos : 0 < (degree : ℝ) := by linarith
  have he : 0 < ell degree := by linarith
  let length : ℝ := Real.pi^2/(2*(ell degree)^2)
  have hlength := selected_length_bounds degree hdegree hell
  have hlpos : 0 < length := hlength.1
  have hlone : length ≤ 1 := hlength.2.1
  have hratio : length/(degree : ℝ) ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ hdpos).2
    linarith
  have hden : 1/(ell degree)^2 ≤ length*(1-length/(degree : ℝ)) := by
    have hhalf : 1/(ell degree)^2 ≤ length/2 := by
      dsimp [length]
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*(ell degree)^2)).2
      have hid : 1/(ell degree)^2*2*(2*(ell degree)^2) = (4 : ℝ) := by field_simp; ring
      rw [hid]
      nlinarith [Real.pi_gt_three, Real.pi_pos]
    exact hhalf.trans (by nlinarith [mul_nonneg hlpos.le (by linarith : 0 ≤ 1/2-length/(degree : ℝ))])
  have hdenpos : 0 < length*(1-length/(degree : ℝ)) := by
    exact (by positivity : (0 : ℝ) < 1/(ell degree)^2).trans_le hden
  have hargument : 8*(degree : ℝ)/(length*(1-length/(degree : ℝ))) ≤
      8*(degree : ℝ)/(1/(ell degree)^2) := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have hid : 8*(degree : ℝ)/(1/(ell degree)^2) = (degree : ℝ)*(8*(ell degree)^2) := by
    field_simp
    <;> ring
  have hlogid : Real.log (8*(degree : ℝ)/(1/(ell degree)^2)) =
      ell degree+Real.log 8+2*Real.log (ell degree) := by
    rw [hid, Real.log_mul (ne_of_gt hdpos) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    simp only [ell, Nat.cast_ofNat]
    ring
  have hlog : Real.log 8 ≤ Real.log (ell degree) := Real.log_le_log (by norm_num) hell
  have hlogpos : 0 ≤ Real.log (ell degree) := Real.log_nonneg (by linarith)
  change Real.log (8*(degree : ℝ)/(length*(1-length/(degree : ℝ)))) ≤ _
  have hmono := Real.log_le_log (by positivity :
    (0 : ℝ) < 8*(degree : ℝ)/(length*(1-length/(degree : ℝ)))) hargument
  rw [hlogid] at hmono
  linarith

theorem selected_exponent_upper (degree : ℕ) (hdegree : 8 ≤ degree) (hell : 8 ≤ ell degree)
    (hlambda : 0 < lambda degree (Real.pi^2/(2*(ell degree)^2))) :
    Real.pi^2/(2*(ell degree)^2)-Real.pi^2/(2*lambda degree (Real.pi^2/(2*(ell degree)^2))) ≤
      -Real.pi^2/(2*ell degree)+(3*Real.pi^2)*Real.log (ell degree)/(ell degree)^2 := by
  have he : 0 < ell degree := by linarith
  have hlog : 1 ≤ Real.log (ell degree) := by
    have hlogorder := Real.log_le_log (by norm_num : (0 : ℝ) < 8) hell
    linarith [finite_log_endpoints.1]
  have hrecip := reciprocal_lower_of_interval (ell degree) (4*Real.log (ell degree))
    (ell degree+4*Real.log (ell degree)) he (by linarith) ⟨by linarith, le_rfl⟩
  have hone : 1/(ell degree+4*Real.log (ell degree)) ≤
      1/lambda degree (Real.pi^2/(2*(ell degree)^2)) :=
    one_div_le_one_div_of_le hlambda (selected_lambda_upper degree hdegree hell)
  have hscaled := mul_le_mul_of_nonneg_left (hrecip.trans hone)
    (by positivity : (0 : ℝ) ≤ Real.pi^2/2)
  have hquotient : Real.pi^2/(2*ell degree)-2*Real.pi^2*Real.log (ell degree)/(ell degree)^2 ≤
      Real.pi^2/(2*lambda degree (Real.pi^2/(2*(ell degree)^2))) := by
    convert hscaled using 1 <;> ring
  have hcoef : Real.pi^2/(2*(ell degree)^2) ≤ Real.pi^2*Real.log (ell degree)/(ell degree)^2 := by
    rw [show Real.pi^2/(2*(ell degree)^2) = (Real.pi^2/2)/(ell degree)^2 by ring]
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos he)).2
    nlinarith [sq_nonneg Real.pi, mul_nonneg (sq_nonneg Real.pi) (by linarith : 0 ≤ Real.log (ell degree)-1)]
  have hid : (3*Real.pi^2)*Real.log (ell degree)/(ell degree)^2 =
      2*Real.pi^2*Real.log (ell degree)/(ell degree)^2 +
      Real.pi^2*Real.log (ell degree)/(ell degree)^2 := by ring
  rw [hid]
  simp only [neg_div]
  linarith

section DLMF
variable (hdlmf : ∀ value : ℝ, value ∈ Ioo 0 1 →
  Real.log ((1 + Real.sqrt (complement value))^2 / value) < mu value ∧
    mu value < Real.log (2*(1+complement value)/value))
include hdlmf

theorem prop_selected_L_from_dlmf : ∃ constant ≥ (0 : ℝ), ∀ᶠ degree : ℕ in atTop,
    beta degree (Real.pi^2/(2*(ell degree)^2)) ≤
      4*Real.exp (-Real.pi^2/(2*ell degree)+constant*Real.log (ell degree)/(ell degree)^2) := by
  refine ⟨3*Real.pi^2, by positivity, ?_⟩
  have htop : Tendsto ell atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (8 : ℕ), htop.eventually_ge_atTop 8] with degree hdegree hell
  have hlength := selected_length_bounds degree hdegree hell
  have hgeneral := general_L_majorant_from_dlmf hdlmf degree (by omega)
    (Real.pi^2/(2*(ell degree)^2)) ⟨hlength.1, hlength.2.2⟩
  exact hgeneral.2.2.trans (by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
    exact Real.exp_le_exp.mpr (selected_exponent_upper degree hdegree hell hgeneral.1))

end DLMF
end SmaleRate.Proofs


