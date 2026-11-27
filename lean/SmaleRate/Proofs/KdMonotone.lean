/-
SmaleRate — bridge earlier Smale degree monotonicity to the actual quotient.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Legacy009.Lemma53
import SmaleRate.Proofs.PolynomialBasics
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology Polynomial

theorem legacy_ratios_eq_general (poly : ℂ[X]) (hderivative : poly.derivative.eval 0 = 1) :
    Legacy009.critRatios poly = criticalRatios poly := by
  ext value
  constructor
  · rintro ⟨point, hpoint, rfl⟩
    refine ⟨point, hpoint, ?_⟩
    simp only [criticalRatio, hderivative, mul_one, norm_div]
  · rintro ⟨point, hpoint, rfl⟩
    refine ⟨point, hpoint, ?_⟩
    simp only [criticalRatio, hderivative, mul_one, norm_div]

theorem legacy_mval_eq_S (poly : ℂ[X]) (hderivative : poly.derivative.eval 0 = 1) :
    Legacy009.mval poly = S poly := by
  unfold Legacy009.mval S
  rw [legacy_ratios_eq_general poly hderivative]

theorem legacy_isPd_to_general (degree : ℕ) (poly : ℂ[X]) (hpoly : Legacy009.IsPd degree poly) :
    IsPd degree poly := by
  refine ⟨hpoly.1, hpoly.2.1, ?_⟩
  rw [hpoly.2.2]
  exact one_ne_zero

/-- Divide by the actual nonzero derivative. The normalized legacy minimum equals the
original project's quotient minimum, rather than the unnormalized norm ratio. -/
theorem derivative_normalized_legacy (degree : ℕ) (poly : ℂ[X]) (hpoly : IsPd degree poly) :
    Legacy009.IsPd degree (C (poly.derivative.eval 0)⁻¹ * poly) ∧
      Legacy009.mval (C (poly.derivative.eval 0)⁻¹ * poly) = S poly := by
  have hscalar : (poly.derivative.eval 0)⁻¹ ≠ 0 := inv_ne_zero hpoly.2.2
  have hscaled := scaled_isPd degree poly hpoly (poly.derivative.eval 0)⁻¹ hscalar
  have hderivative : (C (poly.derivative.eval 0)⁻¹ * poly).derivative.eval 0 = 1 := by
    simp only [derivative_C_mul, eval_C_mul]
    exact inv_mul_cancel₀ hpoly.2.2
  exact ⟨⟨hscaled.1, hscaled.2.1, hderivative⟩,
    (legacy_mval_eq_S _ hderivative).trans (scaled_S poly _ hscalar)⟩

theorem kd_eq_legacy (degree : ℕ) : Kd degree = Legacy009.Kd degree := by
  apply le_antisymm
  · unfold Kd Legacy009.Kd
    apply iSup_le
    intro poly
    obtain ⟨hnormalized, hminimum⟩ := derivative_normalized_legacy degree poly.val poly.property
    calc
      ((S poly.val : ℝ) : EReal) =
          ((Legacy009.mval (C (poly.val.derivative.eval 0)⁻¹ * poly.val) : ℝ) : EReal) := by
        exact congrArg (fun value : ℝ => (value : EReal)) hminimum.symm
      _ ≤ ⨆ normalized : {normalized : ℂ[X] // Legacy009.IsPd degree normalized},
          ((Legacy009.mval normalized.val : ℝ) : EReal) :=
        le_iSup (fun normalized : {normalized : ℂ[X] // Legacy009.IsPd degree normalized} =>
          ((Legacy009.mval normalized.val : ℝ) : EReal)) ⟨_, hnormalized⟩
  · unfold Legacy009.Kd Kd
    apply iSup_le
    intro poly
    calc
      ((Legacy009.mval poly.val : ℝ) : EReal) = ((S poly.val : ℝ) : EReal) :=
        congrArg (fun value : ℝ => (value : EReal)) (legacy_mval_eq_S poly.val poly.property.2.2)
      _ ≤ ⨆ general : {general : ℂ[X] // IsPd degree general}, ((S general.val : ℝ) : EReal) :=
        le_iSup (fun general : {general : ℂ[X] // IsPd degree general} =>
          ((S general.val : ℝ) : EReal)) ⟨poly.val, legacy_isPd_to_general degree poly.val poly.property⟩

theorem kd_succ_le_proved (degree : ℕ) (hdegree : 2 ≤ degree) : Kd degree ≤ Kd (degree + 1) := by
  rw [kd_eq_legacy degree, kd_eq_legacy (degree + 1)]
  exact Legacy009.lem_5_3_proved degree hdegree

theorem kd_monotone_proved : MonotoneOn Kd (Ici 2) :=
  monotoneOn_nat_Ici_of_le_succ kd_succ_le_proved

end SmaleRate.Proofs

#check SmaleRate.Proofs.derivative_normalized_legacy
#check SmaleRate.Proofs.kd_eq_legacy
#check SmaleRate.Proofs.kd_monotone_proved
#print axioms SmaleRate.Legacy009.lem_5_3_proved
#print axioms SmaleRate.Proofs.derivative_normalized_legacy
#print axioms SmaleRate.Proofs.kd_eq_legacy
#print axioms SmaleRate.Proofs.kd_monotone_proved
