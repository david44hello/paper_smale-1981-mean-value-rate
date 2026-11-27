/-
SmaleRate — application of the explicit conformal coefficient upper fact.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.ExteriorMap
public import SmaleRate.Proofs.LeadingCoefficient

set_option backward.proofsInPublic true

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology

theorem capacity_exterior_upper_given_facts (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact)
    (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (hcritical : critical ≠ 0)
    (homit : critical ∉ inverse '' disk 1) :
    capacityTD (closure (exteriorImage inverse height critical)) ≤
      ‖critical‖ / (height * ‖deriv inverse 0‖) := by
  obtain ⟨hgeometry, hbase, hminusone⟩ := exterior_image_geometry_given_jordan hjordan
    inverse hinverse hzero height hheight critical hcritical homit
  have hconnected : IsConnected (exteriorImage inverse height critical) :=
    ⟨hgeometry.2.2.1, hgeometry.2.1⟩
  have hbase_disk : (0 : ℂ) ∈ disk 1 := by simp [disk]
  have hderiv_ne := univalent_deriv_ne_zero inverse hinverse 0 hbase_disk
  have hheight_ne : (height : ℂ) ≠ 0 := by exact_mod_cast hheight.1.ne'
  have hleading_ne : -critical / ((height : ℂ) * deriv inverse 0) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr hcritical) (mul_ne_zero hheight_ne hderiv_ne)
  have hupper := hcoefficient (closure (exteriorImage inverse height critical))
    hgeometry.2.2.2.1.isCompact_closure hconnected.closure
    ⟨0, subset_closure hbase, -1, subset_closure hminusone, by norm_num⟩
    (hjordan (exteriorImage inverse height critical) hgeometry).2
    (fun point : ℂ => inversion critical (inverse ((height : ℂ) / point)))
    (exterior_conformal_map_proved inverse hinverse hzero height hheight critical hcritical)
    (-critical / ((height : ℂ) * deriv inverse 0)) hleading_ne
    (capacity_phi_expansion_proved inverse hinverse hzero height hheight critical hcritical)
  simpa only [norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hheight.1] using hupper

end SmaleRate.Proofs


