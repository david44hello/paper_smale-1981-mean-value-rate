/-
SmaleRate — leading coefficient of the exterior conformal map.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.PoleCancellation
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology

theorem capacity_phi_expansion_proved (inverse : ℂ → ℂ)
    (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (_hcritical : critical ≠ 0) :
    ∃ constant : ℂ, Tendsto (fun point : ℂ =>
      inversion critical (inverse ((height : ℂ) / point)) -
        (-critical / ((height : ℂ) * deriv inverse 0)) * point)
      (cocompact ℂ) (𝓝 constant) := by
  have hbase : (0 : ℂ) ∈ disk 1 := by simp [disk]
  have hheight_ne : (height : ℂ) ≠ 0 := by exact_mod_cast hheight.1.ne'
  have hderiv_ne := univalent_deriv_ne_zero inverse hinverse 0 hbase
  let divided := dslope inverse 0
  let reciprocal : ℂ → ℂ := fun point => (divided point)⁻¹
  have hdivided_diff : DifferentiableOn ℂ divided (disk 1) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds hbase)).mpr hinverse.1
  have hreciprocal_diff : DifferentiableAt ℂ reciprocal 0 :=
    (hdivided_diff.differentiableAt (isOpen_ball.mem_nhds hbase)).inv
      (by simpa only [divided, dslope_same] using hderiv_ne)
  have hcont : ContinuousAt (dslope reciprocal 0) 0 :=
    continuousAt_dslope_same.mpr hreciprocal_diff
  have harg_limit : Tendsto (fun point : ℂ => (height : ℂ) / point) (cocompact ℂ) (𝓝 0) := by
    have hinv : Tendsto (fun point : ℂ => point⁻¹) (cocompact ℂ) (𝓝 0) := by
      simpa only [← Metric.cobounded_eq_cocompact] using
        (Filter.tendsto_inv₀_cobounded : Tendsto (fun point : ℂ => point⁻¹)
          (Bornology.cobounded ℂ) (𝓝 0))
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hinv : Tendsto (fun point : ℂ => (height : ℂ) * point⁻¹)
        (cocompact ℂ) (𝓝 ((height : ℂ) * 0)))
  refine ⟨-critical * deriv reciprocal 0, ?_⟩
  have hlimit : Tendsto (fun point : ℂ => -critical * dslope reciprocal 0 ((height : ℂ) / point))
      (cocompact ℂ) (𝓝 (-critical * deriv reciprocal 0)) := by
    simpa only [dslope_same, Function.comp_def] using
      tendsto_const_nhds.mul (hcont.tendsto.comp harg_limit)
  apply hlimit.congr'
  have hpoint_ne : ∀ᶠ point : ℂ in cocompact ℂ, point ≠ 0 := by
    exact (isCompact_singleton : IsCompact ({0} : Set ℂ)).compl_mem_cocompact
  filter_upwards [hpoint_ne, harg_limit.eventually (isOpen_ball.mem_nhds hbase)] with
    point hpoint_ne harg_disk
  have harg_ne : (height : ℂ) / point ≠ 0 := div_ne_zero hheight_ne hpoint_ne
  have hinverse_ne : inverse ((height : ℂ) / point) ≠ 0 := by
    intro heq
    exact harg_ne (hinverse.2 harg_disk hbase (heq.trans hzero.symm))
  have hdivided_formula : divided ((height : ℂ) / point) =
      inverse ((height : ℂ) / point) / ((height : ℂ) / point) := by
    dsimp only [divided]
    rw [dslope_of_ne _ harg_ne]
    simp [slope, hzero, div_eq_mul_inv, mul_comm]
  have hreciprocal_formula : reciprocal ((height : ℂ) / point) =
      ((height : ℂ) / point) / inverse ((height : ℂ) / point) := by
    dsimp only [reciprocal]
    rw [hdivided_formula]
    simp [div_eq_mul_inv, mul_comm]
  have hreciprocal_zero : reciprocal 0 = (deriv inverse 0)⁻¹ := by
    simp only [reciprocal, divided, dslope_same]
  rw [dslope_of_ne _ harg_ne]
  simp only [slope, vsub_eq_sub, sub_zero, smul_eq_mul, hreciprocal_formula,
    hreciprocal_zero, inversion]
  field_simp [hpoint_ne, hheight_ne, hderiv_ne, hinverse_ne]
  <;> ring

end SmaleRate.Proofs


