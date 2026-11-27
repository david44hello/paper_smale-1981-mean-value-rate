/-
SmaleRate — cancellation of the polynomial pole.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.UnivalentDerivative
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology Polynomial

theorem univalent_dslope_ne_zero (func : ℂ → ℂ) (hfunc : IsUnivalentOn func (disk 1))
    (hzero : func 0 = 0) (point : ℂ) (hpoint : point ∈ disk 1) : dslope func 0 point ≠ 0 := by
  by_cases hpoint_zero : point = 0
  · subst point
    simpa using univalent_deriv_ne_zero func hfunc 0 hpoint
  · have hfunc_point : func point ≠ 0 := by
      intro heq
      have hbase : (0 : ℂ) ∈ disk 1 := by simp [disk]
      exact hpoint_zero (hfunc.2 hpoint hbase (heq.trans hzero.symm))
    rw [dslope_of_ne _ hpoint_zero]
    simpa [slope, hzero] using mul_ne_zero (inv_ne_zero hpoint_zero) hfunc_point

theorem polynomial_pole_cancellation (degree : ℕ) (poly : ℂ[X]) (hdegree : poly.natDegree = degree)
    (critical : ℂ) (hcritical : critical ≠ 0)
    (func : ℂ → ℂ) (hfunc : IsUnivalentOn func (disk 1)) (hzero : func 0 = 0) :
    ∃ extension : ℂ → ℂ, DifferentiableOn ℂ extension (disk 1) ∧
      ∀ point ∈ disk 1, point ≠ 0 →
        extension point = point^degree * poly.eval (inversion critical (func point)) := by
  have hbase : (0 : ℂ) ∈ disk 1 := by simp [disk]
  have hdslope_diff : DifferentiableOn ℂ (dslope func 0) (disk 1) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds hbase)).mpr hfunc.1
  let extension : ℂ → ℂ := fun point =>
    (-critical / dslope func 0 point)^degree * poly.reverse.eval (-func point / critical)
  have hconstant : DifferentiableOn ℂ (fun _ : ℂ => -critical) (disk 1) := by fun_prop
  refine ⟨extension, ?_, ?_⟩
  · exact ((hconstant.div hdslope_diff
      (fun point hpoint => univalent_dslope_ne_zero func hfunc hzero point hpoint)).pow degree).mul
      (poly.reverse.differentiable.comp_differentiableOn (hfunc.1.neg.div_const critical))
  · intro point hpoint hpoint_ne
    have hfunc_ne : func point ≠ 0 := by
      intro heq
      exact hpoint_ne (hfunc.2 hpoint hbase (heq.trans hzero.symm))
    let argument : ℂ := -critical / func point
    have hargument : argument ≠ 0 := div_ne_zero (neg_ne_zero.mpr hcritical) hfunc_ne
    letI : Invertible argument := invertibleOfNonzero hargument
    have hreverse : poly.reverse.eval argument⁻¹ * argument^degree = poly.eval argument := by
      simpa only [eval₂_id, invOf_eq_inv, hdegree] using
        eval₂_reverse_mul_pow (RingHom.id ℂ) argument poly
    have hreciprocal : argument⁻¹ = -func point / critical := by
      dsimp [argument]
      field_simp
    have hdslope : dslope func 0 point = func point / point := by
      rw [dslope_of_ne _ hpoint_ne]
      simp [slope, hzero, div_eq_mul_inv, mul_comm]
    have hfactor : -critical / dslope func 0 point = point * argument := by
      rw [hdslope]
      dsimp [argument]
      field_simp
    dsimp [extension]
    rw [hfactor, mul_pow, ← hreciprocal]
    change point^degree * argument^degree * poly.reverse.eval argument⁻¹ =
      point^degree * poly.eval argument
    rw [mul_assoc, mul_comm (argument^degree), hreverse]

end SmaleRate.Proofs


