/-
SmaleRate — inverse branch through polynomial covering/lifting.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
-- Integrated by : proof declarations unchanged; trailing diagnostic commands removed.
module

public import SmaleRate.Defs.Basic

set_option backward.proofsInPublic true

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Polynomial Set Filter Metric Topology

theorem regular_values_disk (poly : ℂ[X]) (critical : ℂ)
    (hnormal : NormalizedCriticalValues poly critical) :
    ∀ point ∈ disk 1, point ∉ poly.eval '' {point | poly.derivative.eval point = 0} := by
  intro point hpoint hvalue
  obtain ⟨preimage, hcritical, heq⟩ := hvalue
  change poly.eval preimage = point at heq
  have hge := hnormal.2.2 preimage hcritical
  have hlt : ‖poly.eval preimage‖ < 1 := by
    rw [heq]
    exact mem_ball_zero_iff.mp hpoint
  exact (not_lt_of_ge hge) hlt

theorem inverse_derivative (poly : ℂ[X]) (critical : ℂ)
    (hnormal : NormalizedCriticalValues poly critical) (inverse : ℂ → ℂ)
    (hcontinuous : ContinuousOn inverse (disk 1))
    (hright : ∀ point ∈ disk 1, poly.eval (inverse point) = point)
    (point : ℂ) (hpoint : point ∈ disk 1) :
    HasStrictDerivAt inverse (poly.derivative.eval (inverse point))⁻¹ point := by
  have hne : poly.derivative.eval (inverse point) ≠ 0 := by
    intro hzero
    exact regular_values_disk poly critical hnormal point hpoint
      ⟨inverse point, hzero, hright point hpoint⟩
  apply HasStrictDerivAt.of_local_left_inverse
    (hcontinuous.continuousAt (isOpen_ball.mem_nhds hpoint)) (poly.hasStrictDerivAt _) hne
  filter_upwards [isOpen_ball.mem_nhds hpoint] with other hother
  exact hright other hother

theorem inverse_branch_exists_proved (degree : ℕ) (_hdegree : 2 ≤ degree) (poly : ℂ[X])
    (hpoly : IsPd degree poly) (critical : ℂ) (hnormal : NormalizedCriticalValues poly critical) :
    ∃ inverse : ℂ → ℂ, IsInverseBranch poly inverse := by
  classical
  have hzero : (0 : ℂ) ∈ disk 1 := by simp [disk]
  letI : ContractibleSpace (disk 1) :=
    (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, hzero⟩
  letI : SimplyConnectedSpace (disk 1) := inferInstance
  letI : LocallyPathConnectedSpace (disk 1) := isOpen_ball.locallyPathConnectedSpace
  let inclusion : C(disk 1, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨lift, ⟨hbase, hlift⟩, _⟩ :=
    poly.isCoveringMapOn_eval.existsUnique_continuousMap_lifts inclusion
      (a₀ := ⟨0, hzero⟩) (e₀ := 0) hpoly.2.1
      (fun point => regular_values_disk poly critical hnormal point.val point.property)
  obtain ⟨inverse, hextend⟩ : ∃ inverse : ℂ → ℂ, ∀ point : disk 1, inverse point = lift point :=
    ⟨fun point => if hpoint : point ∈ disk 1 then lift ⟨point, hpoint⟩ else 0, by simp⟩
  have hcontinuous : ContinuousOn inverse (disk 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert lift.continuous using 1
    ext point
    exact hextend point
  have hright : ∀ point ∈ disk 1, poly.eval (inverse point) = point := by
    intro point hpoint
    rw [hextend ⟨point, hpoint⟩]
    exact congrFun hlift ⟨point, hpoint⟩
  refine ⟨inverse, ?_, ?_, hright⟩
  · intro point hpoint
    exact (inverse_derivative poly critical hnormal inverse hcontinuous hright point hpoint).hasDerivAt.differentiableAt.differentiableWithinAt
  · rw [hextend ⟨0, hzero⟩]
    exact hbase

theorem inverse_univalent (poly : ℂ[X]) (inverse : ℂ → ℂ) (hinverse : IsInverseBranch poly inverse) :
    IsUnivalentOn inverse (disk 1) := by
  refine ⟨hinverse.1, ?_⟩
  intro first hfirst second hsecond heq
  calc
    first = poly.eval (inverse first) := (hinverse.2.2 first hfirst).symm
    _ = poly.eval (inverse second) := congrArg poly.eval heq
    _ = second := hinverse.2.2 second hsecond

theorem inverse_derivative_zero (poly : ℂ[X]) (critical : ℂ)
    (hnormal : NormalizedCriticalValues poly critical) (inverse : ℂ → ℂ)
    (hinverse : IsInverseBranch poly inverse) :
    deriv inverse 0 = (poly.derivative.eval 0)⁻¹ := by
  have hzero : (0 : ℂ) ∈ disk 1 := by simp [disk]
  simpa [hinverse.2.1] using
    (inverse_derivative poly critical hnormal inverse hinverse.1.continuousOn hinverse.2.2 0 hzero).hasDerivAt.deriv

theorem inverse_omits_critical (poly : ℂ[X]) (critical : ℂ)
    (hnormal : NormalizedCriticalValues poly critical) (inverse : ℂ → ℂ)
    (hinverse : IsInverseBranch poly inverse) : critical ∉ inverse '' disk 1 := by
  rintro ⟨point, hpoint, heq⟩
  have hvalue : poly.eval critical = point := by
    rw [← heq]
    exact hinverse.2.2 point hpoint
  have hnorm : ‖point‖ = 1 := by rw [← hvalue]; exact hnormal.2.1
  exact (ne_of_lt (mem_ball_zero_iff.mp hpoint)) hnorm

theorem inverse_branch_properties_of_ratio (degree : ℕ) (poly : ℂ[X]) (_hpoly : IsPd degree poly)
    (critical : ℂ) (hnormal : NormalizedCriticalValues poly critical)
    (inverse : ℂ → ℂ) (hinverse : IsInverseBranch poly inverse)
    (hminimum : S poly ≤ criticalRatio poly critical) :
    IsUnivalentOn inverse (disk 1) ∧ deriv inverse 0 = (poly.derivative.eval 0)⁻¹ ∧
    critical ∉ inverse '' disk 1 ∧ S poly ≤ ‖deriv inverse 0‖/‖critical‖ := by
  have hderivative := inverse_derivative_zero poly critical hnormal inverse hinverse
  refine ⟨inverse_univalent poly inverse hinverse, hderivative,
    inverse_omits_critical poly critical hnormal inverse hinverse, hminimum.trans_eq ?_⟩
  simp [criticalRatio, hderivative, norm_div, norm_mul, hnormal.2.1, div_eq_mul_inv, mul_comm]

end SmaleRate.Proofs
