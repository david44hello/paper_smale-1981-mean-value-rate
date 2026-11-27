/-
SmaleRate — formalized statements of the paper.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
Unproved rows remain explicit proof obligations listed in OPEN_ROWS.txt.
-/
module

public import SmaleRate.Defs.Basic
public import SmaleRate.Defs.AnalyticBackground
public import SmaleRate.Cited.Approved
public import SmaleRate.Cited.JatarNg
public import SmaleRate.Proofs.PolynomialBasics
public import SmaleRate.Proofs.InverseBranch
public import SmaleRate.Proofs.InverseGeometry
public import SmaleRate.Proofs.Elementary
public import SmaleRate.Proofs.UnivalentDerivative
public import SmaleRate.Proofs.ScalarBasics
public import SmaleRate.Proofs.BackgroundDeductions
public import SmaleRate.Proofs.EllipticOrder
public import SmaleRate.Proofs.MuLimits
public import SmaleRate.Proofs.PoleCancellation
public import SmaleRate.Proofs.XiFull
public import SmaleRate.Proofs.ExteriorJordan
public import SmaleRate.Proofs.DiameterMonotonicity
public import SmaleRate.Proofs.MainBound
public import SmaleRate.Proofs.YBoundLimits
public import SmaleRate.Proofs.GeometryCoverage
public import SmaleRate.Proofs.TableCertificates
public import SmaleRate.Proofs.MuApproximation
public import SmaleRate.Proofs.MuAsymptotics
public import SmaleRate.Proofs.AGMAnalytic
public import SmaleRate.Proofs.DiameterDecreasing
public import SmaleRate.Proofs.YBoundDegreeLimit
public import SmaleRate.Proofs.PolynomialWitness
public import SmaleRate.Proofs.SelectedLength
public import SmaleRate.Proofs.AsymptoticTransport
public import SmaleRate.Proofs.EarlierComparisons
public import SmaleRate.Proofs.BetsakosDerivative
public import SmaleRate.Proofs.ScalarIdentities
public import SmaleRate.Proofs.YBoundStrict
public import SmaleRate.Proofs.BetsakosCoverage
public import SmaleRate.Proofs.FiniteBoxSoundness
public import SmaleRate.Proofs.KdMonotone
public import SmaleRate.Proofs.CraneNumbers
public import SmaleRate.Proofs.FigureDotBounds
public import SmaleRate.Proofs.TailConstants
public import SmaleRate.Proofs.BoundOrders
public import SmaleRate.Proofs.PrintedCases
public import SmaleRate.Proofs.SmallMultiple
public import SmaleRate.Proofs.JnNormalization
public import SmaleRate.Proofs.PrintedTailStrict
public import SmaleRate.Proofs.JnLimit
public import SmaleRate.Proofs.TableEarlier
public import SmaleRate.Proofs.SevenAndRange
public import SmaleRate.Proofs.DiskGreen
public import SmaleRate.Proofs.TableTargets
public import SmaleRate.Proofs.JnBoundary
public import SmaleRate.Proofs.GreenExistence
public import SmaleRate.Proofs.JnBoundaryValues
public import SmaleRate.Proofs.JatarContext
public import SmaleRate.Proofs.AGMCertificates
public import SmaleRate.Proofs.Public030Bridge
public import SmaleRate.Proofs.ExteriorGeometryConcrete
public import SmaleRate.Proofs.GreenConformal
public import SmaleRate.Proofs.CapacityUpperConcrete
public import SmaleRate.Proofs.SmallDegreesConcrete
public import SmaleRate.Proofs.GreenInversion
public import SmaleRate.Proofs.GreenConformalDirect
public import SmaleRate.Proofs.QuarticPolynomial
public import SmaleRate.Proofs.Generated.CoverConsequences

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Paper
open SmaleRate Polynomial Filter Set MeasureTheory
open scoped Topology

/-- minimum_attained. -/
theorem minimum_attained (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly) :
    (criticalPoints poly).Finite ∧ (criticalPoints poly).Nonempty ∧
    ∃ point ∈ criticalPoints poly, S poly = criticalRatio poly point := by
  exact Proofs.minimum_attained_proved degree hdegree poly hpoly

/-- critical_nonzero. -/
theorem critical_nonzero (degree : ℕ) (poly : ℂ[X]) (hpoly : IsPd degree poly) :
    ∀ point ∈ criticalPoints poly, point ≠ 0 := by
  exact Proofs.critical_nonzero_proved degree poly hpoly

/-- critical_ratio_norm_formula. -/
theorem critical_ratio_norm_formula (poly : ℂ[X]) (point : ℂ) :
    criticalRatio poly point = ‖poly.eval point‖ / (‖point‖ * ‖poly.derivative.eval 0‖) := by
  exact Proofs.critical_ratio_norm_formula_proved poly point

/-- s_nonneg. -/
theorem s_nonneg (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly) : 0 ≤ S poly := by
  exact Proofs.s_nonneg_proved degree hdegree poly hpoly

/-- s_le_ratio. -/
theorem s_le_ratio (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (point : ℂ) (hpoint : point ∈ criticalPoints poly) : S poly ≤ criticalRatio poly point := by
  exact Proofs.s_le_ratio_proved degree hdegree poly hpoly point hpoint

/-- scalar_invariance. -/
theorem scalar_invariance (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (scalar : ℂ) (hscalar : scalar ≠ 0) :
    IsPd degree (Polynomial.C scalar * poly) ∧
    criticalPoints (Polynomial.C scalar * poly) = criticalPoints poly ∧
    S (Polynomial.C scalar * poly) = S poly := by
  exact Proofs.scalar_invariance_proved degree hdegree poly hpoly scalar hscalar

/-- zero_critical_value. -/
theorem zero_critical_value (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (point : ℂ) (hpoint : point ∈ criticalPoints poly) (hvalue : poly.eval point = 0) : S poly = 0 := by
  exact Proofs.zero_critical_value_proved degree hdegree poly hpoly point hpoint hvalue

/-- critical_value_normalization. -/
theorem critical_value_normalization (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (hvalues : ∀ point ∈ criticalPoints poly, poly.eval point ≠ 0) :
    ∃ scalar : ℝ, 0 < scalar ∧ ∃ point : ℂ,
      NormalizedCriticalValues (Polynomial.C (scalar : ℂ) * poly) point := by
  exact Proofs.critical_value_normalization_proved degree hdegree poly hpoly hvalues

/-- kd_finite. -/
theorem kd_finite (degree : ℕ) (hdegree : 2 ≤ degree) : Kd degree ≠ ⊥ ∧ Kd degree ≠ ⊤ := by
  exact Proofs.kd_finite_public030 degree hdegree

/-- smale_bound. -/
theorem smale_bound (degree : ℕ) (hdegree : 2 ≤ degree) : Kd degree ≤ (4 : EReal) := by
  exact Proofs.smale_bound_public030 degree hdegree

/-- small_degrees. -/
theorem small_degrees (degree : ℕ) (hdegree : 2 ≤ degree) (hupper : degree ≤ 4) :
    Kd degree = (((degree : ℝ) - 1) / degree : ℝ) := by
  exact Proofs.small_degrees_proved degree hdegree hupper

/-- small_degrees_two_three. -/
theorem small_degrees_two_three (degree : ℕ) (hdegree : 2 ≤ degree) (hupper : degree ≤ 3) :
    Kd degree = (((degree : ℝ) - 1) / degree : ℝ) := by
  exact Proofs.small_degrees_two_three degree hdegree hupper

/-- counterexample_exists. -/
theorem counterexample_exists : ∃ degree : ℕ, 2 ≤ degree ∧ (1 : EReal) < Kd degree := by
  exact Proofs.counterexample_exists_public030

/-- counterexample_explicit_degree. -/
theorem counterexample_explicit_degree : (1 : EReal) < Kd 29984 := by
  sorry

/-- jatar_ng_lower. -/
theorem jatar_ng_lower : ((11018 / 10000 : ℝ) : EReal) < Kstar := by
  exact Proofs.jatar_ng_lower_public030

/-- kd_monotone. -/
theorem kd_monotone : MonotoneOn Kd (Set.Ici 2) := by
  exact Proofs.kd_monotone_proved

/-- kd_limit_and_sup. -/
theorem kd_limit_and_sup : Tendsto Kd atTop (𝓝 (4 : EReal)) ∧ Kstar = 4 := by
  exact Proofs.kd_limit_and_sup_public030

/-- earlier_bounds. -/
theorem earlier_bounds (degree : ℕ) (hdegree : 2 ≤ degree) :
    Kd degree ≤ (beardon degree : EReal) ∧ Kd degree ≤ (conte degree : EReal) ∧
    Kd degree ≤ (fujikawa degree : EReal) ∧ Kd degree ≤ (dubinin degree : EReal) := by
  sorry

/-- crane_bound. -/
theorem crane_bound (degree : ℕ) (hdegree : 8 ≤ degree) : Kd degree < (crane degree : EReal) := by
  sorry

/-- expanded_lower_bound. -/
theorem expanded_lower_bound (degree : ℕ) (hdegree : 2 ≤ degree) : Kd degree ≤ ((4 - expandedLower degree : ℝ) : EReal) := by
  sorry

/-- expanded_upper_bound. -/
theorem expanded_upper_bound (degree : ℕ) (hdegree : Real.exp (104 * (10 : ℝ)^8) ≤ (degree : ℝ)) :
    ((4 - expandedUpper degree : ℝ) : EReal) ≤ Kd degree := by
  sorry

/-- expanded_crossover. -/
theorem expanded_crossover (degree : ℕ) (hdegree : 2 ≤ degree) (hlog : ell degree ≤ 36363) :
    expandedLower degree < 4 / ell degree := by
  have hd : (1 : ℝ) < degree := by exact_mod_cast (show 1 < degree by omega)
  have hell : 0 < ell degree := Real.log_pos hd
  have hmin : expandedLower degree ≤ (11/100000 : ℝ) := min_le_left _ _
  apply hmin.trans_lt
  apply (lt_div_iff₀ hell).2
  nlinarith

/-- elliptic_integrable. -/
theorem elliptic_integrable (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) :
    IntervalIntegrable (fun param : ℝ => 1 / Real.sqrt ((1-param^2)*(1-modulus^2*param^2))) volume 0 1 := by
  exact Proofs.elliptic_integrable_of_mu_positive modulus
    (Proofs.mu_positive_of_lower_dlmf modulus hmodulus (Cited.dlmf_19_9_5 modulus hmodulus).1)

/-- elliptic_positive. -/
theorem elliptic_positive (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) : 0 < ellipticK modulus := by
  exact Proofs.ellipticK_positive_of_mu_positive modulus
    (Proofs.mu_positive_of_lower_dlmf modulus hmodulus (Cited.dlmf_19_9_5 modulus hmodulus).1)

/-- elliptic_increasing. -/
theorem elliptic_increasing : StrictMonoOn ellipticK (Ioo 0 1) := by
  exact Proofs.elliptic_increasing_of_mu_positive (fun modulus hmodulus =>
    Proofs.mu_positive_of_lower_dlmf modulus hmodulus (Cited.dlmf_19_9_5 modulus hmodulus).1)

/-- elliptic_continuous. -/
theorem elliptic_continuous : ContinuousOn ellipticK (Ioo 0 1) := by
  intro modulus hmodulus
  exact (Proofs.ellipticK_continuousAt_of_positive (fun value hvalue =>
    Proofs.mu_positive_of_lower_dlmf value hvalue (Cited.dlmf_19_9_5 value hvalue).1)
    modulus hmodulus).continuousWithinAt

/-- elliptic_endpoints. -/
theorem elliptic_endpoints : Tendsto ellipticK (𝓝[>] 0) (𝓝 (Real.pi/2)) ∧
    Tendsto ellipticK (𝓝[<] 1) atTop := by
  exact Proofs.elliptic_endpoints_from_dlmf Cited.dlmf_19_8_5
    (fun modulus hmodulus => (Cited.dlmf_19_9_5 modulus hmodulus).1)

/-- mu_decreasing. -/
theorem mu_decreasing : StrictAntiOn mu (Ioo 0 1) := by
  exact Proofs.mu_decreasing_of_positive (fun modulus hmodulus =>
    Proofs.mu_positive_of_lower_dlmf modulus hmodulus (Cited.dlmf_19_9_5 modulus hmodulus).1)

/-- mu_range. -/
theorem mu_range : mu '' Ioo 0 1 = Ioi 0 := by
  exact Proofs.mu_range_from_lower_dlmf (fun value hvalue => (Cited.dlmf_19_9_5 value hvalue).1)

/-- mu_continuous. -/
theorem mu_continuous : ContinuousOn mu (Ioo 0 1) := by
  intro modulus hmodulus
  exact (Proofs.mu_continuousAt_of_positive (fun value hvalue =>
    Proofs.mu_positive_of_lower_dlmf value hvalue (Cited.dlmf_19_9_5 value hvalue).1)
    modulus hmodulus).continuousWithinAt

/-- mu_positive. -/
theorem mu_positive (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) : 0 < mu modulus := by
  exact Proofs.mu_positive_of_lower_dlmf modulus hmodulus (Cited.dlmf_19_9_5 modulus hmodulus).1

/-- mu_endpoints. -/
theorem mu_endpoints : Tendsto mu (𝓝[>] 0) atTop ∧ Tendsto mu (𝓝[<] 1) (𝓝 0) := by
  exact Proofs.mu_endpoints_from_lower_dlmf (fun value hvalue => (Cited.dlmf_19_9_5 value hvalue).1)

/-- mu_complement. -/
theorem mu_complement (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) :
    mu modulus * mu (complement modulus) = Real.pi^2/4 := by
  exact Proofs.mu_complement_of_positive modulus hmodulus (mu_positive modulus hmodulus)
    (mu_positive (complement modulus) (Proofs.complement_mem modulus hmodulus))

/-- dlmf_19_9_5. -/
theorem dlmf_19_9_5 (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) :
    Real.log ((1+Real.sqrt (complement modulus))^2/modulus) < mu modulus ∧
    mu modulus < Real.log (2*(1+complement modulus)/modulus) := by
  exact SmaleRate.Cited.dlmf_19_9_5 modulus hmodulus

/-- mu_log_upper. -/
theorem mu_log_upper (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) : mu modulus < Real.log (4/modulus) := by
  exact Proofs.mu_log_upper_of_upper_dlmf modulus hmodulus (Cited.dlmf_19_9_5 modulus hmodulus).2

/-- mu_small_error. -/
theorem mu_small_error : ∃ constant ≥ (0 : ℝ), ∀ᶠ modulus in 𝓝[>] (0 : ℝ),
    |mu modulus - Real.log (4/modulus)| ≤ constant * modulus^2 := by
  exact Proofs.mu_small_error_from_dlmf Cited.dlmf_19_9_5

/-- mu_near_one. -/
theorem mu_near_one : Tendsto (fun modulus : ℝ => mu modulus /
    (Real.pi^2/(2*Real.log (16/(1-modulus^2))))) (𝓝[<] 1) (𝓝 1) := by
  exact Proofs.mu_near_one_from_dlmf Cited.dlmf_19_9_5

/-- thm_1_1. -/
theorem thm_1_1 (degree : ℕ) (hdegree : 2 ≤ degree) (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    Kd degree ≤ (yBound degree height : EReal) := by
  sorry

/-- cor_1_2. -/
theorem cor_1_2 (degree : ℕ) (hdegree : 8 ≤ degree) : Kd degree < (target degree : EReal) := by
  sorry

/-- ybound_at_zero. -/
theorem ybound_at_zero (degree : ℕ) (hdegree : 2 ≤ degree) : Tendsto (yBound degree) (𝓝[>] 0) atTop := by
  exact Proofs.ybound_at_zero_from_log_upper mu_log_upper degree hdegree

/-- ybound_at_one. -/
theorem ybound_at_one (degree : ℕ) (hdegree : 2 ≤ degree) : Tendsto (yBound degree) (𝓝[<] 1) (𝓝 4) := by
  exact Proofs.ybound_at_one_from_mu_limit mu_endpoints.2 degree hdegree

/-- ybound_below_four_near_one. -/
theorem ybound_below_four_near_one (degree : ℕ) (hdegree : 2 ≤ degree) : ∀ᶠ height in 𝓝[<] (1 : ℝ), yBound degree height < 4 := by
  exact Proofs.ybound_below_four_near_one_from_dlmf
    (fun modulus hmodulus => (Cited.dlmf_19_9_5 modulus hmodulus).1) degree hdegree

/-- kd_lt_four. -/
theorem kd_lt_four (degree : ℕ) (hdegree : 2 ≤ degree) : Kd degree < (4 : EReal) := by
  exact Proofs.kd_lt_four_public030 degree hdegree

/-- ybound_fixed_y_limit. -/
theorem ybound_fixed_y_limit (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    Tendsto (fun degree : ℕ => yBound degree height) atTop (𝓝 (4/height)) := by
  exact Proofs.ybound_fixed_y_limit_from_mu_limit mu_endpoints.2 height hheight

/-- degree_example_39. -/
theorem degree_example_39 (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (hlarge : 39/10 ≤ S poly) : 2 * 10^17 < degree := by
  sorry

/-- inverse_branch_exists. -/
theorem inverse_branch_exists (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (critical : ℂ) (hnormal : NormalizedCriticalValues poly critical) :
    ∃ inverse : ℂ → ℂ, IsInverseBranch poly inverse := by
  exact Proofs.inverse_branch_exists_proved degree hdegree poly hpoly critical hnormal

/-- inverse_branch_properties. -/
theorem inverse_branch_properties (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (critical : ℂ) (hnormal : NormalizedCriticalValues poly critical)
    (inverse : ℂ → ℂ) (hinverse : IsInverseBranch poly inverse) :
    IsUnivalentOn inverse (disk 1) ∧ deriv inverse 0 = (poly.derivative.eval 0)⁻¹ ∧
    critical ∉ inverse '' disk 1 ∧ S poly ≤ ‖deriv inverse 0‖/‖critical‖ := by
  exact Proofs.inverse_branch_properties_of_ratio degree poly hpoly critical hnormal inverse hinverse
    (Proofs.s_le_ratio_proved degree hdegree poly hpoly critical hnormal.1)

/-- inverse_jordan_domain. -/
theorem inverse_jordan_domain (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    IsBoundedJordanDomain (inverseDomain inverse height) ∧
    closure (inverseDomain inverse height) = inverse '' Metric.closedBall 0 height ∧
    closure (inverseDomain inverse height) ⊆ inverse '' disk 1 := by
  exact Proofs.inverse_jordan_domain_proved inverse hinverse hzero height hheight

/-- exterior_image_geometry. -/
theorem exterior_image_geometry (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (hcritical : critical ≠ 0)
    (homit : critical ∉ inverse '' disk 1) :
    IsBoundedJordanDomain (exteriorImage inverse height critical) ∧
    (0 : ℂ) ∈ exteriorImage inverse height critical ∧ (-1 : ℂ) ∈ exteriorImage inverse height critical := by
  exact Proofs.exterior_image_geometry_proved inverse hinverse hzero height hheight
    critical hcritical homit

/-- capacity_identity. -/
theorem capacity_identity (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (hcritical : critical ≠ 0)
    (homit : critical ∉ inverse '' disk 1) :
    capacityTD (closure (exteriorImage inverse height critical)) = ‖critical‖/(height*‖deriv inverse 0‖) := by
  sorry

/-- capacity_step_scalar. -/
theorem capacity_step_scalar (value height derivative critical cap : ℝ) (hvalue : 0 < value) (hheight : 0 < height)
    (hderivative : 0 < derivative) (hcritical : 0 < critical)
    (hbound : value ≤ derivative/critical) (hcap : cap = critical/(height*derivative)) : cap ≤ 1/(height*value) := by
  exact Proofs.capacity_step_scalar value height derivative critical cap
    hvalue hheight hderivative hcritical hbound hcap

/-- riemann_map_for_exterior. -/
theorem riemann_map_for_exterior (domain : Set ℂ) (hdomain : IsBoundedJordanDomain domain) (hzero : (0 : ℂ) ∈ domain) :
    ∃ func : ℂ → ℂ, IsConformalOnto func (disk 1) domain ∧ func 0 = 0 := by
  sorry

/-- xi_bound. -/
theorem xi_bound (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (critical : ℂ) (hnormal : NormalizedCriticalValues poly critical)
    (inverse : ℂ → ℂ) (hinverse : IsInverseBranch poly inverse)
    (height : ℝ) (hheight : height ∈ Ioo 0 1)
    (func : ℂ → ℂ) (hfunc : IsConformalOnto func (disk 1) (exteriorImage inverse height critical))
    (hzero : func 0 = 0) (xi : ℂ) (hxi : xi ∈ disk 1) (hminusone : func xi = -1) :
    xi ≠ 0 ∧ ‖xi‖ ≤ height ^ (1/(degree : ℝ)) := by
  exact Proofs.xi_bound_proved degree hdegree poly hpoly critical hnormal inverse hinverse
    height hheight func hfunc hzero xi hxi hminusone

/-- betsakos_inequality. -/
theorem betsakos_inequality (func : ℂ → ℂ) (hhol : DifferentiableOn ℂ func (disk 1))
    (hbound : Bornology.IsBounded (func '' disk 1)) (hzero : func 0 = 0)
    (hnonconstant : ∃ first ∈ disk 1, ∃ second ∈ disk 1, func first ≠ func second)
    (point : ℂ) (hpoint : point ∈ disk 1) (hnonzero : point ≠ 0) :
    ‖func point‖ ≤ 4*transfiniteDiameter (func '' disk 1)*Real.exp (-mu ‖point‖) := by
  exact SmaleRate.Cited.betsakos_2013 func hhol hbound hzero hnonconstant point hpoint hnonzero

/-- betsakos_equality. -/
theorem betsakos_equality (func : ℂ → ℂ) (hhol : DifferentiableOn ℂ func (disk 1))
    (hbound : Bornology.IsBounded (func '' disk 1)) (hzero : func 0 = 0)
    (point : ℂ) (hpoint : point ∈ disk 1) (hnonzero : point ≠ 0)
    (hnonconstant : ∃ first ∈ disk 1, ∃ second ∈ disk 1, func first ≠ func second) :
    (‖func point‖ = 4*transfiniteDiameter (func '' disk 1)*Real.exp (-mu ‖point‖)) ↔
    (IsUnivalentOn func (disk 1) ∧ ∃ major : ℝ, ‖func point‖ < major ∧
      func '' disk 1 = {value | ‖value‖ + ‖value-func point‖ < major}) := by
  sorry

/-- betsakos_derivative. -/
theorem betsakos_derivative (func : ℂ → ℂ) (hhol : DifferentiableOn ℂ func (disk 1))
    (hbound : Bornology.IsBounded (func '' disk 1)) (hzero : func 0 = 0) :
    ‖deriv func 0‖ ≤ transfiniteDiameter (func '' disk 1) := by
  exact Proofs.betsakos_derivative_from_sources Cited.dlmf_19_9_5 Cited.betsakos_2013
    func hhol hbound hzero

/-- diameter_closure. -/
theorem diameter_closure (domain : Set ℂ) (hbound : Bornology.IsBounded domain) (hinfinite : domain.Infinite)
    (count : ℕ) (hcount : 2 ≤ count) : nDiameter domain count = nDiameter (closure domain) count := by
  exact Proofs.nDiameter_closure_of_bounded domain hbound hinfinite.nonempty count

/-- diameter_decreasing. -/
theorem diameter_decreasing (domain : Set ℂ) (hbound : Bornology.IsBounded domain) (hinfinite : domain.Infinite) :
    AntitoneOn (nDiameter domain) (Set.Ici 2) ∧
    Tendsto (nDiameter domain) atTop (𝓝 (transfiniteDiameter domain)) := by
  exact Proofs.diameter_decreasing_proved domain hbound hinfinite

/-- diameter_capacity. -/
theorem diameter_capacity (domain : Set ℂ) (hbound : Bornology.IsBounded domain) (hinfinite : domain.Infinite) :
    transfiniteDiameter domain = capacityTD (closure domain) := by
  exact Proofs.transfiniteDiameter_closure_of_bounded domain hbound hinfinite.nonempty

/-- final_scalar_deduction. -/
theorem final_scalar_deduction (value height inner outer cap : ℝ) (hvalue : 0 < value) (hheight : 0 < height)
    (hinner : inner ∈ Ioo 0 1) (houter : outer ∈ Ioo 0 1) (horder : inner ≤ outer)
    (hmu : AntitoneOn mu (Ioo 0 1)) (hcap : cap ≤ 1/(height*value))
    (hbets : 1 ≤ 4*cap*Real.exp (-mu inner)) : value ≤ (4/height)*Real.exp (-mu outer) := by
  exact Proofs.final_scalar_deduction value height inner outer cap
    hvalue hheight hinner houter horder hmu hcap hbets

/-- polynomial_bound. -/
theorem polynomial_bound (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) : S poly ≤ yBound degree height := by
  sorry

/-- beta_y_change. -/
theorem beta_y_change (degree : ℕ) (hdegree : 2 ≤ degree) :
    yBound degree '' Ioo 0 1 = beta degree '' Ioi 0 := by
  exact Proofs.beta_y_change degree

/-- bound_set_well_defined. -/
theorem bound_set_well_defined (degree : ℕ) (hdegree : 2 ≤ degree) :
    (yBound degree '' Ioo 0 1).Nonempty ∧ BddBelow (yBound degree '' Ioo 0 1) := by
  exact Proofs.bound_set_well_defined degree

/-- kd_le_best. -/
theorem kd_le_best (degree : ℕ) (hdegree : 2 ≤ degree) : Kd degree ≤ (bestBound degree : EReal) := by
  sorry

/-- cor_step1_mu. -/
theorem cor_step1_mu (degree : ℕ) (hdegree : 2 ≤ degree) (length : ℝ) (hlength : 0 < length) :
    Real.pi^2/(4*Real.log (4/complement (radius degree length))) < mu (radius degree length) := by
  exact Proofs.cor_step1_mu_from_dlmf Cited.dlmf_19_9_5 degree hdegree length hlength

/-- cor_step1_majorant. -/
theorem cor_step1_majorant (degree : ℕ) (hdegree : 8 ≤ degree) : beta degree (Lchoice degree) < majorant degree ∧
    Kd degree < (majorant degree : EReal) := by
  sorry

/-- exp_lower. -/
theorem exp_lower (value : ℝ) (hvalue : 0 ≤ value) : value-value^2/2 ≤ 1-Real.exp (-value) := by
  exact Proofs.exp_lower value hvalue

/-- general_L_majorant. -/
theorem general_L_majorant (degree : ℕ) (hdegree : 2 ≤ degree) (length : ℝ) (hlength : length ∈ Ioo 0 (degree : ℝ)) :
    0 < lambda degree length ∧
    Real.log (4/complement (radius degree length)) ≤ lambda degree length/2 ∧
    beta degree length ≤ 4*Real.exp (length-Real.pi^2/(2*lambda degree length)) := by
  exact Proofs.general_L_majorant_from_dlmf Cited.dlmf_19_9_5 degree hdegree length hlength

/-- tail_log_correction. -/
theorem tail_log_correction (degree : ℕ) (hdegree : 21 ≤ degree) :
    1/(4*ell degree)-Real.log (1-1/ell degree) ≤ (7/4)/ell degree := by
  exact Proofs.tail_log_correction degree hdegree

/-- tail_log_ratio_decreasing. -/
theorem tail_log_ratio_decreasing : StrictAntiOn (fun value : ℝ => Real.log (32*value)/value) (Ici 1) := by
  exact Proofs.tail_log_ratio_decreasing_proved

/-- tail_lambda_upper. -/
theorem tail_lambda_upper (degree : ℕ) (hdegree : 21 ≤ degree) : lambda degree (Lchoice degree) < (253/100)*ell degree := by
  exact Proofs.tail_lambda_upper_proved degree hdegree

/-- tail_constants. -/
theorem tail_constants (degree : ℕ) (hdegree : 21 ≤ degree) :
    (304/100 : ℝ) < ell degree ∧ Real.log (32*ell degree) ≤ (152/100)*ell degree ∧
    Lchoice degree/degree < 42/10000 ∧
    -Real.log (1-Lchoice degree/degree) < (2/1000)*ell degree ∧
    (195/100)/ell degree < Real.pi^2/(2*lambda degree (Lchoice degree)) := by
  exact Proofs.tail_constants_proved degree hdegree

/-- cor_step3. -/
theorem cor_step3 (degree : ℕ) (hdegree : 21 ≤ degree) : majorant degree ≤ target degree := by
  exact Proofs.cor_step3 degree hdegree

/-- cor_step2. -/
theorem cor_step2 (degree : ℕ) (hdegree : 8 ≤ degree) (hupper : degree ≤ 20) : majorant degree < target degree := by
  exact Proofs.cor_step2 degree hdegree hupper

/-- best_strict_improvement. -/
theorem best_strict_improvement (degree : ℕ) (hdegree : 8 ≤ degree) : bestBound degree < majorant degree ∧ majorant degree ≤ target degree := by
  exact ⟨(Proofs.best_bound_le_beta degree (Lchoice degree)
    (Proofs.chosen_length_bounds degree hdegree).1).trans_lt
    (Proofs.cor_step1_majorant_from_dlmf Cited.dlmf_19_9_5 degree hdegree),
    Proofs.majorant_le_target degree hdegree⟩

/-- prop_3_4_lower_error. -/
theorem prop_3_4_lower_error : ∃ constant ≥ (0 : ℝ), ∀ᶠ degree : ℕ in atTop,
    2*Real.pi^2-constant*(Real.log (ell degree)/ell degree) ≤ gap degree := by
  exact Proofs.prop_3_4_lower_error_from_dlmf Cited.dlmf_19_9_5

/-- prop_3_4_upper. -/
theorem prop_3_4_upper (degree : ℕ) (hdegree : 8 ≤ degree) :
    gap degree ≤ 2*Real.pi^2/(1-Real.pi^2/((degree : ℝ)*(ell degree)^2)) := by
  exact Proofs.prop_3_4_upper_from_dlmf Cited.dlmf_19_9_5 degree hdegree

/-- prop_3_4_limit. -/
theorem prop_3_4_limit : Tendsto gap atTop (𝓝 (2*Real.pi^2)) := by
  exact Proofs.prop_3_4_limit_from_dlmf Cited.dlmf_19_9_5

/-- prop_denominator_positive. -/
theorem prop_denominator_positive (degree : ℕ) (hdegree : 8 ≤ degree) :
    Real.pi^2 < (degree : ℝ)*(ell degree)^2 ∧ 0 < 2*ell degree-2*Real.pi^2/(ell degree*degree) := by
  exact Proofs.prop_denominator_positive degree hdegree

/-- prop_delta_bound. -/
theorem prop_delta_bound (degree : ℕ) (hdegree : 8 ≤ degree) (length : ℝ) (hlength : length ∈ Ioo 0 2) :
    0 < delta degree length ∧ delta degree length < 4*mu (complement (radius degree length)) ∧
    mu (radius degree length) < Real.pi^2/delta degree length := by
  exact Proofs.prop_delta_bound_from_dlmf Cited.dlmf_19_9_5 degree hdegree length hlength

/-- prop_case_a. -/
theorem prop_case_a (degree : ℕ) (hdegree : 8 ≤ degree) (length : ℝ) (hlength : 2 ≤ length) :
    4 < Real.exp ((1-1/(degree : ℝ))*length) ∧
    Real.exp ((1-1/(degree : ℝ))*length) < beta degree length := by
  exact Proofs.prop_case_a_proved Cited.dlmf_19_9_5 degree hdegree length hlength

/-- prop_case_b. -/
theorem prop_case_b (degree : ℕ) (hdegree : 8 ≤ degree) (length : ℝ)
    (hlower : Real.pi^2/(2*ell degree) ≤ length) (hupper : length < 2) : 4 < beta degree length := by
  exact Proofs.prop_case_b_proved Cited.dlmf_19_9_5 degree hdegree length hlower hupper

/-- prop_case_c. -/
theorem prop_case_c (degree : ℕ) (hdegree : 8 ≤ degree) (length : ℝ)
    (hlength : length ∈ Ioo 0 (min 2 (Real.pi^2/(2*ell degree)))) : uniformLower degree < beta degree length := by
  exact Proofs.prop_case_c_proved Cited.dlmf_19_9_5 degree hdegree length hlength

/-- prop_uniform_lower. -/
theorem prop_uniform_lower (degree : ℕ) (hdegree : 8 ≤ degree) : uniformLower degree ≤ bestBound degree := by
  exact Proofs.prop_uniform_lower_from_dlmf Cited.dlmf_19_9_5 degree hdegree

/-- prop_selected_L. -/
theorem prop_selected_L : ∃ constant ≥ (0 : ℝ), ∀ᶠ degree : ℕ in atTop,
    beta degree (Real.pi^2/(2*(ell degree)^2)) ≤
      4*Real.exp (-Real.pi^2/(2*ell degree)+constant*Real.log (ell degree)/(ell degree)^2) := by
  exact Proofs.prop_selected_L_from_dlmf Cited.dlmf_19_9_5

/-- weaker_asymptotic_difference. -/
theorem weaker_asymptotic_difference : Tendsto (fun degree : ℕ => (target degree-bestBound degree)*ell degree) atTop (𝓝 (2*Real.pi^2-4)) := by
  exact Proofs.weaker_asymptotic_difference_of_gap prop_3_4_limit

/-- weaker_k_gap_liminf. -/
theorem weaker_k_gap_liminf (epsilon : ℝ) (hepsilon : 0 < epsilon) : ∀ᶠ degree : ℕ in atTop,
    Kd degree ≤ ((4 - (2*Real.pi^2-epsilon)/ell degree : ℝ) : EReal) := by
  sorry

/-- earlier_crane_comparison. -/
theorem earlier_crane_comparison (degree : ℕ) (hdegree : 8 ≤ degree) : target degree < crane degree := by
  exact Proofs.earlier_crane_comparison_proved degree hdegree

/-- sqrt_log_minimum. -/
theorem sqrt_log_minimum (value : ℝ) (hvalue : 1 < value) :
    Real.exp 1/2 ≤ Real.sqrt value/Real.log value ∧
    (Real.sqrt value/Real.log value = Real.exp 1/2 ↔ value = Real.exp 2) := by
  exact Proofs.sqrt_log_minimum_proved value hvalue

/-- earlier_fujikawa_comparison. -/
theorem earlier_fujikawa_comparison (degree : ℕ) (hdegree : 8 ≤ degree) : target degree < fujikawa degree := by
  exact Proofs.earlier_fujikawa_comparison_proved degree hdegree

/-- earlier_three_comparisons. -/
theorem earlier_three_comparisons (degree : ℕ) (hdegree : 8 ≤ degree) :
    fujikawa degree ≤ conte degree ∧ fujikawa degree < beardon degree ∧ fujikawa degree < dubinin degree := by
  exact Proofs.earlier_three_comparisons_proved degree hdegree

/-- d_plus_one_log_increasing. -/
theorem d_plus_one_log_increasing : StrictMonoOn (fun value : ℝ => (value+1)/Real.log value) (Ici 4) := by
  exact Proofs.d_plus_one_log_increasing_proved

/-- agm_bracketing. -/
theorem agm_bracketing (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) (index : ℕ) :
    (agmPair modulus index).2 ≤ (agmPair modulus (index+1)).2 ∧
    (agmPair modulus (index+1)).2 ≤ (agmPair modulus (index+1)).1 ∧
    (agmPair modulus (index+1)).1 ≤ (agmPair modulus index).1 ∧
    (agmPair modulus (index+1)).1-(agmPair modulus (index+1)).2 ≤
      ((agmPair modulus index).1-(agmPair modulus index).2)/2 ∧
    (agmPair modulus index).2 ≤ agm modulus ∧ agm modulus ≤ (agmPair modulus index).1 := by
  exact Proofs.agm_bracketing_proved modulus hmodulus index

/-- agm_convergence. -/
theorem agm_convergence (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) :
    Tendsto (fun index => (agmPair modulus index).1) atTop (𝓝 (agm modulus)) ∧
    Tendsto (fun index => (agmPair modulus index).2) atTop (𝓝 (agm modulus)) := by
  exact Proofs.agm_convergence_proved modulus hmodulus

/-- agm_elliptic_identity. -/
theorem agm_elliptic_identity (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) :
    ellipticK modulus = Real.pi/(2*agm (complement modulus)) ∧
    mu modulus = Real.pi*agm (complement modulus)/(2*agm modulus) := by
  exact Proofs.agm_elliptic_identity_from_dlmf Cited.dlmf_19_8_5 modulus hmodulus

/-- dlmf_19_8_5. -/
theorem dlmf_19_8_5 (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) :
    ellipticK modulus = Real.pi/(2*agm (complement modulus)) := by
  exact SmaleRate.Cited.dlmf_19_8_5 modulus hmodulus

/-- range_7_enclosure. -/
theorem range_7_enclosure : (20190/10000 : ℝ) < bestBound 7 ∧ bestBound 7 < 20191/10000 ∧ target 7 < 19445/10000 := by
  have hbound := Proofs.certified_seven_enclosure Cited.dlmf_19_8_5 Cited.dlmf_19_9_5
  exact ⟨hbound.1, hbound.2, Proofs.degree_seven_target_upper⟩

/-- range_8_enclosure. -/
theorem range_8_enclosure : (20549/10000 : ℝ) < bestBound 8 ∧ bestBound 8 < 20550/10000 ∧ gap 8 < 4045/1000 := by
  have hbound := Proofs.certified_eight_enclosure Cited.dlmf_19_8_5 Cited.dlmf_19_9_5
  exact ⟨hbound.1, hbound.2,
    (Proofs.certified_eight_gap_enclosure Cited.dlmf_19_8_5 Cited.dlmf_19_9_5).2⟩

/-- range_selected_values. -/
theorem range_selected_values : beta 8 (12766/100000) < (20550/10000 : ℝ) ∧ beta 7 (13621/100000) < 20191/10000 := by
  constructor
  · convert Proofs.point8_certificate Cited.dlmf_19_8_5 using 1 <;> norm_num
  · convert Proofs.point7_certificate Cited.dlmf_19_8_5 using 1 <;> norm_num

/-- range_tail. -/
theorem range_tail (degree : ℕ) (hdegree : degree = 7 ∨ degree = 8) (length : ℝ) (hlength : 1 ≤ length) :
    (235/100 : ℝ) < Real.exp (6/7) ∧ Real.exp (6/7) < beta degree length := by
  exact Proofs.range_tail_strict_from_dlmf Cited.dlmf_19_9_5 degree hdegree length hlength

/-- range_interval_lower. -/
theorem range_interval_lower (degree : ℕ) (hdegree : 2 ≤ degree) (lower upper length : ℝ)
    (hlower : 0 ≤ lower) (horder : lower < length) (hupper : length ≤ upper) :
    4*Real.exp lower*Real.exp (-mu (radius degree upper)) ≤ beta degree length := by
  exact Proofs.range_interval_lower_proved Cited.dlmf_19_9_5 degree hdegree lower upper length hlower horder hupper

/-- figure3_height. -/
theorem figure3_height (degree : ℕ) (hdegree : 8 ≤ degree) :
    Kd degree ≤ ((4-gap degree/ell degree : ℝ) : EReal) ∧ 4 < gap degree := by
  sorry

/-- Table 3 M, degree 8. -/
theorem table3_M_8 : majorant 8 ≤ (205907/100000 : ℝ) := by
  convert Proofs.table3_rounding_eight.1.2 using 1 <;> norm_num

/-- Table 3 target, degree 8. -/
theorem table3_target_8 : (207640/100000 : ℝ) ≤ target 8 := by
  convert Proofs.table3_rounding_eight.2.1 using 1 <;> norm_num

/-- Table 3 margin, degree 8. -/
theorem table3_margin_8 : (1733/100000 : ℝ) ≤ target 8-majorant 8 := by
  have hmajorant := Proofs.table3_rounding_eight.1.2
  have htarget := Proofs.table3_rounding_eight.2.1
  linarith

/-- Table 3 M, degree 9. -/
theorem table3_M_9 : majorant 9 ≤ (208862/100000 : ℝ) := by
  convert Proofs.table3_rounding_9.1.2 using 1 <;> norm_num

/-- Table 3 target, degree 9. -/
theorem table3_target_9 : (217952/100000 : ℝ) ≤ target 9 := by
  convert Proofs.table3_rounding_9.2.1 using 1 <;> norm_num

/-- Table 3 margin, degree 9. -/
theorem table3_margin_9 : (9090/100000 : ℝ) ≤ target 9-majorant 9 := by
  have hmajorant := Proofs.table3_rounding_9.1.2
  have htarget := Proofs.table3_rounding_9.2.1
  linarith

/-- Table 3 M, degree 10. -/
theorem table3_M_10 : majorant 10 ≤ (211417/100000 : ℝ) := by
  convert Proofs.table3_rounding_10.1.2 using 1 <;> norm_num

/-- Table 3 target, degree 10. -/
theorem table3_target_10 : (226282/100000 : ℝ) ≤ target 10 := by
  convert Proofs.table3_rounding_10.2.1 using 1 <;> norm_num

/-- Table 3 margin, degree 10. -/
theorem table3_margin_10 : (14865/100000 : ℝ) ≤ target 10-majorant 10 := by
  have hmajorant := Proofs.table3_rounding_10.1.2
  have htarget := Proofs.table3_rounding_10.2.1
  linarith

/-- Table 3 M, degree 11. -/
theorem table3_M_11 : majorant 11 ≤ (213661/100000 : ℝ) := by
  convert Proofs.table3_rounding_11.1.2 using 1 <;> norm_num

/-- Table 3 target, degree 11. -/
theorem table3_target_11 : (233187/100000 : ℝ) ≤ target 11 := by
  convert Proofs.table3_rounding_11.2.1 using 1 <;> norm_num

/-- Table 3 margin, degree 11. -/
theorem table3_margin_11 : (19526/100000 : ℝ) ≤ target 11-majorant 11 := by
  have hmajorant := Proofs.table3_rounding_11.1.2
  have htarget := Proofs.table3_rounding_11.2.1
  linarith

/-- Table 3 M, degree 12. -/
theorem table3_M_12 : majorant 12 ≤ (215656/100000 : ℝ) := by
  convert Proofs.table3_rounding_12.1.2 using 1 <;> norm_num

/-- Table 3 target, degree 12. -/
theorem table3_target_12 : (239028/100000 : ℝ) ≤ target 12 := by
  convert Proofs.table3_rounding_12.2.1 using 1 <;> norm_num

/-- Table 3 margin, degree 12. -/
theorem table3_margin_12 : (23372/100000 : ℝ) ≤ target 12-majorant 12 := by
  have hmajorant := Proofs.table3_rounding_12.1.2
  have htarget := Proofs.table3_rounding_12.2.1
  linarith

/-- Table 3 M, degree 13. -/
theorem table3_M_13 : majorant 13 ≤ (217447/100000 : ℝ) := by
  convert Proofs.table3_rounding_13.1.2 using 1 <;> norm_num

/-- Table 3 target, degree 13. -/
theorem table3_target_13 : (244051/100000 : ℝ) ≤ target 13 := by
  convert Proofs.table3_rounding_13.2.1 using 1 <;> norm_num

/-- Table 3 margin, degree 13. -/
theorem table3_margin_13 : (26604/100000 : ℝ) ≤ target 13-majorant 13 := by
  have hmajorant := Proofs.table3_rounding_13.1.2
  have htarget := Proofs.table3_rounding_13.2.1
  linarith

/-- Table 3 M, degree 14. -/
theorem table3_M_14 : majorant 14 ≤ (219069/100000 : ℝ) := by
  convert Proofs.table3_rounding_14.1.2 using 1 <;> norm_num

/-- Table 3 target, degree 14. -/
theorem table3_target_14 : (248430/100000 : ℝ) ≤ target 14 := by
  convert Proofs.table3_rounding_14.2.1 using 1 <;> norm_num

/-- Table 3 margin, degree 14. -/
theorem table3_margin_14 : (29361/100000 : ℝ) ≤ target 14-majorant 14 := by
  have hmajorant := Proofs.table3_rounding_14.1.2
  have htarget := Proofs.table3_rounding_14.2.1
  linarith

/-- Table 3 M, degree 15. -/
theorem table3_M_15 : majorant 15 ≤ (220549/100000 : ℝ) := by
  convert Proofs.table3_rounding_15.1.2 using 1 <;> norm_num

/-- Table 3 target, degree 15. -/
theorem table3_target_15 : (252292/100000 : ℝ) ≤ target 15 := by
  convert Proofs.table3_rounding_15.2.1 using 1 <;> norm_num

/-- Table 3 margin, degree 15. -/
theorem table3_margin_15 : (31743/100000 : ℝ) ≤ target 15-majorant 15 := by
  have hmajorant := Proofs.table3_rounding_15.1.2
  have htarget := Proofs.table3_rounding_15.2.1
  linarith

/-- Table 3 M, degree 16. -/
theorem table3_M_16 : majorant 16 ≤ (221907/100000 : ℝ) := by
  convert Proofs.table3_rounding_16.1.2 using 1 <;> norm_num

/-- Table 3 target, degree 16. -/
theorem table3_target_16 : (255730/100000 : ℝ) ≤ target 16 := by
  convert Proofs.table3_rounding_16.2.1 using 1 <;> norm_num

/-- Table 3 margin, degree 16. -/
theorem table3_margin_16 : (33823/100000 : ℝ) ≤ target 16-majorant 16 := by
  have hmajorant := Proofs.table3_rounding_16.1.2
  have htarget := Proofs.table3_rounding_16.2.1
  linarith

/-- Table 3 M, degree 17. -/
theorem table3_M_17 : majorant 17 ≤ (223162/100000 : ℝ) := by
  convert Proofs.table3_rounding_17.1.2 using 1 <;> norm_num

/-- Table 3 target, degree 17. -/
theorem table3_target_17 : (258817/100000 : ℝ) ≤ target 17 := by
  convert Proofs.table3_rounding_17.2.1 using 1 <;> norm_num

/-- Table 3 margin, degree 17. -/
theorem table3_margin_17 : (35655/100000 : ℝ) ≤ target 17-majorant 17 := by
  have hmajorant := Proofs.table3_rounding_17.1.2
  have htarget := Proofs.table3_rounding_17.2.1
  linarith

/-- Table 3 M, degree 18. -/
theorem table3_M_18 : majorant 18 ≤ (224326/100000 : ℝ) := by
  convert Proofs.table3_rounding_18.1.2 using 1 <;> norm_num

/-- Table 3 target, degree 18. -/
theorem table3_target_18 : (261609/100000 : ℝ) ≤ target 18 := by
  convert Proofs.table3_rounding_18.2.1 using 1 <;> norm_num

/-- Table 3 margin, degree 18. -/
theorem table3_margin_18 : (37283/100000 : ℝ) ≤ target 18-majorant 18 := by
  have hmajorant := Proofs.table3_rounding_18.1.2
  have htarget := Proofs.table3_rounding_18.2.1
  linarith

/-- Table 3 M, degree 19. -/
theorem table3_M_19 : majorant 19 ≤ (225410/100000 : ℝ) := by
  convert Proofs.table3_rounding_19.1.2 using 1 <;> norm_num

/-- Table 3 target, degree 19. -/
theorem table3_target_19 : (264150/100000 : ℝ) ≤ target 19 := by
  convert Proofs.table3_rounding_19.2.1 using 1 <;> norm_num

/-- Table 3 margin, degree 19. -/
theorem table3_margin_19 : (38740/100000 : ℝ) ≤ target 19-majorant 19 := by
  have hmajorant := Proofs.table3_rounding_19.1.2
  have htarget := Proofs.table3_rounding_19.2.1
  linarith

/-- Table 3 M, degree 20. -/
theorem table3_M_20 : majorant 20 ≤ (226424/100000 : ℝ) := by
  convert Proofs.table3_rounding_20.1.2 using 1 <;> norm_num

/-- Table 3 target, degree 20. -/
theorem table3_target_20 : (266476/100000 : ℝ) ≤ target 20 := by
  convert Proofs.table3_rounding_20.2.1 using 1 <;> norm_num

/-- Table 3 margin, degree 20. -/
theorem table3_margin_20 : (40052/100000 : ℝ) ≤ target 20-majorant 20 := by
  have hmajorant := Proofs.table3_rounding_20.1.2
  have htarget := Proofs.table3_rounding_20.2.1
  linarith

/-- tail_star. -/
theorem tail_star (degree : ℕ) (hdegree : 21 ≤ degree) : 1/(4*ell degree)-Real.log (1-1/ell degree) ≤ Real.pi^2/(2*lambda degree (Lchoice degree)) := by
  exact Proofs.tail_star degree hdegree

/-- bounds_below_39. -/
theorem bounds_below_39 (degree : ℕ) (hdegree : 8 ≤ degree) (hupper : (degree : ℝ) ≤ Real.exp 40) : Kd degree < ((39/10 : ℝ) : EReal) := by
  sorry

/-- small_bound_below_39. -/
theorem small_bound_below_39 (degree : ℕ) (hdegree : 2 ≤ degree) (hupper : degree ≤ 7) : Kd degree ≤ ((Real.rpow 4 (5/6) : ℝ) : EReal) ∧ (4 : ℝ)^(5/6 : ℝ) < 39/10 := by
  sorry

/-- range_7_best_improvement. -/
theorem range_7_best_improvement : target 7 < bestBound 7 ∧ Kd 7 ≤ (bestBound 7 : EReal) ∧ fujikawa 7 ≤ conte 7 ∧ fujikawa 7 ≤ beardon 7 ∧ fujikawa 7 ≤ dubinin 7 ∧ (24842/10000 : ℝ) < fujikawa 7 ∧ fujikawa 7 < 24843/10000 := by
  sorry

/-- figure3_gap8. -/
theorem figure3_gap8 : (4 : ℝ) < gap 8 ∧ gap 8 < 405/100 := by
  have hbound := Proofs.certified_eight_gap_enclosure Cited.dlmf_19_8_5 Cited.dlmf_19_9_5
  exact ⟨hbound.1, hbound.2.trans (by norm_num)⟩

/-- general_exp_upper. -/
theorem general_exp_upper (value : ℝ) (hvalue : 0 ≤ value) : 1-Real.exp (-value) ≤ value := by
  exact Proofs.general_exp_upper value hvalue

/-- log_one_sub. -/
theorem log_one_sub (value : ℝ) (hvalue : value ∈ Ioo 0 1) : -Real.log (1-value) ≤ value/(1-value) := by
  exact Proofs.log_one_sub value hvalue

/-- log_one_sub_half. -/
theorem log_one_sub_half (value : ℝ) (hvalue : value ∈ Icc 0 (1/2 : ℝ)) : -Real.log (1-value) ≤ 2*value := by
  exact Proofs.log_one_sub_half value hvalue

/-- diameter_closure_limit. -/
theorem diameter_closure_limit (domain : Set ℂ) (hbound : Bornology.IsBounded domain) (hinfinite : domain.Infinite) : transfiniteDiameter domain = transfiniteDiameter (closure domain) := by
  exact Proofs.transfiniteDiameter_closure_of_bounded domain hbound hinfinite.nonempty

/-- betsakos_small_argument. -/
theorem betsakos_small_argument (diameter : ℝ) : ∃ constant ≥ (0 : ℝ), ∀ᶠ modulus in 𝓝[>] (0 : ℝ), |4*diameter*Real.exp (-mu modulus)-diameter*modulus| ≤ constant*|modulus|^3 := by
  exact Proofs.betsakos_small_argument_proved Cited.dlmf_19_9_5 diameter

/-- betsakos_large_argument. -/
theorem betsakos_large_argument (diameter : ℝ) : Tendsto (fun modulus : ℝ => 4*diameter*Real.exp (-mu modulus)) (𝓝[<] 1) (𝓝 (4*diameter)) := by
  exact Proofs.betsakos_large_argument_proved Cited.dlmf_19_9_5 diameter

/-- zero_betsakos_interpretation. -/
theorem zero_betsakos_interpretation (diameter : ℝ) : Tendsto (fun modulus : ℝ => 4*diameter*Real.exp (-mu modulus)) (𝓝[>] 0) (𝓝 0) := by
  exact Proofs.zero_betsakos_interpretation_proved Cited.dlmf_19_9_5 diameter

/-- capacity_phi_expansion. -/
theorem capacity_phi_expansion (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0) (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (hcritical : critical ≠ 0) : ∃ constant : ℂ, Tendsto (fun point : ℂ => inversion critical (inverse ((height : ℂ)/point)) - (-critical/((height : ℂ)*deriv inverse 0))*point) (cocompact ℂ) (𝓝 constant) := by
  exact Proofs.capacity_phi_expansion_proved inverse hinverse hzero height hheight critical hcritical

/-- exterior_conformal_map. -/
theorem exterior_conformal_map (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0) (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (hcritical : critical ≠ 0) : IsConformalOnto (fun point : ℂ => inversion critical (inverse ((height : ℂ)/point))) {point : ℂ | 1 < ‖point‖} (closure (exteriorImage inverse height critical))ᶜ := by
  exact Proofs.exterior_conformal_map_proved inverse hinverse hzero height hheight critical hcritical

/-- xi_polynomial_holomorphic_extension. -/
theorem xi_polynomial_holomorphic_extension (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly) (critical : ℂ) (hnormal : NormalizedCriticalValues poly critical) (inverse : ℂ → ℂ) (hinverse : IsInverseBranch poly inverse) (height : ℝ) (hheight : height ∈ Ioo 0 1) (func : ℂ → ℂ) (hfunc : IsConformalOnto func (disk 1) (exteriorImage inverse height critical)) (hzero : func 0 = 0) : ∃ extension : ℂ → ℂ, DifferentiableOn ℂ extension (disk 1) ∧ (∀ point ∈ disk 1, point ≠ 0 → extension point = point^degree*poly.eval (inversion critical (func point))) ∧ ∀ point ∈ disk 1, ‖extension point‖ ≤ height := by
  exact Proofs.xi_polynomial_holomorphic_extension_proved degree hdegree poly hpoly critical hnormal
    inverse hinverse height hheight func hfunc hzero

/-- figure2_example. -/
theorem figure2_example : IsPd 2 ((2 : ℂ[X])*Polynomial.X-Polynomial.X^2) ∧ NormalizedCriticalValues ((2 : ℂ[X])*Polynomial.X-Polynomial.X^2) 1 := by
  exact Proofs.figure2_example_proved

/-- table2_8. -/
theorem table2_8 : target 8 ≤ (20765/10000 : ℝ) ∧ beta 8 (12766/100000) ≤ (20550/10000 : ℝ) ∧ bestBound 8 ≤ (20550/10000 : ℝ) := by
  have hbeta : beta 8 (12766/100000) < (20550/10000 : ℝ) := by
    convert Proofs.point8_certificate Cited.dlmf_19_8_5 using 1 <;> norm_num
  exact Proofs.table2_point_of_beta 8 (12766/100000) (20765/10000) (20550/10000) (by norm_num) Proofs.table2_target_bounds.1 hbeta.le

/-- figure3_dot_8. -/
theorem figure3_dot_8 : ((4-(20550/10000 : ℝ))*ell 8) ≤ gap 8 := by
  exact Proofs.figure_gap_lower_of_beta 8 (by norm_num) (12766/100000) (20550/10000) (by norm_num) table2_8.2.1

/-- table2_100. -/
theorem table2_100 : target 100 ≤ (31315/10000 : ℝ) ∧ beta 100 (5337/100000) ≤ (25255/10000 : ℝ) ∧ bestBound 100 ≤ (25255/10000 : ℝ) := by
  have hbeta : beta 100 (5337/100000) < (25255/10000 : ℝ) := by
    convert Proofs.point100_certificate Cited.dlmf_19_8_5 using 1 <;> norm_num
  exact Proofs.table2_point_of_beta 100 (5337/100000) (31315/10000) (25255/10000) (by norm_num) Proofs.table2_target_bounds.2.1 hbeta.le

/-- figure3_dot_100. -/
theorem figure3_dot_100 : ((4-(25255/10000 : ℝ))*ell 100) ≤ gap 100 := by
  exact Proofs.figure_gap_lower_of_beta 100 (by norm_num) (5337/100000) (25255/10000) (by norm_num) table2_100.2.1

/-- table2_10000. -/
theorem table2_10000 : target 10000 ≤ (35658/10000 : ℝ) ∧ beta 10000 (2156/100000) ≤ (29495/10000 : ℝ) ∧ bestBound 10000 ≤ (29495/10000 : ℝ) := by
  have hbeta : beta 10000 (2156/100000) < (29495/10000 : ℝ) := by
    convert Proofs.point10000_certificate Cited.dlmf_19_8_5 using 1 <;> norm_num
  exact Proofs.table2_point_of_beta 10000 (2156/100000) (35658/10000) (29495/10000) (by norm_num) Proofs.table2_target_bounds.2.2.1 hbeta.le

/-- figure3_dot_10000. -/
theorem figure3_dot_10000 : ((4-(29495/10000 : ℝ))*ell 10000) ≤ gap 10000 := by
  exact Proofs.figure_gap_lower_of_beta 10000 (by norm_num) (2156/100000) (29495/10000) (by norm_num) table2_10000.2.1

/-- table2_1000000. -/
theorem table2_1000000 : target 1000000 ≤ (37105/10000 : ℝ) ∧ beta 1000000 (1194/100000) ≤ (31754/10000 : ℝ) ∧ bestBound 1000000 ≤ (31754/10000 : ℝ) := by
  have hbeta : beta 1000000 (1194/100000) < (31754/10000 : ℝ) := by
    convert Proofs.point1000000_certificate Cited.dlmf_19_8_5 using 1 <;> norm_num
  exact Proofs.table2_point_of_beta 1000000 (1194/100000) (37105/10000) (31754/10000) (by norm_num) Proofs.table2_target_bounds.2.2.2 hbeta.le

/-- figure3_dot_1000000. -/
theorem figure3_dot_1000000 : ((4-(31754/10000 : ℝ))*ell 1000000) ≤ gap 1000000 := by
  exact Proofs.figure_gap_lower_of_beta 1000000 (by norm_num) (1194/100000) (31754/10000) (by norm_num) table2_1000000.2.1

/-- crane_numeric_8. -/
theorem crane_numeric_8 : Kd 8 < ((3124/1000 : ℝ) : EReal) ∧ (389/1000 : ℝ) < 3124/1000-target 8 := by
  sorry

/-- crane_numeric_9. -/
theorem crane_numeric_9 : Kd 9 < ((3150/1000 : ℝ) : EReal) ∧ (389/1000 : ℝ) < 3150/1000-target 9 := by
  sorry

/-- crane_numeric_10. -/
theorem crane_numeric_10 : Kd 10 < ((3169/1000 : ℝ) : EReal) ∧ (389/1000 : ℝ) < 3169/1000-target 10 := by
  sorry

/-- crane_numeric_11. -/
theorem crane_numeric_11 : Kd 11 < ((3188/1000 : ℝ) : EReal) ∧ (389/1000 : ℝ) < 3188/1000-target 11 := by
  sorry

/-- crane_numeric_12. -/
theorem crane_numeric_12 : Kd 12 < ((3208/1000 : ℝ) : EReal) ∧ (389/1000 : ℝ) < 3208/1000-target 12 := by
  sorry

/-- crane_numeric_16. -/
theorem crane_numeric_16 : Kd 16 < ((3271/1000 : ℝ) : EReal) ∧ (389/1000 : ℝ) < 3271/1000-target 16 := by
  sorry

/-- crane_numeric_25. -/
theorem crane_numeric_25 : Kd 25 < ((3365/1000 : ℝ) : EReal) ∧ (389/1000 : ℝ) < 3365/1000-target 25 := by
  sorry

/-- crane_numeric_100. -/
theorem crane_numeric_100 : Kd 100 < ((3621/1000 : ℝ) : EReal) ∧ (389/1000 : ℝ) < 3621/1000-target 100 := by
  sorry

/-- crane_numeric_10000. -/
theorem crane_numeric_10000 : Kd 10000 < ((3955/1000 : ℝ) : EReal) ∧ (389/1000 : ℝ) < 3955/1000-target 10000 := by
  sorry

/-- inverse_analytic_boundary. -/
theorem inverse_analytic_boundary (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0) (height : ℝ) (hheight : height ∈ Ioo 0 1) : AnalyticOnNhd ℂ inverse (Metric.sphere 0 height) ∧ (∀ point ∈ Metric.sphere 0 height, deriv inverse point ≠ 0) ∧ frontier (inverseDomain inverse height) = inverse '' Metric.sphere 0 height := by
  exact Proofs.inverse_analytic_boundary_proved inverse hinverse hzero height hheight

/-- conformal_geometry_witness. -/
theorem conformal_geometry_witness  : IsBoundedJordanDomain (disk 1) ∧ IsConformalOnto (fun point : ℂ => point) (disk 1) (disk 1) := by
  exact Proofs.conformal_geometry_witness_proved

/-- capacity_conformal_coefficient. -/
theorem capacity_conformal_coefficient (compactSet : Set ℂ) (hcompact : IsCompact compactSet) (hconnected : IsConnected compactSet) (hnontrivial : ∃ first ∈ compactSet, ∃ second ∈ compactSet, first ≠ second) (hcomplement : IsConnected compactSetᶜ) (phi : ℂ → ℂ) (hphi : IsConformalOnto phi {point : ℂ | 1 < ‖point‖} compactSetᶜ) (coefficient : ℂ) (hcoefficient : coefficient ≠ 0) (hexpansion : ∃ constant : ℂ, Tendsto (fun point : ℂ => phi point-coefficient*point) (cocompact ℂ) (𝓝 constant)) : capacityTD compactSet ≤ ‖coefficient‖ := by
  sorry

/-- table3_printed_minimum. -/
theorem table3_printed_minimum  : ∀ entry ∈ ([(8,1733),(9,9090),(10,14865),(11,19526),(12,23372),(13,26604),(14,29361),(15,31743),(16,33823),(17,35655),(18,37283),(19,38740),(20,40052)] : List (ℕ × ℕ)), (1733 : ℕ) ≤ entry.2 ∧ (entry.2 = 1733 ↔ entry.1 = 8) := by
  exact Proofs.table3_printed_minimum

/-- crane_unique_minimum. -/
theorem crane_unique_minimum  : ∀ entry ∈ ([(8,3124),(9,3150),(10,3169),(11,3188),(12,3208),(16,3271),(25,3365),(100,3621),(10000,3955)] : List (ℕ × ℕ)), (3955/1000 : ℝ)-target 10000 ≤ (entry.2 : ℝ)/1000-target entry.1 ∧ (entry.1 ≠ 10000 → (3955/1000 : ℝ)-target 10000 < (entry.2 : ℝ)/1000-target entry.1) := by
  exact Proofs.crane_unique_minimum_proved

/-- figure1_six_dots_above. -/
theorem figure1_six_dots_above  : ∀ entry ∈ ([(8,3124),(9,3150),(10,3169),(11,3188),(12,3208),(16,3271)] : List (ℕ × ℕ)), min (fujikawa entry.1) (crane entry.1) < (entry.2 : ℝ)/1000 := by
  exact Proofs.figure1_six_dots_above_proved

/-- figure1_three_dots_below. -/
theorem figure1_three_dots_below  : ∀ entry ∈ ([(25,3365),(100,3621),(10000,3955)] : List (ℕ × ℕ)), (entry.2 : ℝ)/1000 < min (fujikawa entry.1) (crane entry.1) := by
  exact Proofs.figure1_three_dots_below_proved

/-- figure1_excluded_regions. -/
theorem figure1_excluded_regions (degree : ℕ) (hdegree : 8 ≤ degree) : Kd degree ≤ ((min (fujikawa degree) (crane degree) : ℝ) : EReal) ∧ bestBound degree < min (fujikawa degree) (crane degree) := by
  sorry

/-- first_four_order. -/
theorem first_four_order  : ∀ bound ∈ ([beardon, conte, fujikawa, dubinin] : List (ℕ → ℝ)), ∃ lower upper : ℝ, 0 < lower ∧ lower ≤ upper ∧ ∀ᶠ degree : ℕ in atTop, lower/(degree : ℝ) ≤ 4-bound degree ∧ 4-bound degree ≤ upper/degree := by
  exact Proofs.first_four_order_proved

/-- crane_gap_order. -/
theorem crane_gap_order (degree : ℕ) : 4-crane degree = (2263/1000)/Real.sqrt degree := by
  exact Proofs.crane_gap_order_proved degree

/-- small_multiple_asymptotic. -/
theorem small_multiple_asymptotic (multiple : ℝ) (hmultiple : multiple ∈ Ioo 0 (Real.pi^2/2)) : Tendsto (fun degree : ℕ => (4-4*Real.exp (multiple/ell degree-Real.pi^2/(2*lambda degree (multiple/ell degree))))*ell degree) atTop (𝓝 (2*Real.pi^2-4*multiple)) := by
  exact Proofs.small_multiple_asymptotic_proved multiple hmultiple

/-- quadratic_inverse_example. -/
theorem quadratic_inverse_example  : IsInverseBranch ((2 : ℂ[X])*Polynomial.X-Polynomial.X^2) (fun point : ℂ => 1-Complex.sqrt (1-point)) ∧ (1 : ℂ) ∉ (fun point : ℂ => 1-Complex.sqrt (1-point)) '' disk 1 ∧ (1 : ℂ) ∈ frontier ((fun point : ℂ => 1-Complex.sqrt (1-point)) '' disk 1) := by
  exact Proofs.quadratic_inverse_example_proved

/-- table2_earlier_8. -/
theorem table2_earlier_8  : IsLeast ({fujikawa 8, conte 8, beardon 8, dubinin 8, crane 8, (3124/1000 : ℝ)} : Set ℝ) (fujikawa 8) ∧ (fujikawa 8) ≤ (26321/10000 : ℝ) := by
  exact Proofs.table2_earlier_eight_proved

/-- table2_earlier_100. -/
theorem table2_earlier_100  : IsLeast ({fujikawa 100, conte 100, beardon 100, dubinin 100, crane 100, (3621/1000 : ℝ)} : Set ℝ) ((3621/1000 : ℝ)) ∧ ((3621/1000 : ℝ)) ≤ (3621/1000 : ℝ) := by
  exact Proofs.table2_earlier_hundred_proved

/-- table2_earlier_10000. -/
theorem table2_earlier_10000  : IsLeast ({fujikawa 10000, conte 10000, beardon 10000, dubinin 10000, crane 10000, (3955/1000 : ℝ)} : Set ℝ) ((3955/1000 : ℝ)) ∧ ((3955/1000 : ℝ)) ≤ (3955/1000 : ℝ) := by
  exact Proofs.table2_earlier_ten_thousand_proved

/-- table2_earlier_1000000. -/
theorem table2_earlier_1000000  : IsLeast ({fujikawa 1000000, conte 1000000, beardon 1000000, dubinin 1000000, crane 1000000} : Set ℝ) (crane 1000000) ∧ (crane 1000000) ≤ (39978/10000 : ℝ) := by
  exact Proofs.table2_earlier_million_proved

/-- table3_M_rounding_8. -/
theorem table3_M_rounding_8  : (205906/100000 : ℝ) < majorant 8 ∧ majorant 8 ≤ (205907/100000 : ℝ) := by
  convert Proofs.table3_rounding_eight.1 using 1 <;> norm_num

/-- table3_target_rounding_8. -/
theorem table3_target_rounding_8  : (207640/100000 : ℝ) ≤ target 8 ∧ target 8 < (207641/100000 : ℝ) := by
  convert Proofs.table3_rounding_eight.2 using 1 <;> norm_num

/-- table3_M_rounding_9. -/
theorem table3_M_rounding_9  : (208861/100000 : ℝ) < majorant 9 ∧ majorant 9 ≤ (208862/100000 : ℝ) := by
  convert Proofs.table3_rounding_9.1 using 1 <;> norm_num

/-- table3_target_rounding_9. -/
theorem table3_target_rounding_9  : (217952/100000 : ℝ) ≤ target 9 ∧ target 9 < (217953/100000 : ℝ) := by
  convert Proofs.table3_rounding_9.2 using 1 <;> norm_num

/-- table3_M_rounding_10. -/
theorem table3_M_rounding_10  : (211416/100000 : ℝ) < majorant 10 ∧ majorant 10 ≤ (211417/100000 : ℝ) := by
  convert Proofs.table3_rounding_10.1 using 1 <;> norm_num

/-- table3_target_rounding_10. -/
theorem table3_target_rounding_10  : (226282/100000 : ℝ) ≤ target 10 ∧ target 10 < (226283/100000 : ℝ) := by
  convert Proofs.table3_rounding_10.2 using 1 <;> norm_num

/-- table3_M_rounding_11. -/
theorem table3_M_rounding_11  : (213660/100000 : ℝ) < majorant 11 ∧ majorant 11 ≤ (213661/100000 : ℝ) := by
  convert Proofs.table3_rounding_11.1 using 1 <;> norm_num

/-- table3_target_rounding_11. -/
theorem table3_target_rounding_11  : (233187/100000 : ℝ) ≤ target 11 ∧ target 11 < (233188/100000 : ℝ) := by
  convert Proofs.table3_rounding_11.2 using 1 <;> norm_num

/-- table3_M_rounding_12. -/
theorem table3_M_rounding_12  : (215655/100000 : ℝ) < majorant 12 ∧ majorant 12 ≤ (215656/100000 : ℝ) := by
  convert Proofs.table3_rounding_12.1 using 1 <;> norm_num

/-- table3_target_rounding_12. -/
theorem table3_target_rounding_12  : (239028/100000 : ℝ) ≤ target 12 ∧ target 12 < (239029/100000 : ℝ) := by
  convert Proofs.table3_rounding_12.2 using 1 <;> norm_num

/-- table3_M_rounding_13. -/
theorem table3_M_rounding_13  : (217446/100000 : ℝ) < majorant 13 ∧ majorant 13 ≤ (217447/100000 : ℝ) := by
  convert Proofs.table3_rounding_13.1 using 1 <;> norm_num

/-- table3_target_rounding_13. -/
theorem table3_target_rounding_13  : (244051/100000 : ℝ) ≤ target 13 ∧ target 13 < (244052/100000 : ℝ) := by
  convert Proofs.table3_rounding_13.2 using 1 <;> norm_num

/-- table3_M_rounding_14. -/
theorem table3_M_rounding_14  : (219068/100000 : ℝ) < majorant 14 ∧ majorant 14 ≤ (219069/100000 : ℝ) := by
  convert Proofs.table3_rounding_14.1 using 1 <;> norm_num

/-- table3_target_rounding_14. -/
theorem table3_target_rounding_14  : (248430/100000 : ℝ) ≤ target 14 ∧ target 14 < (248431/100000 : ℝ) := by
  convert Proofs.table3_rounding_14.2 using 1 <;> norm_num

/-- table3_M_rounding_15. -/
theorem table3_M_rounding_15  : (220548/100000 : ℝ) < majorant 15 ∧ majorant 15 ≤ (220549/100000 : ℝ) := by
  convert Proofs.table3_rounding_15.1 using 1 <;> norm_num

/-- table3_target_rounding_15. -/
theorem table3_target_rounding_15  : (252292/100000 : ℝ) ≤ target 15 ∧ target 15 < (252293/100000 : ℝ) := by
  convert Proofs.table3_rounding_15.2 using 1 <;> norm_num

/-- table3_M_rounding_16. -/
theorem table3_M_rounding_16  : (221906/100000 : ℝ) < majorant 16 ∧ majorant 16 ≤ (221907/100000 : ℝ) := by
  convert Proofs.table3_rounding_16.1 using 1 <;> norm_num

/-- table3_target_rounding_16. -/
theorem table3_target_rounding_16  : (255730/100000 : ℝ) ≤ target 16 ∧ target 16 < (255731/100000 : ℝ) := by
  convert Proofs.table3_rounding_16.2 using 1 <;> norm_num

/-- table3_M_rounding_17. -/
theorem table3_M_rounding_17  : (223161/100000 : ℝ) < majorant 17 ∧ majorant 17 ≤ (223162/100000 : ℝ) := by
  convert Proofs.table3_rounding_17.1 using 1 <;> norm_num

/-- table3_target_rounding_17. -/
theorem table3_target_rounding_17  : (258817/100000 : ℝ) ≤ target 17 ∧ target 17 < (258818/100000 : ℝ) := by
  convert Proofs.table3_rounding_17.2 using 1 <;> norm_num

/-- table3_M_rounding_18. -/
theorem table3_M_rounding_18  : (224325/100000 : ℝ) < majorant 18 ∧ majorant 18 ≤ (224326/100000 : ℝ) := by
  convert Proofs.table3_rounding_18.1 using 1 <;> norm_num

/-- table3_target_rounding_18. -/
theorem table3_target_rounding_18  : (261609/100000 : ℝ) ≤ target 18 ∧ target 18 < (261610/100000 : ℝ) := by
  convert Proofs.table3_rounding_18.2 using 1 <;> norm_num

/-- table3_M_rounding_19. -/
theorem table3_M_rounding_19  : (225409/100000 : ℝ) < majorant 19 ∧ majorant 19 ≤ (225410/100000 : ℝ) := by
  convert Proofs.table3_rounding_19.1 using 1 <;> norm_num

/-- table3_target_rounding_19. -/
theorem table3_target_rounding_19  : (264150/100000 : ℝ) ≤ target 19 ∧ target 19 < (264151/100000 : ℝ) := by
  convert Proofs.table3_rounding_19.2 using 1 <;> norm_num

/-- table3_M_rounding_20. -/
theorem table3_M_rounding_20  : (226423/100000 : ℝ) < majorant 20 ∧ majorant 20 ≤ (226424/100000 : ℝ) := by
  convert Proofs.table3_rounding_20.1 using 1 <;> norm_num

/-- table3_target_rounding_20. -/
theorem table3_target_rounding_20  : (266476/100000 : ℝ) ≤ target 20 ∧ target 20 < (266477/100000 : ℝ) := by
  convert Proofs.table3_rounding_20.2 using 1 <;> norm_num

/-- disk_green_instance. -/
theorem disk_green_instance  : IsClassicalGreen (disk 1) 0 diskGreen := by
  exact Proofs.disk_green_instance_proved

/-- finite_green_exists. -/
theorem finite_green_exists (domain : Set ℂ) (hdomain : IsBoundedJordanDomain domain) (pole : ℂ) (hpole : pole ∈ domain) : ∃ green : ℂ → ℝ, IsClassicalGreen domain pole green := by
  sorry

/-- finite_green_conformal_invariance. -/
theorem finite_green_conformal_invariance (domain image : Set ℂ) (hdomain : IsBoundedJordanDomain domain) (himage : IsBoundedJordanDomain image) (func : ℂ → ℂ) (hfunc : IsConformalOnto func domain image) (pole point : ℂ) (hpole : pole ∈ domain) (hpoint : point ∈ domain) (hdistinct : point ≠ pole) (greenDomain greenImage : ℂ → ℝ) (hgreenDomain : IsClassicalGreen domain pole greenDomain) (hgreenImage : IsClassicalGreen image (func pole) greenImage) : greenImage (func point) = greenDomain point := by
  exact Proofs.finite_green_conformal_proved domain image hdomain himage func hfunc pole point
    hpole hpoint hdistinct greenDomain greenImage hgreenDomain hgreenImage

/-- exterior_green_exists. -/
theorem exterior_green_exists (domain : Set ℂ) (hdomain : IsBoundedJordanDomain domain) : ∃ green : ℂ → ℝ, IsClassicalExteriorGreen (closure domain) green := by
  sorry

/-- inversion_green_identity. -/
theorem inversion_green_identity (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0) (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (hcritical : critical ≠ 0) (homit : critical ∉ inverse '' disk 1) (greenExterior greenImage : ℂ → ℝ) (hgreenExterior : IsClassicalExteriorGreen (closure (inverseDomain inverse height)) greenExterior) (hgreenImage : IsClassicalGreen (exteriorImage inverse height critical) 0 greenImage) : greenExterior critical = greenImage (-1) := by
  exact Proofs.inversion_green_identity_proved inverse hinverse hzero height hheight
    critical hcritical homit greenExterior greenImage hgreenExterior hgreenImage

/-- bernstein_walsh. -/
theorem bernstein_walsh (domain : Set ℂ) (hdomain : IsBoundedJordanDomain domain) (poly : ℂ[X]) (green : ℂ → ℝ) (hgreen : IsClassicalExteriorGreen (closure domain) green) (point : ℂ) (hpoint : point ∉ closure domain) : ‖poly.eval point‖ ≤ sSup ((fun value : ℂ => ‖poly.eval value‖) '' closure domain)*Real.exp ((poly.natDegree : ℝ)*green point) := by
  sorry

/-- dubinin_polynomial_specialization. -/
theorem dubinin_polynomial_specialization (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly) (domain : Set ℂ) (hdomain : IsBoundedJordanDomain domain) (height : ℝ) (hheight : height ∈ Ioo 0 1) (hboundary : ∀ point ∈ frontier domain, ‖poly.eval point‖ = height) (green : ℂ → ℝ) (hgreen : IsClassicalExteriorGreen (closure domain) green) (critical : ℂ) (hcritical : critical ∉ closure domain) (hvalue : ‖poly.eval critical‖ = 1) : Real.log (1/height) ≤ (degree : ℝ)*green critical := by
  sorry

/-- jatar_ng_boundary_critical_exists. -/
theorem jatar_ng_boundary_critical_exists (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsSchlichtNormalized degree poly) : ∃ point ∈ frontier (lemniscateComponent poly 1), point ∈ criticalPoints poly := by
  exact Proofs.jatar_ng_boundary_critical_exists_proved degree hdegree poly hpoly

/-- jatar_ng_leading_coefficient. -/
theorem jatar_ng_leading_coefficient (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsSchlichtNormalized degree poly) : 0 < ‖poly.leadingCoeff‖ ∧ ‖poly.leadingCoeff‖ < 1 := by
  exact ⟨Proofs.schlicht_leading_coefficient_pos degree hdegree poly hpoly,
    Cited.jatar_ng_2026_sec1_2_leading_lt_one degree hdegree poly hpoly⟩

/-- jatar_ng_source_v. -/
theorem jatar_ng_source_v (degree : ℕ) (hdegree : 169 ≤ degree) (poly : ℂ[X]) (hpoly : IsSchlichtNormalized degree poly) (hlog : (Real.log (1/‖poly.leadingCoeff‖))^2 ≤ (degree : ℝ)) (point : ℂ) (hpoint : point ∈ criticalPoints poly) (hboundary : point ∈ frontier (lemniscateComponent poly 1)) : criticalRatio poly point ≤ jatarNgBound degree := by
  exact Cited.jatar_ng_2026_theorem1_v degree hdegree poly hpoly hlog point hpoint hboundary

/-- jatar_ng_printed_bound. -/
theorem jatar_ng_printed_bound (degree : ℕ) (hdegree : 169 ≤ degree) (poly : ℂ[X]) (hpoly : IsSchlichtNormalized degree poly) (hleading : Real.exp (-Real.sqrt degree) ≤ ‖poly.leadingCoeff‖) : S poly ≤ jatarNgBound degree := by
  exact Proofs.jatar_printed_bound_from_sources Cited.jatar_ng_2026_theorem1_v
    Cited.jatar_ng_2026_sec1_2_leading_lt_one degree hdegree poly hpoly hleading

/-- jatar_ng_bound_limit. -/
theorem jatar_ng_bound_limit  : Tendsto jatarNgBound atTop (𝓝 1) := by
  exact Proofs.jatar_ng_bound_limit_proved

/-- finite_box_soundness. -/
theorem finite_box_soundness (degree : ℕ) (hdegree : degree = 7 ∨ degree = 8) (boxes : List CertifiedBoxData) (hnonempty : boxes ≠ []) (hvalid : ∀ box ∈ boxes, ValidBox box) (hcover : CoversUnit boxes) (hendpoint : ∀ box ∈ boxes, BoxEndpointBound degree box) (cutoff : ℝ) (hcutoff : ∀ box ∈ boxes, cutoff < (box.lower : ℝ)) (htail : cutoff < Real.exp (6/7)) : cutoff < bestBound degree := by
  exact Proofs.finite_box_soundness_from_dlmf Cited.dlmf_19_9_5 degree hdegree boxes hnonempty
    hvalid hcover hendpoint cutoff hcutoff htail

/-- range7_finite_certificate. -/
theorem range7_finite_certificate  : ∃ boxes : List CertifiedBoxData, CoversUnit boxes ∧ ∀ box ∈ boxes, ValidBox box ∧ BoxEndpointBound 7 box ∧ (20190/10000 : ℝ) < (box.lower : ℝ) := by
  have hcover := Proofs.dyadic_unit_cover Proofs.cover7_tree
  have hleaves := (Proofs.tree_boxes_all (fun box => BoxEndpointBound 7 box ∧
    (2019/1000 : ℝ) < (box.lower : ℝ)) Proofs.cover7_tree 0 1).mpr
    (Proofs.cover7_tree_checked Cited.dlmf_19_8_5)
  refine ⟨Proofs.treeBoxes Proofs.cover7_tree 0 1, hcover.2.1, ?_⟩
  intro box hbox
  refine ⟨hcover.2.2 box hbox, (hleaves box hbox).1, ?_⟩
  convert (hleaves box hbox).2 using 1 <;> norm_num

/-- range8_finite_certificate. -/
theorem range8_finite_certificate  : ∃ boxes : List CertifiedBoxData, CoversUnit boxes ∧ ∀ box ∈ boxes, ValidBox box ∧ BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ) := by
  have hcover := Proofs.dyadic_unit_cover Proofs.cover8_tree
  have hleaves := (Proofs.tree_boxes_all (fun box => BoxEndpointBound 8 box ∧
    (20549/10000 : ℝ) < (box.lower : ℝ)) Proofs.cover8_tree 0 1).mpr
    (Proofs.cover8_tree_checked Cited.dlmf_19_8_5)
  refine ⟨Proofs.treeBoxes Proofs.cover8_tree 0 1, hcover.2.1, ?_⟩
  intro box hbox
  exact ⟨hcover.2.2 box hbox, (hleaves box hbox).1, (hleaves box hbox).2⟩

/-- s_pos_of_critical_values_ne_zero. -/
theorem s_pos_of_critical_values_ne_zero (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly) (hvalues : ∀ point ∈ criticalPoints poly, poly.eval point ≠ 0) : 0 < S poly := by
  exact Proofs.s_pos_of_critical_values_ne_zero_proved degree hdegree poly hpoly hvalues

/-- ybound_gt_rpow. -/
theorem ybound_gt_rpow (degree : ℕ) (hdegree : 2 ≤ degree) (height : ℝ) (hheight : height ∈ Ioo 0 1) : height^((1/(degree : ℝ))-1) < yBound degree height := by
  exact Proofs.ybound_gt_rpow_from_log_upper mu_log_upper degree hdegree height hheight

/-- koebe_quarter_omission. -/
theorem koebe_quarter_omission (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0) (point : ℂ) (homit : point ∉ inverse '' disk 1) : ‖deriv inverse 0‖/4 ≤ ‖point‖ := by
  exact Proofs.koebe_quarter_omission_public030 inverse hinverse hzero point homit

/-- lambda_chosen_identity. -/
theorem lambda_chosen_identity (degree : ℕ) (hdegree : 8 ≤ degree) : lambda degree (Lchoice degree) = ell degree+Real.log (32*ell degree)-Real.log (1-Lchoice degree/degree) := by
  exact Proofs.lambda_chosen_identity degree hdegree

/-- tail_numerical_endpoints. -/
theorem tail_numerical_endpoints  : Real.log (32*Real.log 21)/Real.log 21 < (152/100 : ℝ) ∧ -Real.log (1-(42/10000 : ℝ)) < 5/1000 := by
  exact Proofs.tail_numerical_endpoints_proved

/-- fujikawa_identity. -/
theorem fujikawa_identity (degree : ℕ) (hdegree : 2 ≤ degree) : fujikawa degree = 4-4*(((degree : ℝ)-2)*(1-(4 : ℝ)^(-1/((degree : ℝ)-1)))+2)/((degree : ℝ)+1) := by
  exact Proofs.fujikawa_identity_proved degree hdegree

/-- earlier_q_log_bound. -/
theorem earlier_q_log_bound (degree : ℕ) (hdegree : 2 ≤ degree) : 1-(4 : ℝ)^(-1/((degree : ℝ)-1)) ≤ Real.log 4/((degree : ℝ)-1) := by
  exact Proofs.earlier_q_log_bound_proved degree hdegree

/-- earlier_bracket_bound. -/
theorem earlier_bracket_bound (degree : ℕ) (hdegree : 8 ≤ degree) : ((degree : ℝ)-2)*(1-(4 : ℝ)^(-1/((degree : ℝ)-1)))+2 < Real.log 4+2 ∧ Real.log 4+2 < 339/100 := by
  exact Proofs.earlier_bracket_bound_proved degree hdegree

/-- earlier_endpoint_8. -/
theorem earlier_endpoint_8  : (432/100 : ℝ) < 9/Real.log 8 := by
  exact Proofs.earlier_endpoint_eight_proved

/-- earlier_difference_formulas. -/
theorem earlier_difference_formulas (degree : ℕ) (hdegree : 8 ≤ degree) : let quotient : ℝ := (4 : ℝ)^(-1/((degree : ℝ)-1)); conte degree-fujikawa degree = 4*((degree : ℝ)-2)*(1-quotient)/((degree : ℝ)+1) ∧ beardon degree-fujikawa degree = 4*(3*quotient-1)/((degree : ℝ)+1) ∧ dubinin degree-fujikawa degree = 4*((2*(degree : ℝ)-1)*quotient-degree)/((degree : ℝ)*((degree : ℝ)+1)) := by
  exact Proofs.earlier_difference_formulas_proved degree hdegree

/-- earlier_q_half. -/
theorem earlier_q_half (degree : ℕ) (hdegree : 3 ≤ degree) : (1/2 : ℝ) ≤ (4 : ℝ)^(-1/((degree : ℝ)-1)) := by
  exact Proofs.earlier_q_half_proved degree hdegree

/-- earlier_q_eight. -/
theorem earlier_q_eight (degree : ℕ) (hdegree : 8 ≤ degree) : (4 : ℝ)^(-1/7 : ℝ) ≤ (4 : ℝ)^(-1/((degree : ℝ)-1)) ∧ (4/5 : ℝ) < (4 : ℝ)^(-1/7 : ℝ) ∧ (degree : ℝ)/(2*(degree : ℝ)-1) < (4/5 : ℝ) := by
  exact Proofs.earlier_q_eight_proved degree hdegree

/-- prop_mu_complement_lower. -/
theorem prop_mu_complement_lower (degree : ℕ) (hdegree : 8 ≤ degree) (length : ℝ) (hlength : length ∈ Ioo 0 2) : Real.log (4/complement (radius degree length))-length/degree < mu (complement (radius degree length)) := by
  exact Proofs.prop_mu_complement_lower_from_dlmf Cited.dlmf_19_9_5 degree (by omega) length hlength.1

/-- prop_log_complement_lower. -/
theorem prop_log_complement_lower (degree : ℕ) (hdegree : 8 ≤ degree) (length : ℝ) (hlength : length ∈ Ioo 0 2) : (1/2)*Real.log (8*degree/length) ≤ Real.log (4/complement (radius degree length)) := by
  exact Proofs.prop_log_complement_lower degree (by omega) length hlength.1

/-- prop_delta_elementary_lower. -/
theorem prop_delta_elementary_lower (degree : ℕ) (hdegree : 8 ≤ degree) (length : ℝ) (hlength : length ∈ Ioo 0 2) : 2*Real.log (4*degree)-8/degree < delta degree length := by
  exact Proofs.prop_delta_elementary_lower degree hdegree length hlength

/-- jn_radius_well_defined. -/
theorem jn_radius_well_defined (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly) :
    (univalentRadii poly).Nonempty ∧ BddAbove (univalentRadii poly) ∧
    0 < maxUnivalentRadius poly ∧ maxUnivalentRadius poly ∈ univalentRadii poly := by
  exact Proofs.jn_radius_well_defined_proved degree hdegree poly hpoly

/-- jn_normalization_witness. -/
theorem jn_normalization_witness :
    IsSchlichtNormalized 2 (Polynomial.X - Polynomial.C (1/4 : ℂ)*Polynomial.X^2) := by
  exact Proofs.jn_normalization_witness_proved

/-! ## NOT stated
(NgreenGeneral) [out of scope] the general
potential-theoretic Green theory for arbitrary irregular domains is not formalized here.
Concrete classical Jordan-domain instances have OPEN typed rows; they are not the general theorem.
(NdubininGeneral) [out of scope] Dubinin's general
spherical meromorphic inequality with a complete multiplicity-counted pole fiber is not
formalized. Its polynomial specialization has an OPEN row; no general result is imported.
(NcapacityPotential) [absorbed boundary] 
potential-theoretic capacity is not defined. Fekete–Szegő is absorbed into the TD coefficient
boundary, which must cite Ransford5.2.3 / Cor5.2.2 AND5.5.2. No theorem is proved by the alias. -/
/-- conditional riemann_map_for_exterior; the unconditional row stays open. -/
theorem riemann_map_for_exterior_given_jordan (hjordan : Background.JordanCurveFact)
    (domain : Set ℂ) (hdomain : IsBoundedJordanDomain domain) (hzero : (0 : ℂ) ∈ domain) :
    ∃ func : ℂ → ℂ, IsConformalOnto func (disk 1) domain ∧ func 0 = 0 := by
  exact Proofs.riemann_map_given_jordan hjordan domain hdomain hzero

/-- conditional coefficient upper bound; the unconditional row stays open. -/
theorem capacity_conformal_coefficient_given_background (hcoefficientFact : Background.CoefficientUpperFact)
    (compactSet : Set ℂ) (hcompact : IsCompact compactSet) (hconnected : IsConnected compactSet)
    (hnontrivial : ∃ first ∈ compactSet, ∃ second ∈ compactSet, first ≠ second)
    (hcomplement : IsConnected compactSetᶜ) (phi : ℂ → ℂ)
    (hphi : IsConformalOnto phi {point : ℂ | 1 < ‖point‖} compactSetᶜ)
    (coefficient : ℂ) (hcoefficient : coefficient ≠ 0)
    (hexpansion : ∃ constant : ℂ, Tendsto (fun point : ℂ => phi point - coefficient * point)
      (cocompact ℂ) (𝓝 constant)) : capacityTD compactSet ≤ ‖coefficient‖ := by
  exact hcoefficientFact compactSet hcompact hconnected hnontrivial hcomplement
    phi hphi coefficient hcoefficient hexpansion


/-- conditional exterior_image_geometry; the original is now independently proved without this premise. -/
theorem exterior_image_geometry_given_jordan (hjordan : Background.JordanCurveFact)
    (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (hcritical : critical ≠ 0)
    (homit : critical ∉ inverse '' disk 1) :
    IsBoundedJordanDomain (exteriorImage inverse height critical) ∧
      (0 : ℂ) ∈ exteriorImage inverse height critical ∧ (-1 : ℂ) ∈ exteriorImage inverse height critical := by
  exact Proofs.exterior_image_geometry_given_jordan hjordan inverse hinverse hzero height hheight
    critical hcritical homit


/-- conditional polynomial bound with both named facts explicit. -/
theorem polynomial_bound_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 2 ≤ degree)
    (poly : ℂ[X]) (hpoly : IsPd degree poly) (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    S poly ≤ yBound degree height := by
  exact Proofs.polynomial_bound_given_facts hjordan hcoefficient mu_decreasing.antitoneOn
    Cited.betsakos_2013 degree hdegree poly hpoly height hheight

/-- conditional Theorem1.1; original unconditional row stays open. -/
theorem thm_1_1_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 2 ≤ degree)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) : Kd degree ≤ (yBound degree height : EReal) := by
  unfold Kd
  apply iSup_le
  intro poly
  exact_mod_cast polynomial_bound_given_background hjordan hcoefficient degree hdegree poly.val poly.property height hheight

/-- conditional Corollary1.2; original unconditional row stays open. -/
theorem cor_1_2_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 8 ≤ degree) :
    Kd degree < (target degree : EReal) := by
  apply Proofs.cor_1_2_of_ybound Cited.dlmf_19_9_5 degree hdegree
  have hlength := (Proofs.chosen_length_bounds degree hdegree).1
  exact thm_1_1_given_background hjordan hcoefficient degree (by omega) (Real.exp (-Lchoice degree))
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos hlength)⟩

/-- conditional small-degree bound; explicit named facts retained. -/
theorem small_bound_below_39_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 2 ≤ degree) (hupper : degree ≤ 7) :
    Kd degree ≤ ((Real.rpow 4 (5/6) : ℝ) : EReal) ∧ (4 : ℝ)^(5/6 : ℝ) < 39/10 := by
  apply Proofs.small_bound_below_39_of_ybound Cited.dlmf_19_9_5 degree hdegree hupper
  exact thm_1_1_given_background hjordan hcoefficient degree hdegree (Real.exp (-(1/10 : ℝ)))
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by norm_num)⟩

/-- conditional intermediate degree bound; original remains open. -/
theorem bounds_below_39_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 8 ≤ degree)
    (hupper : (degree : ℝ) ≤ Real.exp 40) : Kd degree < ((39/10 : ℝ) : EReal) := by
  exact Proofs.bounds_below_39_of_corollary degree hdegree hupper
    (cor_1_2_given_background hjordan hcoefficient degree hdegree)

/-- conditional 3.9 degree example; original remains open. -/
theorem degree_example_39_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 2 ≤ degree)
    (poly : ℂ[X]) (hpoly : IsPd degree poly) (hlarge : 39/10 ≤ S poly) : 2 * 10^17 < degree := by
  apply Proofs.degree_example_39_of_bounds ?_ (cor_1_2_given_background hjordan hcoefficient)
    degree hdegree poly hpoly hlarge
  intro small hsmall hupper
  have hbound := small_bound_below_39_given_background hjordan hcoefficient small hsmall hupper
  exact hbound.1.trans_lt (by exact_mod_cast hbound.2)

/-- conditional strict all-degree bound; original remains open. -/
theorem kd_lt_four_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 2 ≤ degree) : Kd degree < (4 : EReal) := by
  by_cases hsmall : degree ≤ 7
  · have hbound := small_bound_below_39_given_background hjordan hcoefficient degree hdegree hsmall
    have hreal : (4 : ℝ)^(5/6 : ℝ) < 4 := hbound.2.trans (by norm_num)
    exact hbound.1.trans_lt (EReal.coe_lt_coe hreal)
  · have hdegree8 : 8 ≤ degree := by omega
    have hell : 0 < ell degree := lt_trans (by norm_num) (Proofs.ell_gt_one degree hdegree8)
    have htarget : target degree < 4 := by unfold target; exact sub_lt_self _ (div_pos (by norm_num) hell)
    exact (cor_1_2_given_background hjordan hcoefficient degree hdegree8).trans
      (EReal.coe_lt_coe htarget)

/-- conditional weak all-degree bound; original remains open. -/
theorem smale_bound_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 2 ≤ degree) : Kd degree ≤ (4 : EReal) := by
  exact (kd_lt_four_given_background hjordan hcoefficient degree hdegree).le

/-- conditional supremum finiteness; original unconditional row remains open. -/
theorem kd_finite_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 2 ≤ degree) :
    Kd degree ≠ ⊥ ∧ Kd degree ≠ ⊤ := by
  refine ⟨Proofs.kd_ne_bot degree hdegree, ?_⟩
  intro heq
  have hbound := kd_lt_four_given_background hjordan hcoefficient degree hdegree
  simp [heq] at hbound

/-- conditional optimized bound; original unconditional row remains open. -/
theorem kd_le_best_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 2 ≤ degree) :
    Kd degree ≤ (bestBound degree : EReal) := by
  unfold Kd
  apply iSup_le
  intro poly
  apply EReal.coe_le_coe
  unfold bestBound
  apply le_csInf (Proofs.bound_set_well_defined degree).1
  rintro value ⟨height, hheight, rfl⟩
  exact polynomial_bound_given_background hjordan hcoefficient degree hdegree poly.val poly.property height hheight

/-- conditional K-gap consequence; original unconditional row remains open. -/
theorem weaker_k_gap_liminf_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ degree : ℕ in atTop, Kd degree ≤ ((4 - (2*Real.pi^2-epsilon)/ell degree : ℝ) : EReal) := by
  exact Proofs.weaker_k_gap_liminf_of_best
    (fun degree hdegree => kd_le_best_given_background hjordan hcoefficient degree (by omega))
    prop_3_4_limit epsilon hepsilon

/-- conditional Crane comparison for Kd; original remains open. -/
theorem crane_bound_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 8 ≤ degree) :
    Kd degree < (crane degree : EReal) := by
  exact (cor_1_2_given_background hjordan hcoefficient degree hdegree).trans
    (EReal.coe_lt_coe (earlier_crane_comparison degree hdegree))

/-- conditional Step1 majorant; original remains open. -/
theorem cor_step1_majorant_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 8 ≤ degree) :
    beta degree (Lchoice degree) < majorant degree ∧ Kd degree < (majorant degree : EReal) := by
  have hbeta := Proofs.cor_step1_majorant_from_dlmf Cited.dlmf_19_9_5 degree hdegree
  refine ⟨hbeta, ?_⟩
  have hlength := (Proofs.chosen_length_bounds degree hdegree).1
  have hbound := thm_1_1_given_background hjordan hcoefficient degree (by omega)
    (Real.exp (-Lchoice degree)) ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos hlength)⟩
  rw [Proofs.ybound_exp_eq_beta] at hbound
  exact hbound.trans_lt (EReal.coe_lt_coe hbeta)

/-- conditional excluded-region bound; original remains open. -/
theorem figure1_excluded_regions_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 8 ≤ degree) :
    Kd degree ≤ ((min (fujikawa degree) (crane degree) : ℝ) : EReal) ∧
      bestBound degree < min (fujikawa degree) (crane degree) := by
  have htarget : target degree < min (fujikawa degree) (crane degree) :=
    lt_min (earlier_fujikawa_comparison degree hdegree) (earlier_crane_comparison degree hdegree)
  have hbest := best_strict_improvement degree hdegree
  exact ⟨(cor_1_2_given_background hjordan hcoefficient degree hdegree).le.trans
    (EReal.coe_le_coe htarget.le), (hbest.1.trans_le hbest.2).trans htarget⟩


/-- scalar margins for the nine printed Crane numbers; no Kd hypothesis. -/
theorem crane_numeric_margins : ∀ entry ∈
    ([(8,3124),(9,3150),(10,3169),(11,3188),(12,3208),(16,3271),(25,3365),(100,3621),(10000,3955)] : List (ℕ × ℕ)),
    (389/1000 : ℝ) < (entry.2 : ℝ)/1000-target entry.1 ∧
      (entry.1 ≠ 10000 → (2/5 : ℝ) < (entry.2 : ℝ)/1000-target entry.1) := by
  exact Proofs.crane_numeric_margins

/-- conditional nine-number Crane comparison; original unconditional rows remain open. -/
theorem crane_numbers_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    ∀ entry ∈ ([(8,3124),(9,3150),(10,3169),(11,3188),(12,3208),(16,3271),(25,3365),(100,3621),(10000,3955)] : List (ℕ × ℕ)),
    Kd entry.1 < (((entry.2 : ℝ)/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < (entry.2 : ℝ)/1000-target entry.1 := by
  exact Proofs.crane_numeric_of_corollary (cor_1_2_given_background hjordan hcoefficient)

/-- conditional Crane number at degree 8; original unconditional row remains open. -/
theorem crane_numeric_8_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    Kd 8 < ((3124/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < 3124/1000-target 8 := by
  simpa only [Prod.fst, Prod.snd, Nat.cast_ofNat] using
    crane_numbers_given_background hjordan hcoefficient (8,3124) (by simp)

/-- conditional Crane number at degree 9; original unconditional row remains open. -/
theorem crane_numeric_9_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    Kd 9 < ((3150/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < 3150/1000-target 9 := by
  simpa only [Prod.fst, Prod.snd, Nat.cast_ofNat] using
    crane_numbers_given_background hjordan hcoefficient (9,3150) (by simp)

/-- conditional Crane number at degree 10; original unconditional row remains open. -/
theorem crane_numeric_10_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    Kd 10 < ((3169/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < 3169/1000-target 10 := by
  simpa only [Prod.fst, Prod.snd, Nat.cast_ofNat] using
    crane_numbers_given_background hjordan hcoefficient (10,3169) (by simp)

/-- conditional Crane number at degree 11; original unconditional row remains open. -/
theorem crane_numeric_11_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    Kd 11 < ((3188/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < 3188/1000-target 11 := by
  simpa only [Prod.fst, Prod.snd, Nat.cast_ofNat] using
    crane_numbers_given_background hjordan hcoefficient (11,3188) (by simp)

/-- conditional Crane number at degree 12; original unconditional row remains open. -/
theorem crane_numeric_12_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    Kd 12 < ((3208/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < 3208/1000-target 12 := by
  simpa only [Prod.fst, Prod.snd, Nat.cast_ofNat] using
    crane_numbers_given_background hjordan hcoefficient (12,3208) (by simp)

/-- conditional Crane number at degree 16; original unconditional row remains open. -/
theorem crane_numeric_16_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    Kd 16 < ((3271/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < 3271/1000-target 16 := by
  simpa only [Prod.fst, Prod.snd, Nat.cast_ofNat] using
    crane_numbers_given_background hjordan hcoefficient (16,3271) (by simp)

/-- conditional Crane number at degree 25; original unconditional row remains open. -/
theorem crane_numeric_25_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    Kd 25 < ((3365/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < 3365/1000-target 25 := by
  simpa only [Prod.fst, Prod.snd, Nat.cast_ofNat] using
    crane_numbers_given_background hjordan hcoefficient (25,3365) (by simp)

/-- conditional Crane number at degree 100; original unconditional row remains open. -/
theorem crane_numeric_100_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    Kd 100 < ((3621/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < 3621/1000-target 100 := by
  simpa only [Prod.fst, Prod.snd, Nat.cast_ofNat] using
    crane_numbers_given_background hjordan hcoefficient (100,3621) (by simp)

/-- conditional Crane number at degree 10000; original unconditional row remains open. -/
theorem crane_numeric_10000_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    Kd 10000 < ((3955/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < 3955/1000-target 10000 := by
  simpa only [Prod.fst, Prod.snd, Nat.cast_ofNat] using
    crane_numbers_given_background hjordan hcoefficient (10000,3955) (by simp)

/-- scalar Figure3 height lower bound; no Kd hypothesis. -/
theorem gap_gt_four (degree : ℕ) (hdegree : 8 ≤ degree) : 4 < gap degree := by
  have hell : 0 < ell degree := by linarith [Proofs.ell_gt_one degree hdegree]
  have hbest := (best_strict_improvement degree hdegree).1.trans_le
    (best_strict_improvement degree hdegree).2
  have hmul := mul_lt_mul_of_pos_right hbest hell
  have hid : target degree*ell degree = 4*ell degree-4 := by
    unfold target
    field_simp [ne_of_gt hell]
    <;> ring
  rw [hid] at hmul
  unfold gap
  nlinarith

/-- conditional Figure3 height; original unconditional row remains open. -/
theorem figure3_height_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 8 ≤ degree) :
    Kd degree ≤ ((4-gap degree/ell degree : ℝ) : EReal) ∧ 4 < gap degree := by
  have hell : 0 < ell degree := by linarith [Proofs.ell_gt_one degree hdegree]
  have hid : 4-gap degree/ell degree = bestBound degree := by
    unfold gap
    field_simp [ne_of_gt hell]
    <;> ring
  rw [hid]
  exact ⟨kd_le_best_given_background hjordan hcoefficient degree (by omega), gap_gt_four degree hdegree⟩

/-- degree-seven target comparison; independent of the bestBound enclosure. -/
theorem degree_seven_target_upper : target 7 < (19445/10000 : ℝ) := by
  exact Proofs.degree_seven_target_upper

/-- degree-seven older-bound minimum and printed decimal enclosure. -/
theorem fujikawa_seven_scalar :
    fujikawa 7 ≤ conte 7 ∧ fujikawa 7 ≤ beardon 7 ∧ fujikawa 7 ≤ dubinin 7 ∧
      (24842/10000 : ℝ) < fujikawa 7 ∧ fujikawa 7 < 24843/10000 := by
  exact Proofs.fujikawa_seven_scalar

/-- elementary target entries in Table2, independent of the elliptic beta columns. -/
theorem table2_target_columns : target 8 ≤ (20765/10000 : ℝ) ∧
    target 100 ≤ (31315/10000 : ℝ) ∧ target 10000 ≤ (35658/10000 : ℝ) ∧
    target 1000000 ≤ (37105/10000 : ℝ) := by
  exact Proofs.table2_target_bounds

/-- finite Green existence from the analytic RMT; original unconditional row remains open. -/
theorem finite_green_exists_given_jordan (hjordan : Background.JordanCurveFact)
    (domain : Set ℂ) (hdomain : IsBoundedJordanDomain domain) (pole : ℂ) (hpole : pole ∈ domain) :
    ∃ green : ℂ → ℝ, IsClassicalGreen domain pole green := by
  exact Proofs.finite_green_given_jordan hjordan domain hdomain pole hpole

/-- component-frontier polynomial modulus at the defining radius. -/
theorem lemniscate_frontier_value (poly : ℂ[X]) (hzero : poly.eval 0 = 0)
    (height : ℝ) (hheight : 0 < height) (point : ℂ)
    (hpoint : point ∈ frontier (lemniscateComponent poly height)) : ‖poly.eval point‖ = height := by
  exact Proofs.lemniscate_frontier_norm poly hzero height hheight point hpoint

/-- normalized boundary-critical witness has unit polynomial modulus. -/
theorem jatar_ng_boundary_value (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X])
    (hpoly : IsSchlichtNormalized degree poly) :
    ∃ point ∈ frontier (lemniscateComponent poly 1), point ∈ criticalPoints poly ∧ ‖poly.eval point‖ = 1 := by
  exact Proofs.schlicht_boundary_critical_witness degree hdegree poly hpoly

/-- positive leading coefficient; the strict upper bound is a separate cited row. -/
theorem jatar_ng_leading_coefficient_positive (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X])
    (hpoly : IsSchlichtNormalized degree poly) : 0 < ‖poly.leadingCoeff‖ := by
  exact Proofs.schlicht_leading_coefficient_pos degree hdegree poly hpoly

/-- strict leading-coefficient upper restriction, direct external restatement. -/
theorem jatar_ng_leading_lt_one (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X])
    (hpoly : IsSchlichtNormalized degree poly) : ‖poly.leadingCoeff‖ < 1 := by
  exact Cited.jatar_ng_2026_sec1_2_leading_lt_one degree hdegree poly hpoly

/-- strict upper half of the degree-seven best-bound enclosure; lower cover remains separate. -/
theorem best_seven_upper : bestBound 7 < (20191/10000 : ℝ) := by
  apply Proofs.best_bound_upper_of_beta_strict 7 (13621/100000) _ (by norm_num)
  convert Proofs.point7_certificate Cited.dlmf_19_8_5 using 1 <;> norm_num

/-- strict upper half of the degree-eight best-bound enclosure; lower cover remains separate. -/
theorem best_eight_upper : bestBound 8 < (20550/10000 : ℝ) := by
  apply Proofs.best_bound_upper_of_beta_strict 8 (12766/100000) _ (by norm_num)
  convert Proofs.point8_certificate Cited.dlmf_19_8_5 using 1 <;> norm_num

/-- historical conditional Green coverage from disk coordinates; the original is independently proved without this premise. -/
theorem finite_green_conformal_invariance_given_jordan (hjordan : Background.JordanCurveFact)
    (domain image : Set ℂ) (hdomain : IsBoundedJordanDomain domain)
    (himage : IsBoundedJordanDomain image) (func : ℂ → ℂ)
    (hfunc : IsConformalOnto func domain image) (pole point : ℂ)
    (hpole : pole ∈ domain) (hpoint : point ∈ domain) (hdistinct : point ≠ pole)
    (greenDomain greenImage : ℂ → ℝ)
    (hgreenDomain : IsClassicalGreen domain pole greenDomain)
    (hgreenImage : IsClassicalGreen image (func pole) greenImage) :
    greenImage (func point) = greenDomain point := by
  exact Proofs.finite_green_conformal_given_jordan hjordan domain image hdomain himage
    func hfunc pole point hpole hpoint hdistinct greenDomain greenImage hgreenDomain hgreenImage

/-- upper half of the concrete capacity formula; the original equality remains open. -/
theorem capacity_exterior_upper_given_coefficient
    (hcoefficient : Background.CoefficientUpperFact)
    (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (hcritical : critical ≠ 0)
    (homit : critical ∉ inverse '' disk 1) :
    capacityTD (closure (exteriorImage inverse height critical)) ≤
      ‖critical‖ / (height * ‖deriv inverse 0‖) := by
  exact Proofs.capacity_exterior_upper_given_coefficient hcoefficient inverse hinverse hzero
    height hheight critical hcritical homit

/-- degree-seven comparison with explicit main-theorem premises; original unconditional row remains open. -/
theorem range_7_best_improvement_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    target 7 < bestBound 7 ∧ Kd 7 ≤ (bestBound 7 : EReal) ∧
      fujikawa 7 ≤ conte 7 ∧ fujikawa 7 ≤ beardon 7 ∧ fujikawa 7 ≤ dubinin 7 ∧
      (24842/10000 : ℝ) < fujikawa 7 ∧ fujikawa 7 < 24843/10000 := by
  exact Proofs.range_seven_best_improvement_of_bounds
    (Proofs.certified_seven_enclosure Cited.dlmf_19_8_5 Cited.dlmf_19_9_5).1
    (kd_le_best_given_background hjordan hcoefficient 7 (by norm_num))

end SmaleRate.Paper

