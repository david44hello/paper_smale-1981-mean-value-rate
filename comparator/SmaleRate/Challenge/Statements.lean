/-
SmaleRate — comparator challenge statements (proof bodies left open).
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Defs.Basic
public import SmaleRate.Defs.AnalyticBackground
public import SmaleRate.Cited.Approved
public import SmaleRate.Cited.JatarNg
public import SmaleRate.Defs.BackgroundFacts

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Paper
open SmaleRate Polynomial Filter Set MeasureTheory
open scoped Topology

/-- minimum_attained. -/
theorem minimum_attained (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly) :
    (criticalPoints poly).Finite ∧ (criticalPoints poly).Nonempty ∧
    ∃ point ∈ criticalPoints poly, S poly = criticalRatio poly point :=
  sorry

/-- critical_nonzero. -/
theorem critical_nonzero (degree : ℕ) (poly : ℂ[X]) (hpoly : IsPd degree poly) :
    ∀ point ∈ criticalPoints poly, point ≠ 0 :=
  sorry

/-- critical_ratio_norm_formula. -/
theorem critical_ratio_norm_formula (poly : ℂ[X]) (point : ℂ) :
    criticalRatio poly point = ‖poly.eval point‖ / (‖point‖ * ‖poly.derivative.eval 0‖) :=
  sorry

/-- s_nonneg. -/
theorem s_nonneg (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly) : 0 ≤ S poly :=
  sorry

/-- s_le_ratio. -/
theorem s_le_ratio (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (point : ℂ) (hpoint : point ∈ criticalPoints poly) : S poly ≤ criticalRatio poly point :=
  sorry

/-- scalar_invariance. -/
theorem scalar_invariance (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (scalar : ℂ) (hscalar : scalar ≠ 0) :
    IsPd degree (Polynomial.C scalar * poly) ∧
    criticalPoints (Polynomial.C scalar * poly) = criticalPoints poly ∧
    S (Polynomial.C scalar * poly) = S poly :=
  sorry

/-- zero_critical_value. -/
theorem zero_critical_value (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (point : ℂ) (hpoint : point ∈ criticalPoints poly) (hvalue : poly.eval point = 0) : S poly = 0 :=
  sorry

/-- critical_value_normalization. -/
theorem critical_value_normalization (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (hvalues : ∀ point ∈ criticalPoints poly, poly.eval point ≠ 0) :
    ∃ scalar : ℝ, 0 < scalar ∧ ∃ point : ℂ,
      NormalizedCriticalValues (Polynomial.C (scalar : ℂ) * poly) point :=
  sorry

/-- kd_finite. -/
theorem kd_finite (degree : ℕ) (hdegree : 2 ≤ degree) : Kd degree ≠ ⊥ ∧ Kd degree ≠ ⊤ :=
  sorry

/-- smale_bound. -/
theorem smale_bound (degree : ℕ) (hdegree : 2 ≤ degree) : Kd degree ≤ (4 : EReal) :=
  sorry

/-- small_degrees. -/
theorem small_degrees (degree : ℕ) (hdegree : 2 ≤ degree) (hupper : degree ≤ 4) :
    Kd degree = (((degree : ℝ) - 1) / degree : ℝ) :=
  sorry

/-- small_degrees_two_three. -/
theorem small_degrees_two_three (degree : ℕ) (hdegree : 2 ≤ degree) (hupper : degree ≤ 3) :
    Kd degree = (((degree : ℝ) - 1) / degree : ℝ) :=
  sorry

/-- counterexample_exists. -/
theorem counterexample_exists : ∃ degree : ℕ, 2 ≤ degree ∧ (1 : EReal) < Kd degree :=
  sorry

/-- counterexample_explicit_degree. -/
theorem counterexample_explicit_degree : (1 : EReal) < Kd 29984 :=
  sorry

/-- jatar_ng_lower. -/
theorem jatar_ng_lower : ((11018 / 10000 : ℝ) : EReal) < Kstar :=
  sorry

/-- kd_monotone. -/
theorem kd_monotone : MonotoneOn Kd (Set.Ici 2) :=
  sorry

/-- kd_limit_and_sup. -/
theorem kd_limit_and_sup : Tendsto Kd atTop (𝓝 (4 : EReal)) ∧ Kstar = 4 :=
  sorry

/-- earlier_bounds. -/
theorem earlier_bounds (degree : ℕ) (hdegree : 2 ≤ degree) :
    Kd degree ≤ (beardon degree : EReal) ∧ Kd degree ≤ (conte degree : EReal) ∧
    Kd degree ≤ (fujikawa degree : EReal) ∧ Kd degree ≤ (dubinin degree : EReal) :=
  sorry

/-- crane_bound. -/
theorem crane_bound (degree : ℕ) (hdegree : 8 ≤ degree) : Kd degree < (crane degree : EReal) :=
  sorry

/-- expanded_lower_bound. -/
theorem expanded_lower_bound (degree : ℕ) (hdegree : 2 ≤ degree) : Kd degree ≤ ((4 - expandedLower degree : ℝ) : EReal) :=
  sorry

/-- expanded_upper_bound. -/
theorem expanded_upper_bound (degree : ℕ) (hdegree : Real.exp (104 * (10 : ℝ)^8) ≤ (degree : ℝ)) :
    ((4 - expandedUpper degree : ℝ) : EReal) ≤ Kd degree :=
  sorry

/-- expanded_crossover. -/
theorem expanded_crossover (degree : ℕ) (hdegree : 2 ≤ degree) (hlog : ell degree ≤ 36363) :
    expandedLower degree < 4 / ell degree :=
  sorry

/-- elliptic_integrable. -/
theorem elliptic_integrable (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) :
    IntervalIntegrable (fun param : ℝ => 1 / Real.sqrt ((1-param^2)*(1-modulus^2*param^2))) volume 0 1 :=
  sorry

/-- elliptic_positive. -/
theorem elliptic_positive (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) : 0 < ellipticK modulus :=
  sorry

/-- elliptic_increasing. -/
theorem elliptic_increasing : StrictMonoOn ellipticK (Ioo 0 1) :=
  sorry

/-- elliptic_continuous. -/
theorem elliptic_continuous : ContinuousOn ellipticK (Ioo 0 1) :=
  sorry

/-- elliptic_endpoints. -/
theorem elliptic_endpoints : Tendsto ellipticK (𝓝[>] 0) (𝓝 (Real.pi/2)) ∧
    Tendsto ellipticK (𝓝[<] 1) atTop :=
  sorry

/-- mu_decreasing. -/
theorem mu_decreasing : StrictAntiOn mu (Ioo 0 1) :=
  sorry

/-- mu_range. -/
theorem mu_range : mu '' Ioo 0 1 = Ioi 0 :=
  sorry

/-- mu_continuous. -/
theorem mu_continuous : ContinuousOn mu (Ioo 0 1) :=
  sorry

/-- mu_positive. -/
theorem mu_positive (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) : 0 < mu modulus :=
  sorry

/-- mu_endpoints. -/
theorem mu_endpoints : Tendsto mu (𝓝[>] 0) atTop ∧ Tendsto mu (𝓝[<] 1) (𝓝 0) :=
  sorry

/-- mu_complement. -/
theorem mu_complement (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) :
    mu modulus * mu (complement modulus) = Real.pi^2/4 :=
  sorry

/-- dlmf_19_9_5. -/
theorem dlmf_19_9_5 (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) :
    Real.log ((1+Real.sqrt (complement modulus))^2/modulus) < mu modulus ∧
    mu modulus < Real.log (2*(1+complement modulus)/modulus) :=
  sorry

/-- mu_log_upper. -/
theorem mu_log_upper (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) : mu modulus < Real.log (4/modulus) :=
  sorry

/-- mu_small_error. -/
theorem mu_small_error : ∃ constant ≥ (0 : ℝ), ∀ᶠ modulus in 𝓝[>] (0 : ℝ),
    |mu modulus - Real.log (4/modulus)| ≤ constant * modulus^2 :=
  sorry

/-- mu_near_one. -/
theorem mu_near_one : Tendsto (fun modulus : ℝ => mu modulus /
    (Real.pi^2/(2*Real.log (16/(1-modulus^2))))) (𝓝[<] 1) (𝓝 1) :=
  sorry

/-- thm_1_1. -/
theorem thm_1_1 (degree : ℕ) (hdegree : 2 ≤ degree) (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    Kd degree ≤ (yBound degree height : EReal) :=
  sorry

/-- cor_1_2. -/
theorem cor_1_2 (degree : ℕ) (hdegree : 8 ≤ degree) : Kd degree < (target degree : EReal) :=
  sorry

/-- ybound_at_zero. -/
theorem ybound_at_zero (degree : ℕ) (hdegree : 2 ≤ degree) : Tendsto (yBound degree) (𝓝[>] 0) atTop :=
  sorry

/-- ybound_at_one. -/
theorem ybound_at_one (degree : ℕ) (hdegree : 2 ≤ degree) : Tendsto (yBound degree) (𝓝[<] 1) (𝓝 4) :=
  sorry

/-- ybound_below_four_near_one. -/
theorem ybound_below_four_near_one (degree : ℕ) (hdegree : 2 ≤ degree) : ∀ᶠ height in 𝓝[<] (1 : ℝ), yBound degree height < 4 :=
  sorry

/-- kd_lt_four. -/
theorem kd_lt_four (degree : ℕ) (hdegree : 2 ≤ degree) : Kd degree < (4 : EReal) :=
  sorry

/-- ybound_fixed_y_limit. -/
theorem ybound_fixed_y_limit (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    Tendsto (fun degree : ℕ => yBound degree height) atTop (𝓝 (4/height)) :=
  sorry

/-- degree_example_39. -/
theorem degree_example_39 (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (hlarge : 39/10 ≤ S poly) : 2 * 10^17 < degree :=
  sorry

/-- inverse_branch_exists. -/
theorem inverse_branch_exists (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (critical : ℂ) (hnormal : NormalizedCriticalValues poly critical) :
    ∃ inverse : ℂ → ℂ, IsInverseBranch poly inverse :=
  sorry

/-- inverse_branch_properties. -/
theorem inverse_branch_properties (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (critical : ℂ) (hnormal : NormalizedCriticalValues poly critical)
    (inverse : ℂ → ℂ) (hinverse : IsInverseBranch poly inverse) :
    IsUnivalentOn inverse (disk 1) ∧ deriv inverse 0 = (poly.derivative.eval 0)⁻¹ ∧
    critical ∉ inverse '' disk 1 ∧ S poly ≤ ‖deriv inverse 0‖/‖critical‖ :=
  sorry

/-- inverse_jordan_domain. -/
theorem inverse_jordan_domain (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    IsBoundedJordanDomain (inverseDomain inverse height) ∧
    closure (inverseDomain inverse height) = inverse '' Metric.closedBall 0 height ∧
    closure (inverseDomain inverse height) ⊆ inverse '' disk 1 :=
  sorry

/-- exterior_image_geometry. -/
theorem exterior_image_geometry (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (hcritical : critical ≠ 0)
    (homit : critical ∉ inverse '' disk 1) :
    IsBoundedJordanDomain (exteriorImage inverse height critical) ∧
    (0 : ℂ) ∈ exteriorImage inverse height critical ∧ (-1 : ℂ) ∈ exteriorImage inverse height critical :=
  sorry

/-- capacity_identity. -/
theorem capacity_identity (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (hcritical : critical ≠ 0)
    (homit : critical ∉ inverse '' disk 1) :
    capacityTD (closure (exteriorImage inverse height critical)) = ‖critical‖/(height*‖deriv inverse 0‖) :=
  sorry

/-- capacity_step_scalar. -/
theorem capacity_step_scalar (value height derivative critical cap : ℝ) (hvalue : 0 < value) (hheight : 0 < height)
    (hderivative : 0 < derivative) (hcritical : 0 < critical)
    (hbound : value ≤ derivative/critical) (hcap : cap = critical/(height*derivative)) : cap ≤ 1/(height*value) :=
  sorry

/-- riemann_map_for_exterior. -/
theorem riemann_map_for_exterior (domain : Set ℂ) (hdomain : IsBoundedJordanDomain domain) (hzero : (0 : ℂ) ∈ domain) :
    ∃ func : ℂ → ℂ, IsConformalOnto func (disk 1) domain ∧ func 0 = 0 :=
  sorry

/-- xi_bound. -/
theorem xi_bound (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (critical : ℂ) (hnormal : NormalizedCriticalValues poly critical)
    (inverse : ℂ → ℂ) (hinverse : IsInverseBranch poly inverse)
    (height : ℝ) (hheight : height ∈ Ioo 0 1)
    (func : ℂ → ℂ) (hfunc : IsConformalOnto func (disk 1) (exteriorImage inverse height critical))
    (hzero : func 0 = 0) (xi : ℂ) (hxi : xi ∈ disk 1) (hminusone : func xi = -1) :
    xi ≠ 0 ∧ ‖xi‖ ≤ height ^ (1/(degree : ℝ)) :=
  sorry

/-- betsakos_inequality. -/
theorem betsakos_inequality (func : ℂ → ℂ) (hhol : DifferentiableOn ℂ func (disk 1))
    (hbound : Bornology.IsBounded (func '' disk 1)) (hzero : func 0 = 0)
    (hnonconstant : ∃ first ∈ disk 1, ∃ second ∈ disk 1, func first ≠ func second)
    (point : ℂ) (hpoint : point ∈ disk 1) (hnonzero : point ≠ 0) :
    ‖func point‖ ≤ 4*transfiniteDiameter (func '' disk 1)*Real.exp (-mu ‖point‖) :=
  sorry

/-- betsakos_equality. -/
theorem betsakos_equality (func : ℂ → ℂ) (hhol : DifferentiableOn ℂ func (disk 1))
    (hbound : Bornology.IsBounded (func '' disk 1)) (hzero : func 0 = 0)
    (point : ℂ) (hpoint : point ∈ disk 1) (hnonzero : point ≠ 0)
    (hnonconstant : ∃ first ∈ disk 1, ∃ second ∈ disk 1, func first ≠ func second) :
    (‖func point‖ = 4*transfiniteDiameter (func '' disk 1)*Real.exp (-mu ‖point‖)) ↔
    (IsUnivalentOn func (disk 1) ∧ ∃ major : ℝ, ‖func point‖ < major ∧
      func '' disk 1 = {value | ‖value‖ + ‖value-func point‖ < major}) :=
  sorry

/-- betsakos_derivative. -/
theorem betsakos_derivative (func : ℂ → ℂ) (hhol : DifferentiableOn ℂ func (disk 1))
    (hbound : Bornology.IsBounded (func '' disk 1)) (hzero : func 0 = 0) :
    ‖deriv func 0‖ ≤ transfiniteDiameter (func '' disk 1) :=
  sorry

/-- diameter_closure. -/
theorem diameter_closure (domain : Set ℂ) (hbound : Bornology.IsBounded domain) (hinfinite : domain.Infinite)
    (count : ℕ) (hcount : 2 ≤ count) : nDiameter domain count = nDiameter (closure domain) count :=
  sorry

/-- diameter_decreasing. -/
theorem diameter_decreasing (domain : Set ℂ) (hbound : Bornology.IsBounded domain) (hinfinite : domain.Infinite) :
    AntitoneOn (nDiameter domain) (Set.Ici 2) ∧
    Tendsto (nDiameter domain) atTop (𝓝 (transfiniteDiameter domain)) :=
  sorry

/-- diameter_capacity. -/
theorem diameter_capacity (domain : Set ℂ) (hbound : Bornology.IsBounded domain) (hinfinite : domain.Infinite) :
    transfiniteDiameter domain = capacityTD (closure domain) :=
  sorry

/-- final_scalar_deduction. -/
theorem final_scalar_deduction (value height inner outer cap : ℝ) (hvalue : 0 < value) (hheight : 0 < height)
    (hinner : inner ∈ Ioo 0 1) (houter : outer ∈ Ioo 0 1) (horder : inner ≤ outer)
    (hmu : AntitoneOn mu (Ioo 0 1)) (hcap : cap ≤ 1/(height*value))
    (hbets : 1 ≤ 4*cap*Real.exp (-mu inner)) : value ≤ (4/height)*Real.exp (-mu outer) :=
  sorry

/-- polynomial_bound. -/
theorem polynomial_bound (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) : S poly ≤ yBound degree height :=
  sorry

/-- beta_y_change. -/
theorem beta_y_change (degree : ℕ) (hdegree : 2 ≤ degree) :
    yBound degree '' Ioo 0 1 = beta degree '' Ioi 0 :=
  sorry

/-- bound_set_well_defined. -/
theorem bound_set_well_defined (degree : ℕ) (hdegree : 2 ≤ degree) :
    (yBound degree '' Ioo 0 1).Nonempty ∧ BddBelow (yBound degree '' Ioo 0 1) :=
  sorry

/-- kd_le_best. -/
theorem kd_le_best (degree : ℕ) (hdegree : 2 ≤ degree) : Kd degree ≤ (bestBound degree : EReal) :=
  sorry

/-- cor_step1_mu. -/
theorem cor_step1_mu (degree : ℕ) (hdegree : 2 ≤ degree) (length : ℝ) (hlength : 0 < length) :
    Real.pi^2/(4*Real.log (4/complement (radius degree length))) < mu (radius degree length) :=
  sorry

/-- cor_step1_majorant. -/
theorem cor_step1_majorant (degree : ℕ) (hdegree : 8 ≤ degree) : beta degree (Lchoice degree) < majorant degree ∧
    Kd degree < (majorant degree : EReal) :=
  sorry

/-- exp_lower. -/
theorem exp_lower (value : ℝ) (hvalue : 0 ≤ value) : value-value^2/2 ≤ 1-Real.exp (-value) :=
  sorry

/-- general_L_majorant. -/
theorem general_L_majorant (degree : ℕ) (hdegree : 2 ≤ degree) (length : ℝ) (hlength : length ∈ Ioo 0 (degree : ℝ)) :
    0 < lambda degree length ∧
    Real.log (4/complement (radius degree length)) ≤ lambda degree length/2 ∧
    beta degree length ≤ 4*Real.exp (length-Real.pi^2/(2*lambda degree length)) :=
  sorry

/-- tail_log_correction. -/
theorem tail_log_correction (degree : ℕ) (hdegree : 21 ≤ degree) :
    1/(4*ell degree)-Real.log (1-1/ell degree) ≤ (7/4)/ell degree :=
  sorry

/-- tail_log_ratio_decreasing. -/
theorem tail_log_ratio_decreasing : StrictAntiOn (fun value : ℝ => Real.log (32*value)/value) (Ici 1) :=
  sorry

/-- tail_lambda_upper. -/
theorem tail_lambda_upper (degree : ℕ) (hdegree : 21 ≤ degree) : lambda degree (Lchoice degree) < (253/100)*ell degree :=
  sorry

/-- tail_constants. -/
theorem tail_constants (degree : ℕ) (hdegree : 21 ≤ degree) :
    (304/100 : ℝ) < ell degree ∧ Real.log (32*ell degree) ≤ (152/100)*ell degree ∧
    Lchoice degree/degree < 42/10000 ∧
    -Real.log (1-Lchoice degree/degree) < (2/1000)*ell degree ∧
    (195/100)/ell degree < Real.pi^2/(2*lambda degree (Lchoice degree)) :=
  sorry

/-- cor_step3. -/
theorem cor_step3 (degree : ℕ) (hdegree : 21 ≤ degree) : majorant degree ≤ target degree :=
  sorry

/-- cor_step2. -/
theorem cor_step2 (degree : ℕ) (hdegree : 8 ≤ degree) (hupper : degree ≤ 20) : majorant degree < target degree :=
  sorry

/-- best_strict_improvement. -/
theorem best_strict_improvement (degree : ℕ) (hdegree : 8 ≤ degree) : bestBound degree < majorant degree ∧ majorant degree ≤ target degree :=
  sorry

/-- prop_3_4_lower_error. -/
theorem prop_3_4_lower_error : ∃ constant ≥ (0 : ℝ), ∀ᶠ degree : ℕ in atTop,
    2*Real.pi^2-constant*(Real.log (ell degree)/ell degree) ≤ gap degree :=
  sorry

/-- prop_3_4_upper. -/
theorem prop_3_4_upper (degree : ℕ) (hdegree : 8 ≤ degree) :
    gap degree ≤ 2*Real.pi^2/(1-Real.pi^2/((degree : ℝ)*(ell degree)^2)) :=
  sorry

/-- prop_3_4_limit. -/
theorem prop_3_4_limit : Tendsto gap atTop (𝓝 (2*Real.pi^2)) :=
  sorry

/-- prop_denominator_positive. -/
theorem prop_denominator_positive (degree : ℕ) (hdegree : 8 ≤ degree) :
    Real.pi^2 < (degree : ℝ)*(ell degree)^2 ∧ 0 < 2*ell degree-2*Real.pi^2/(ell degree*degree) :=
  sorry

/-- prop_delta_bound. -/
theorem prop_delta_bound (degree : ℕ) (hdegree : 8 ≤ degree) (length : ℝ) (hlength : length ∈ Ioo 0 2) :
    0 < delta degree length ∧ delta degree length < 4*mu (complement (radius degree length)) ∧
    mu (radius degree length) < Real.pi^2/delta degree length :=
  sorry

/-- prop_case_a. -/
theorem prop_case_a (degree : ℕ) (hdegree : 8 ≤ degree) (length : ℝ) (hlength : 2 ≤ length) :
    4 < Real.exp ((1-1/(degree : ℝ))*length) ∧
    Real.exp ((1-1/(degree : ℝ))*length) < beta degree length :=
  sorry

/-- prop_case_b. -/
theorem prop_case_b (degree : ℕ) (hdegree : 8 ≤ degree) (length : ℝ)
    (hlower : Real.pi^2/(2*ell degree) ≤ length) (hupper : length < 2) : 4 < beta degree length :=
  sorry

/-- prop_case_c. -/
theorem prop_case_c (degree : ℕ) (hdegree : 8 ≤ degree) (length : ℝ)
    (hlength : length ∈ Ioo 0 (min 2 (Real.pi^2/(2*ell degree)))) : uniformLower degree < beta degree length :=
  sorry

/-- prop_uniform_lower. -/
theorem prop_uniform_lower (degree : ℕ) (hdegree : 8 ≤ degree) : uniformLower degree ≤ bestBound degree :=
  sorry

/-- prop_selected_L. -/
theorem prop_selected_L : ∃ constant ≥ (0 : ℝ), ∀ᶠ degree : ℕ in atTop,
    beta degree (Real.pi^2/(2*(ell degree)^2)) ≤
      4*Real.exp (-Real.pi^2/(2*ell degree)+constant*Real.log (ell degree)/(ell degree)^2) :=
  sorry

/-- weaker_asymptotic_difference. -/
theorem weaker_asymptotic_difference : Tendsto (fun degree : ℕ => (target degree-bestBound degree)*ell degree) atTop (𝓝 (2*Real.pi^2-4)) :=
  sorry

/-- weaker_k_gap_liminf. -/
theorem weaker_k_gap_liminf (epsilon : ℝ) (hepsilon : 0 < epsilon) : ∀ᶠ degree : ℕ in atTop,
    Kd degree ≤ ((4 - (2*Real.pi^2-epsilon)/ell degree : ℝ) : EReal) :=
  sorry

/-- earlier_crane_comparison. -/
theorem earlier_crane_comparison (degree : ℕ) (hdegree : 8 ≤ degree) : target degree < crane degree :=
  sorry

/-- sqrt_log_minimum. -/
theorem sqrt_log_minimum (value : ℝ) (hvalue : 1 < value) :
    Real.exp 1/2 ≤ Real.sqrt value/Real.log value ∧
    (Real.sqrt value/Real.log value = Real.exp 1/2 ↔ value = Real.exp 2) :=
  sorry

/-- earlier_fujikawa_comparison. -/
theorem earlier_fujikawa_comparison (degree : ℕ) (hdegree : 8 ≤ degree) : target degree < fujikawa degree :=
  sorry

/-- earlier_three_comparisons. -/
theorem earlier_three_comparisons (degree : ℕ) (hdegree : 8 ≤ degree) :
    fujikawa degree ≤ conte degree ∧ fujikawa degree < beardon degree ∧ fujikawa degree < dubinin degree :=
  sorry

/-- d_plus_one_log_increasing. -/
theorem d_plus_one_log_increasing : StrictMonoOn (fun value : ℝ => (value+1)/Real.log value) (Ici 4) :=
  sorry

/-- agm_bracketing. -/
theorem agm_bracketing (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) (index : ℕ) :
    (agmPair modulus index).2 ≤ (agmPair modulus (index+1)).2 ∧
    (agmPair modulus (index+1)).2 ≤ (agmPair modulus (index+1)).1 ∧
    (agmPair modulus (index+1)).1 ≤ (agmPair modulus index).1 ∧
    (agmPair modulus (index+1)).1-(agmPair modulus (index+1)).2 ≤
      ((agmPair modulus index).1-(agmPair modulus index).2)/2 ∧
    (agmPair modulus index).2 ≤ agm modulus ∧ agm modulus ≤ (agmPair modulus index).1 :=
  sorry

/-- agm_convergence. -/
theorem agm_convergence (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) :
    Tendsto (fun index => (agmPair modulus index).1) atTop (𝓝 (agm modulus)) ∧
    Tendsto (fun index => (agmPair modulus index).2) atTop (𝓝 (agm modulus)) :=
  sorry

/-- agm_elliptic_identity. -/
theorem agm_elliptic_identity (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) :
    ellipticK modulus = Real.pi/(2*agm (complement modulus)) ∧
    mu modulus = Real.pi*agm (complement modulus)/(2*agm modulus) :=
  sorry

/-- dlmf_19_8_5. -/
theorem dlmf_19_8_5 (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) :
    ellipticK modulus = Real.pi/(2*agm (complement modulus)) :=
  sorry

/-- range_7_enclosure. -/
theorem range_7_enclosure : (20190/10000 : ℝ) < bestBound 7 ∧ bestBound 7 < 20191/10000 ∧ target 7 < 19445/10000 :=
  sorry

/-- range_8_enclosure. -/
theorem range_8_enclosure : (20549/10000 : ℝ) < bestBound 8 ∧ bestBound 8 < 20550/10000 ∧ gap 8 < 4045/1000 :=
  sorry

/-- range_selected_values. -/
theorem range_selected_values : beta 8 (12766/100000) < (20550/10000 : ℝ) ∧ beta 7 (13621/100000) < 20191/10000 :=
  sorry

/-- range_tail. -/
theorem range_tail (degree : ℕ) (hdegree : degree = 7 ∨ degree = 8) (length : ℝ) (hlength : 1 ≤ length) :
    (235/100 : ℝ) < Real.exp (6/7) ∧ Real.exp (6/7) < beta degree length :=
  sorry

/-- range_interval_lower. -/
theorem range_interval_lower (degree : ℕ) (hdegree : 2 ≤ degree) (lower upper length : ℝ)
    (hlower : 0 ≤ lower) (horder : lower < length) (hupper : length ≤ upper) :
    4*Real.exp lower*Real.exp (-mu (radius degree upper)) ≤ beta degree length :=
  sorry

/-- figure3_height. -/
theorem figure3_height (degree : ℕ) (hdegree : 8 ≤ degree) :
    Kd degree ≤ ((4-gap degree/ell degree : ℝ) : EReal) ∧ 4 < gap degree :=
  sorry

/-- Table 3 M, degree 8. -/
theorem table3_M_8 : majorant 8 ≤ (205907/100000 : ℝ) :=
  sorry

/-- Table 3 target, degree 8. -/
theorem table3_target_8 : (207640/100000 : ℝ) ≤ target 8 :=
  sorry

/-- Table 3 margin, degree 8. -/
theorem table3_margin_8 : (1733/100000 : ℝ) ≤ target 8-majorant 8 :=
  sorry

/-- Table 3 M, degree 9. -/
theorem table3_M_9 : majorant 9 ≤ (208862/100000 : ℝ) :=
  sorry

/-- Table 3 target, degree 9. -/
theorem table3_target_9 : (217952/100000 : ℝ) ≤ target 9 :=
  sorry

/-- Table 3 margin, degree 9. -/
theorem table3_margin_9 : (9090/100000 : ℝ) ≤ target 9-majorant 9 :=
  sorry

/-- Table 3 M, degree 10. -/
theorem table3_M_10 : majorant 10 ≤ (211417/100000 : ℝ) :=
  sorry

/-- Table 3 target, degree 10. -/
theorem table3_target_10 : (226282/100000 : ℝ) ≤ target 10 :=
  sorry

/-- Table 3 margin, degree 10. -/
theorem table3_margin_10 : (14865/100000 : ℝ) ≤ target 10-majorant 10 :=
  sorry

/-- Table 3 M, degree 11. -/
theorem table3_M_11 : majorant 11 ≤ (213661/100000 : ℝ) :=
  sorry

/-- Table 3 target, degree 11. -/
theorem table3_target_11 : (233187/100000 : ℝ) ≤ target 11 :=
  sorry

/-- Table 3 margin, degree 11. -/
theorem table3_margin_11 : (19526/100000 : ℝ) ≤ target 11-majorant 11 :=
  sorry

/-- Table 3 M, degree 12. -/
theorem table3_M_12 : majorant 12 ≤ (215656/100000 : ℝ) :=
  sorry

/-- Table 3 target, degree 12. -/
theorem table3_target_12 : (239028/100000 : ℝ) ≤ target 12 :=
  sorry

/-- Table 3 margin, degree 12. -/
theorem table3_margin_12 : (23372/100000 : ℝ) ≤ target 12-majorant 12 :=
  sorry

/-- Table 3 M, degree 13. -/
theorem table3_M_13 : majorant 13 ≤ (217447/100000 : ℝ) :=
  sorry

/-- Table 3 target, degree 13. -/
theorem table3_target_13 : (244051/100000 : ℝ) ≤ target 13 :=
  sorry

/-- Table 3 margin, degree 13. -/
theorem table3_margin_13 : (26604/100000 : ℝ) ≤ target 13-majorant 13 :=
  sorry

/-- Table 3 M, degree 14. -/
theorem table3_M_14 : majorant 14 ≤ (219069/100000 : ℝ) :=
  sorry

/-- Table 3 target, degree 14. -/
theorem table3_target_14 : (248430/100000 : ℝ) ≤ target 14 :=
  sorry

/-- Table 3 margin, degree 14. -/
theorem table3_margin_14 : (29361/100000 : ℝ) ≤ target 14-majorant 14 :=
  sorry

/-- Table 3 M, degree 15. -/
theorem table3_M_15 : majorant 15 ≤ (220549/100000 : ℝ) :=
  sorry

/-- Table 3 target, degree 15. -/
theorem table3_target_15 : (252292/100000 : ℝ) ≤ target 15 :=
  sorry

/-- Table 3 margin, degree 15. -/
theorem table3_margin_15 : (31743/100000 : ℝ) ≤ target 15-majorant 15 :=
  sorry

/-- Table 3 M, degree 16. -/
theorem table3_M_16 : majorant 16 ≤ (221907/100000 : ℝ) :=
  sorry

/-- Table 3 target, degree 16. -/
theorem table3_target_16 : (255730/100000 : ℝ) ≤ target 16 :=
  sorry

/-- Table 3 margin, degree 16. -/
theorem table3_margin_16 : (33823/100000 : ℝ) ≤ target 16-majorant 16 :=
  sorry

/-- Table 3 M, degree 17. -/
theorem table3_M_17 : majorant 17 ≤ (223162/100000 : ℝ) :=
  sorry

/-- Table 3 target, degree 17. -/
theorem table3_target_17 : (258817/100000 : ℝ) ≤ target 17 :=
  sorry

/-- Table 3 margin, degree 17. -/
theorem table3_margin_17 : (35655/100000 : ℝ) ≤ target 17-majorant 17 :=
  sorry

/-- Table 3 M, degree 18. -/
theorem table3_M_18 : majorant 18 ≤ (224326/100000 : ℝ) :=
  sorry

/-- Table 3 target, degree 18. -/
theorem table3_target_18 : (261609/100000 : ℝ) ≤ target 18 :=
  sorry

/-- Table 3 margin, degree 18. -/
theorem table3_margin_18 : (37283/100000 : ℝ) ≤ target 18-majorant 18 :=
  sorry

/-- Table 3 M, degree 19. -/
theorem table3_M_19 : majorant 19 ≤ (225410/100000 : ℝ) :=
  sorry

/-- Table 3 target, degree 19. -/
theorem table3_target_19 : (264150/100000 : ℝ) ≤ target 19 :=
  sorry

/-- Table 3 margin, degree 19. -/
theorem table3_margin_19 : (38740/100000 : ℝ) ≤ target 19-majorant 19 :=
  sorry

/-- Table 3 M, degree 20. -/
theorem table3_M_20 : majorant 20 ≤ (226424/100000 : ℝ) :=
  sorry

/-- Table 3 target, degree 20. -/
theorem table3_target_20 : (266476/100000 : ℝ) ≤ target 20 :=
  sorry

/-- Table 3 margin, degree 20. -/
theorem table3_margin_20 : (40052/100000 : ℝ) ≤ target 20-majorant 20 :=
  sorry

/-- tail_star. -/
theorem tail_star (degree : ℕ) (hdegree : 21 ≤ degree) : 1/(4*ell degree)-Real.log (1-1/ell degree) ≤ Real.pi^2/(2*lambda degree (Lchoice degree)) :=
  sorry

/-- bounds_below_39. -/
theorem bounds_below_39 (degree : ℕ) (hdegree : 8 ≤ degree) (hupper : (degree : ℝ) ≤ Real.exp 40) : Kd degree < ((39/10 : ℝ) : EReal) :=
  sorry

/-- small_bound_below_39. -/
theorem small_bound_below_39 (degree : ℕ) (hdegree : 2 ≤ degree) (hupper : degree ≤ 7) : Kd degree ≤ ((Real.rpow 4 (5/6) : ℝ) : EReal) ∧ (4 : ℝ)^(5/6 : ℝ) < 39/10 :=
  sorry

/-- range_7_best_improvement. -/
theorem range_7_best_improvement : target 7 < bestBound 7 ∧ Kd 7 ≤ (bestBound 7 : EReal) ∧ fujikawa 7 ≤ conte 7 ∧ fujikawa 7 ≤ beardon 7 ∧ fujikawa 7 ≤ dubinin 7 ∧ (24842/10000 : ℝ) < fujikawa 7 ∧ fujikawa 7 < 24843/10000 :=
  sorry

/-- figure3_gap8. -/
theorem figure3_gap8 : (4 : ℝ) < gap 8 ∧ gap 8 < 405/100 :=
  sorry

/-- general_exp_upper. -/
theorem general_exp_upper (value : ℝ) (hvalue : 0 ≤ value) : 1-Real.exp (-value) ≤ value :=
  sorry

/-- log_one_sub. -/
theorem log_one_sub (value : ℝ) (hvalue : value ∈ Ioo 0 1) : -Real.log (1-value) ≤ value/(1-value) :=
  sorry

/-- log_one_sub_half. -/
theorem log_one_sub_half (value : ℝ) (hvalue : value ∈ Icc 0 (1/2 : ℝ)) : -Real.log (1-value) ≤ 2*value :=
  sorry

/-- diameter_closure_limit. -/
theorem diameter_closure_limit (domain : Set ℂ) (hbound : Bornology.IsBounded domain) (hinfinite : domain.Infinite) : transfiniteDiameter domain = transfiniteDiameter (closure domain) :=
  sorry

/-- betsakos_small_argument. -/
theorem betsakos_small_argument (diameter : ℝ) : ∃ constant ≥ (0 : ℝ), ∀ᶠ modulus in 𝓝[>] (0 : ℝ), |4*diameter*Real.exp (-mu modulus)-diameter*modulus| ≤ constant*|modulus|^3 :=
  sorry

/-- betsakos_large_argument. -/
theorem betsakos_large_argument (diameter : ℝ) : Tendsto (fun modulus : ℝ => 4*diameter*Real.exp (-mu modulus)) (𝓝[<] 1) (𝓝 (4*diameter)) :=
  sorry

/-- zero_betsakos_interpretation. -/
theorem zero_betsakos_interpretation (diameter : ℝ) : Tendsto (fun modulus : ℝ => 4*diameter*Real.exp (-mu modulus)) (𝓝[>] 0) (𝓝 0) :=
  sorry

/-- capacity_phi_expansion. -/
theorem capacity_phi_expansion (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0) (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (hcritical : critical ≠ 0) : ∃ constant : ℂ, Tendsto (fun point : ℂ => inversion critical (inverse ((height : ℂ)/point)) - (-critical/((height : ℂ)*deriv inverse 0))*point) (cocompact ℂ) (𝓝 constant) :=
  sorry

/-- exterior_conformal_map. -/
theorem exterior_conformal_map (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0) (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (hcritical : critical ≠ 0) : IsConformalOnto (fun point : ℂ => inversion critical (inverse ((height : ℂ)/point))) {point : ℂ | 1 < ‖point‖} (closure (exteriorImage inverse height critical))ᶜ :=
  sorry

/-- xi_polynomial_holomorphic_extension. -/
theorem xi_polynomial_holomorphic_extension (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly) (critical : ℂ) (hnormal : NormalizedCriticalValues poly critical) (inverse : ℂ → ℂ) (hinverse : IsInverseBranch poly inverse) (height : ℝ) (hheight : height ∈ Ioo 0 1) (func : ℂ → ℂ) (hfunc : IsConformalOnto func (disk 1) (exteriorImage inverse height critical)) (hzero : func 0 = 0) : ∃ extension : ℂ → ℂ, DifferentiableOn ℂ extension (disk 1) ∧ (∀ point ∈ disk 1, point ≠ 0 → extension point = point^degree*poly.eval (inversion critical (func point))) ∧ ∀ point ∈ disk 1, ‖extension point‖ ≤ height :=
  sorry

/-- figure2_example. -/
theorem figure2_example : IsPd 2 ((2 : ℂ[X])*Polynomial.X-Polynomial.X^2) ∧ NormalizedCriticalValues ((2 : ℂ[X])*Polynomial.X-Polynomial.X^2) 1 :=
  sorry

/-- table2_8. -/
theorem table2_8 : target 8 ≤ (20765/10000 : ℝ) ∧ beta 8 (12766/100000) ≤ (20550/10000 : ℝ) ∧ bestBound 8 ≤ (20550/10000 : ℝ) :=
  sorry

/-- figure3_dot_8. -/
theorem figure3_dot_8 : ((4-(20550/10000 : ℝ))*ell 8) ≤ gap 8 :=
  sorry

/-- table2_100. -/
theorem table2_100 : target 100 ≤ (31315/10000 : ℝ) ∧ beta 100 (5337/100000) ≤ (25255/10000 : ℝ) ∧ bestBound 100 ≤ (25255/10000 : ℝ) :=
  sorry

/-- figure3_dot_100. -/
theorem figure3_dot_100 : ((4-(25255/10000 : ℝ))*ell 100) ≤ gap 100 :=
  sorry

/-- table2_10000. -/
theorem table2_10000 : target 10000 ≤ (35658/10000 : ℝ) ∧ beta 10000 (2156/100000) ≤ (29495/10000 : ℝ) ∧ bestBound 10000 ≤ (29495/10000 : ℝ) :=
  sorry

/-- figure3_dot_10000. -/
theorem figure3_dot_10000 : ((4-(29495/10000 : ℝ))*ell 10000) ≤ gap 10000 :=
  sorry

/-- table2_1000000. -/
theorem table2_1000000 : target 1000000 ≤ (37105/10000 : ℝ) ∧ beta 1000000 (1194/100000) ≤ (31754/10000 : ℝ) ∧ bestBound 1000000 ≤ (31754/10000 : ℝ) :=
  sorry

/-- figure3_dot_1000000. -/
theorem figure3_dot_1000000 : ((4-(31754/10000 : ℝ))*ell 1000000) ≤ gap 1000000 :=
  sorry

/-- crane_numeric_8. -/
theorem crane_numeric_8 : Kd 8 < ((3124/1000 : ℝ) : EReal) ∧ (389/1000 : ℝ) < 3124/1000-target 8 :=
  sorry

/-- crane_numeric_9. -/
theorem crane_numeric_9 : Kd 9 < ((3150/1000 : ℝ) : EReal) ∧ (389/1000 : ℝ) < 3150/1000-target 9 :=
  sorry

/-- crane_numeric_10. -/
theorem crane_numeric_10 : Kd 10 < ((3169/1000 : ℝ) : EReal) ∧ (389/1000 : ℝ) < 3169/1000-target 10 :=
  sorry

/-- crane_numeric_11. -/
theorem crane_numeric_11 : Kd 11 < ((3188/1000 : ℝ) : EReal) ∧ (389/1000 : ℝ) < 3188/1000-target 11 :=
  sorry

/-- crane_numeric_12. -/
theorem crane_numeric_12 : Kd 12 < ((3208/1000 : ℝ) : EReal) ∧ (389/1000 : ℝ) < 3208/1000-target 12 :=
  sorry

/-- crane_numeric_16. -/
theorem crane_numeric_16 : Kd 16 < ((3271/1000 : ℝ) : EReal) ∧ (389/1000 : ℝ) < 3271/1000-target 16 :=
  sorry

/-- crane_numeric_25. -/
theorem crane_numeric_25 : Kd 25 < ((3365/1000 : ℝ) : EReal) ∧ (389/1000 : ℝ) < 3365/1000-target 25 :=
  sorry

/-- crane_numeric_100. -/
theorem crane_numeric_100 : Kd 100 < ((3621/1000 : ℝ) : EReal) ∧ (389/1000 : ℝ) < 3621/1000-target 100 :=
  sorry

/-- crane_numeric_10000. -/
theorem crane_numeric_10000 : Kd 10000 < ((3955/1000 : ℝ) : EReal) ∧ (389/1000 : ℝ) < 3955/1000-target 10000 :=
  sorry

/-- inverse_analytic_boundary. -/
theorem inverse_analytic_boundary (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0) (height : ℝ) (hheight : height ∈ Ioo 0 1) : AnalyticOnNhd ℂ inverse (Metric.sphere 0 height) ∧ (∀ point ∈ Metric.sphere 0 height, deriv inverse point ≠ 0) ∧ frontier (inverseDomain inverse height) = inverse '' Metric.sphere 0 height :=
  sorry

/-- conformal_geometry_witness. -/
theorem conformal_geometry_witness  : IsBoundedJordanDomain (disk 1) ∧ IsConformalOnto (fun point : ℂ => point) (disk 1) (disk 1) :=
  sorry

/-- capacity_conformal_coefficient. -/
theorem capacity_conformal_coefficient (compactSet : Set ℂ) (hcompact : IsCompact compactSet) (hconnected : IsConnected compactSet) (hnontrivial : ∃ first ∈ compactSet, ∃ second ∈ compactSet, first ≠ second) (hcomplement : IsConnected compactSetᶜ) (phi : ℂ → ℂ) (hphi : IsConformalOnto phi {point : ℂ | 1 < ‖point‖} compactSetᶜ) (coefficient : ℂ) (hcoefficient : coefficient ≠ 0) (hexpansion : ∃ constant : ℂ, Tendsto (fun point : ℂ => phi point-coefficient*point) (cocompact ℂ) (𝓝 constant)) : capacityTD compactSet ≤ ‖coefficient‖ :=
  sorry

/-- table3_printed_minimum. -/
theorem table3_printed_minimum  : ∀ entry ∈ ([(8,1733),(9,9090),(10,14865),(11,19526),(12,23372),(13,26604),(14,29361),(15,31743),(16,33823),(17,35655),(18,37283),(19,38740),(20,40052)] : List (ℕ × ℕ)), (1733 : ℕ) ≤ entry.2 ∧ (entry.2 = 1733 ↔ entry.1 = 8) :=
  sorry

/-- crane_unique_minimum. -/
theorem crane_unique_minimum  : ∀ entry ∈ ([(8,3124),(9,3150),(10,3169),(11,3188),(12,3208),(16,3271),(25,3365),(100,3621),(10000,3955)] : List (ℕ × ℕ)), (3955/1000 : ℝ)-target 10000 ≤ (entry.2 : ℝ)/1000-target entry.1 ∧ (entry.1 ≠ 10000 → (3955/1000 : ℝ)-target 10000 < (entry.2 : ℝ)/1000-target entry.1) :=
  sorry

/-- figure1_six_dots_above. -/
theorem figure1_six_dots_above  : ∀ entry ∈ ([(8,3124),(9,3150),(10,3169),(11,3188),(12,3208),(16,3271)] : List (ℕ × ℕ)), min (fujikawa entry.1) (crane entry.1) < (entry.2 : ℝ)/1000 :=
  sorry

/-- figure1_three_dots_below. -/
theorem figure1_three_dots_below  : ∀ entry ∈ ([(25,3365),(100,3621),(10000,3955)] : List (ℕ × ℕ)), (entry.2 : ℝ)/1000 < min (fujikawa entry.1) (crane entry.1) :=
  sorry

/-- figure1_excluded_regions. -/
theorem figure1_excluded_regions (degree : ℕ) (hdegree : 8 ≤ degree) : Kd degree ≤ ((min (fujikawa degree) (crane degree) : ℝ) : EReal) ∧ bestBound degree < min (fujikawa degree) (crane degree) :=
  sorry

/-- first_four_order. -/
theorem first_four_order  : ∀ bound ∈ ([beardon, conte, fujikawa, dubinin] : List (ℕ → ℝ)), ∃ lower upper : ℝ, 0 < lower ∧ lower ≤ upper ∧ ∀ᶠ degree : ℕ in atTop, lower/(degree : ℝ) ≤ 4-bound degree ∧ 4-bound degree ≤ upper/degree :=
  sorry

/-- crane_gap_order. -/
theorem crane_gap_order (degree : ℕ) : 4-crane degree = (2263/1000)/Real.sqrt degree :=
  sorry

/-- small_multiple_asymptotic. -/
theorem small_multiple_asymptotic (multiple : ℝ) (hmultiple : multiple ∈ Ioo 0 (Real.pi^2/2)) : Tendsto (fun degree : ℕ => (4-4*Real.exp (multiple/ell degree-Real.pi^2/(2*lambda degree (multiple/ell degree))))*ell degree) atTop (𝓝 (2*Real.pi^2-4*multiple)) :=
  sorry

/-- quadratic_inverse_example. -/
theorem quadratic_inverse_example  : IsInverseBranch ((2 : ℂ[X])*Polynomial.X-Polynomial.X^2) (fun point : ℂ => 1-Complex.sqrt (1-point)) ∧ (1 : ℂ) ∉ (fun point : ℂ => 1-Complex.sqrt (1-point)) '' disk 1 ∧ (1 : ℂ) ∈ frontier ((fun point : ℂ => 1-Complex.sqrt (1-point)) '' disk 1) :=
  sorry

/-- table2_earlier_8. -/
theorem table2_earlier_8  : IsLeast ({fujikawa 8, conte 8, beardon 8, dubinin 8, crane 8, (3124/1000 : ℝ)} : Set ℝ) (fujikawa 8) ∧ (fujikawa 8) ≤ (26321/10000 : ℝ) :=
  sorry

/-- table2_earlier_100. -/
theorem table2_earlier_100  : IsLeast ({fujikawa 100, conte 100, beardon 100, dubinin 100, crane 100, (3621/1000 : ℝ)} : Set ℝ) ((3621/1000 : ℝ)) ∧ ((3621/1000 : ℝ)) ≤ (3621/1000 : ℝ) :=
  sorry

/-- table2_earlier_10000. -/
theorem table2_earlier_10000  : IsLeast ({fujikawa 10000, conte 10000, beardon 10000, dubinin 10000, crane 10000, (3955/1000 : ℝ)} : Set ℝ) ((3955/1000 : ℝ)) ∧ ((3955/1000 : ℝ)) ≤ (3955/1000 : ℝ) :=
  sorry

/-- table2_earlier_1000000. -/
theorem table2_earlier_1000000  : IsLeast ({fujikawa 1000000, conte 1000000, beardon 1000000, dubinin 1000000, crane 1000000} : Set ℝ) (crane 1000000) ∧ (crane 1000000) ≤ (39978/10000 : ℝ) :=
  sorry

/-- table3_M_rounding_8. -/
theorem table3_M_rounding_8  : (205906/100000 : ℝ) < majorant 8 ∧ majorant 8 ≤ (205907/100000 : ℝ) :=
  sorry

/-- table3_target_rounding_8. -/
theorem table3_target_rounding_8  : (207640/100000 : ℝ) ≤ target 8 ∧ target 8 < (207641/100000 : ℝ) :=
  sorry

/-- table3_M_rounding_9. -/
theorem table3_M_rounding_9  : (208861/100000 : ℝ) < majorant 9 ∧ majorant 9 ≤ (208862/100000 : ℝ) :=
  sorry

/-- table3_target_rounding_9. -/
theorem table3_target_rounding_9  : (217952/100000 : ℝ) ≤ target 9 ∧ target 9 < (217953/100000 : ℝ) :=
  sorry

/-- table3_M_rounding_10. -/
theorem table3_M_rounding_10  : (211416/100000 : ℝ) < majorant 10 ∧ majorant 10 ≤ (211417/100000 : ℝ) :=
  sorry

/-- table3_target_rounding_10. -/
theorem table3_target_rounding_10  : (226282/100000 : ℝ) ≤ target 10 ∧ target 10 < (226283/100000 : ℝ) :=
  sorry

/-- table3_M_rounding_11. -/
theorem table3_M_rounding_11  : (213660/100000 : ℝ) < majorant 11 ∧ majorant 11 ≤ (213661/100000 : ℝ) :=
  sorry

/-- table3_target_rounding_11. -/
theorem table3_target_rounding_11  : (233187/100000 : ℝ) ≤ target 11 ∧ target 11 < (233188/100000 : ℝ) :=
  sorry

/-- table3_M_rounding_12. -/
theorem table3_M_rounding_12  : (215655/100000 : ℝ) < majorant 12 ∧ majorant 12 ≤ (215656/100000 : ℝ) :=
  sorry

/-- table3_target_rounding_12. -/
theorem table3_target_rounding_12  : (239028/100000 : ℝ) ≤ target 12 ∧ target 12 < (239029/100000 : ℝ) :=
  sorry

/-- table3_M_rounding_13. -/
theorem table3_M_rounding_13  : (217446/100000 : ℝ) < majorant 13 ∧ majorant 13 ≤ (217447/100000 : ℝ) :=
  sorry

/-- table3_target_rounding_13. -/
theorem table3_target_rounding_13  : (244051/100000 : ℝ) ≤ target 13 ∧ target 13 < (244052/100000 : ℝ) :=
  sorry

/-- table3_M_rounding_14. -/
theorem table3_M_rounding_14  : (219068/100000 : ℝ) < majorant 14 ∧ majorant 14 ≤ (219069/100000 : ℝ) :=
  sorry

/-- table3_target_rounding_14. -/
theorem table3_target_rounding_14  : (248430/100000 : ℝ) ≤ target 14 ∧ target 14 < (248431/100000 : ℝ) :=
  sorry

/-- table3_M_rounding_15. -/
theorem table3_M_rounding_15  : (220548/100000 : ℝ) < majorant 15 ∧ majorant 15 ≤ (220549/100000 : ℝ) :=
  sorry

/-- table3_target_rounding_15. -/
theorem table3_target_rounding_15  : (252292/100000 : ℝ) ≤ target 15 ∧ target 15 < (252293/100000 : ℝ) :=
  sorry

/-- table3_M_rounding_16. -/
theorem table3_M_rounding_16  : (221906/100000 : ℝ) < majorant 16 ∧ majorant 16 ≤ (221907/100000 : ℝ) :=
  sorry

/-- table3_target_rounding_16. -/
theorem table3_target_rounding_16  : (255730/100000 : ℝ) ≤ target 16 ∧ target 16 < (255731/100000 : ℝ) :=
  sorry

/-- table3_M_rounding_17. -/
theorem table3_M_rounding_17  : (223161/100000 : ℝ) < majorant 17 ∧ majorant 17 ≤ (223162/100000 : ℝ) :=
  sorry

/-- table3_target_rounding_17. -/
theorem table3_target_rounding_17  : (258817/100000 : ℝ) ≤ target 17 ∧ target 17 < (258818/100000 : ℝ) :=
  sorry

/-- table3_M_rounding_18. -/
theorem table3_M_rounding_18  : (224325/100000 : ℝ) < majorant 18 ∧ majorant 18 ≤ (224326/100000 : ℝ) :=
  sorry

/-- table3_target_rounding_18. -/
theorem table3_target_rounding_18  : (261609/100000 : ℝ) ≤ target 18 ∧ target 18 < (261610/100000 : ℝ) :=
  sorry

/-- table3_M_rounding_19. -/
theorem table3_M_rounding_19  : (225409/100000 : ℝ) < majorant 19 ∧ majorant 19 ≤ (225410/100000 : ℝ) :=
  sorry

/-- table3_target_rounding_19. -/
theorem table3_target_rounding_19  : (264150/100000 : ℝ) ≤ target 19 ∧ target 19 < (264151/100000 : ℝ) :=
  sorry

/-- table3_M_rounding_20. -/
theorem table3_M_rounding_20  : (226423/100000 : ℝ) < majorant 20 ∧ majorant 20 ≤ (226424/100000 : ℝ) :=
  sorry

/-- table3_target_rounding_20. -/
theorem table3_target_rounding_20  : (266476/100000 : ℝ) ≤ target 20 ∧ target 20 < (266477/100000 : ℝ) :=
  sorry

/-- disk_green_instance. -/
theorem disk_green_instance  : IsClassicalGreen (disk 1) 0 diskGreen :=
  sorry

/-- finite_green_exists. -/
theorem finite_green_exists (domain : Set ℂ) (hdomain : IsBoundedJordanDomain domain) (pole : ℂ) (hpole : pole ∈ domain) : ∃ green : ℂ → ℝ, IsClassicalGreen domain pole green :=
  sorry

/-- finite_green_conformal_invariance. -/
theorem finite_green_conformal_invariance (domain image : Set ℂ) (hdomain : IsBoundedJordanDomain domain) (himage : IsBoundedJordanDomain image) (func : ℂ → ℂ) (hfunc : IsConformalOnto func domain image) (pole point : ℂ) (hpole : pole ∈ domain) (hpoint : point ∈ domain) (hdistinct : point ≠ pole) (greenDomain greenImage : ℂ → ℝ) (hgreenDomain : IsClassicalGreen domain pole greenDomain) (hgreenImage : IsClassicalGreen image (func pole) greenImage) : greenImage (func point) = greenDomain point :=
  sorry

/-- exterior_green_exists. -/
theorem exterior_green_exists (domain : Set ℂ) (hdomain : IsBoundedJordanDomain domain) : ∃ green : ℂ → ℝ, IsClassicalExteriorGreen (closure domain) green :=
  sorry

/-- inversion_green_identity. -/
theorem inversion_green_identity (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0) (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (hcritical : critical ≠ 0) (homit : critical ∉ inverse '' disk 1) (greenExterior greenImage : ℂ → ℝ) (hgreenExterior : IsClassicalExteriorGreen (closure (inverseDomain inverse height)) greenExterior) (hgreenImage : IsClassicalGreen (exteriorImage inverse height critical) 0 greenImage) : greenExterior critical = greenImage (-1) :=
  sorry

/-- bernstein_walsh. -/
theorem bernstein_walsh (domain : Set ℂ) (hdomain : IsBoundedJordanDomain domain) (poly : ℂ[X]) (green : ℂ → ℝ) (hgreen : IsClassicalExteriorGreen (closure domain) green) (point : ℂ) (hpoint : point ∉ closure domain) : ‖poly.eval point‖ ≤ sSup ((fun value : ℂ => ‖poly.eval value‖) '' closure domain)*Real.exp ((poly.natDegree : ℝ)*green point) :=
  sorry

/-- dubinin_polynomial_specialization. -/
theorem dubinin_polynomial_specialization (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly) (domain : Set ℂ) (hdomain : IsBoundedJordanDomain domain) (height : ℝ) (hheight : height ∈ Ioo 0 1) (hboundary : ∀ point ∈ frontier domain, ‖poly.eval point‖ = height) (green : ℂ → ℝ) (hgreen : IsClassicalExteriorGreen (closure domain) green) (critical : ℂ) (hcritical : critical ∉ closure domain) (hvalue : ‖poly.eval critical‖ = 1) : Real.log (1/height) ≤ (degree : ℝ)*green critical :=
  sorry

/-- jatar_ng_boundary_critical_exists. -/
theorem jatar_ng_boundary_critical_exists (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsSchlichtNormalized degree poly) : ∃ point ∈ frontier (lemniscateComponent poly 1), point ∈ criticalPoints poly :=
  sorry

/-- jatar_ng_leading_coefficient. -/
theorem jatar_ng_leading_coefficient (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsSchlichtNormalized degree poly) : 0 < ‖poly.leadingCoeff‖ ∧ ‖poly.leadingCoeff‖ < 1 :=
  sorry

/-- jatar_ng_source_v. -/
theorem jatar_ng_source_v (degree : ℕ) (hdegree : 169 ≤ degree) (poly : ℂ[X]) (hpoly : IsSchlichtNormalized degree poly) (hlog : (Real.log (1/‖poly.leadingCoeff‖))^2 ≤ (degree : ℝ)) (point : ℂ) (hpoint : point ∈ criticalPoints poly) (hboundary : point ∈ frontier (lemniscateComponent poly 1)) : criticalRatio poly point ≤ jatarNgBound degree :=
  sorry

/-- jatar_ng_printed_bound. -/
theorem jatar_ng_printed_bound (degree : ℕ) (hdegree : 169 ≤ degree) (poly : ℂ[X]) (hpoly : IsSchlichtNormalized degree poly) (hleading : Real.exp (-Real.sqrt degree) ≤ ‖poly.leadingCoeff‖) : S poly ≤ jatarNgBound degree :=
  sorry

/-- jatar_ng_bound_limit. -/
theorem jatar_ng_bound_limit  : Tendsto jatarNgBound atTop (𝓝 1) :=
  sorry

/-- finite_box_soundness. -/
theorem finite_box_soundness (degree : ℕ) (hdegree : degree = 7 ∨ degree = 8) (boxes : List CertifiedBoxData) (hnonempty : boxes ≠ []) (hvalid : ∀ box ∈ boxes, ValidBox box) (hcover : CoversUnit boxes) (hendpoint : ∀ box ∈ boxes, BoxEndpointBound degree box) (cutoff : ℝ) (hcutoff : ∀ box ∈ boxes, cutoff < (box.lower : ℝ)) (htail : cutoff < Real.exp (6/7)) : cutoff < bestBound degree :=
  sorry

/-- range7_finite_certificate. -/
theorem range7_finite_certificate  : ∃ boxes : List CertifiedBoxData, CoversUnit boxes ∧ ∀ box ∈ boxes, ValidBox box ∧ BoxEndpointBound 7 box ∧ (20190/10000 : ℝ) < (box.lower : ℝ) :=
  sorry

/-- range8_finite_certificate. -/
theorem range8_finite_certificate  : ∃ boxes : List CertifiedBoxData, CoversUnit boxes ∧ ∀ box ∈ boxes, ValidBox box ∧ BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ) :=
  sorry

/-- s_pos_of_critical_values_ne_zero. -/
theorem s_pos_of_critical_values_ne_zero (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly) (hvalues : ∀ point ∈ criticalPoints poly, poly.eval point ≠ 0) : 0 < S poly :=
  sorry

/-- ybound_gt_rpow. -/
theorem ybound_gt_rpow (degree : ℕ) (hdegree : 2 ≤ degree) (height : ℝ) (hheight : height ∈ Ioo 0 1) : height^((1/(degree : ℝ))-1) < yBound degree height :=
  sorry

/-- koebe_quarter_omission. -/
theorem koebe_quarter_omission (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0) (point : ℂ) (homit : point ∉ inverse '' disk 1) : ‖deriv inverse 0‖/4 ≤ ‖point‖ :=
  sorry

/-- lambda_chosen_identity. -/
theorem lambda_chosen_identity (degree : ℕ) (hdegree : 8 ≤ degree) : lambda degree (Lchoice degree) = ell degree+Real.log (32*ell degree)-Real.log (1-Lchoice degree/degree) :=
  sorry

/-- tail_numerical_endpoints. -/
theorem tail_numerical_endpoints  : Real.log (32*Real.log 21)/Real.log 21 < (152/100 : ℝ) ∧ -Real.log (1-(42/10000 : ℝ)) < 5/1000 :=
  sorry

/-- fujikawa_identity. -/
theorem fujikawa_identity (degree : ℕ) (hdegree : 2 ≤ degree) : fujikawa degree = 4-4*(((degree : ℝ)-2)*(1-(4 : ℝ)^(-1/((degree : ℝ)-1)))+2)/((degree : ℝ)+1) :=
  sorry

/-- earlier_q_log_bound. -/
theorem earlier_q_log_bound (degree : ℕ) (hdegree : 2 ≤ degree) : 1-(4 : ℝ)^(-1/((degree : ℝ)-1)) ≤ Real.log 4/((degree : ℝ)-1) :=
  sorry

/-- earlier_bracket_bound. -/
theorem earlier_bracket_bound (degree : ℕ) (hdegree : 8 ≤ degree) : ((degree : ℝ)-2)*(1-(4 : ℝ)^(-1/((degree : ℝ)-1)))+2 < Real.log 4+2 ∧ Real.log 4+2 < 339/100 :=
  sorry

/-- earlier_endpoint_8. -/
theorem earlier_endpoint_8  : (432/100 : ℝ) < 9/Real.log 8 :=
  sorry

/-- earlier_difference_formulas. -/
theorem earlier_difference_formulas (degree : ℕ) (hdegree : 8 ≤ degree) : let quotient : ℝ := (4 : ℝ)^(-1/((degree : ℝ)-1)); conte degree-fujikawa degree = 4*((degree : ℝ)-2)*(1-quotient)/((degree : ℝ)+1) ∧ beardon degree-fujikawa degree = 4*(3*quotient-1)/((degree : ℝ)+1) ∧ dubinin degree-fujikawa degree = 4*((2*(degree : ℝ)-1)*quotient-degree)/((degree : ℝ)*((degree : ℝ)+1)) :=
  sorry

/-- earlier_q_half. -/
theorem earlier_q_half (degree : ℕ) (hdegree : 3 ≤ degree) : (1/2 : ℝ) ≤ (4 : ℝ)^(-1/((degree : ℝ)-1)) :=
  sorry

/-- earlier_q_eight. -/
theorem earlier_q_eight (degree : ℕ) (hdegree : 8 ≤ degree) : (4 : ℝ)^(-1/7 : ℝ) ≤ (4 : ℝ)^(-1/((degree : ℝ)-1)) ∧ (4/5 : ℝ) < (4 : ℝ)^(-1/7 : ℝ) ∧ (degree : ℝ)/(2*(degree : ℝ)-1) < (4/5 : ℝ) :=
  sorry

/-- prop_mu_complement_lower. -/
theorem prop_mu_complement_lower (degree : ℕ) (hdegree : 8 ≤ degree) (length : ℝ) (hlength : length ∈ Ioo 0 2) : Real.log (4/complement (radius degree length))-length/degree < mu (complement (radius degree length)) :=
  sorry

/-- prop_log_complement_lower. -/
theorem prop_log_complement_lower (degree : ℕ) (hdegree : 8 ≤ degree) (length : ℝ) (hlength : length ∈ Ioo 0 2) : (1/2)*Real.log (8*degree/length) ≤ Real.log (4/complement (radius degree length)) :=
  sorry

/-- prop_delta_elementary_lower. -/
theorem prop_delta_elementary_lower (degree : ℕ) (hdegree : 8 ≤ degree) (length : ℝ) (hlength : length ∈ Ioo 0 2) : 2*Real.log (4*degree)-8/degree < delta degree length :=
  sorry

/-- jn_radius_well_defined. -/
theorem jn_radius_well_defined (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X]) (hpoly : IsPd degree poly) :
    (univalentRadii poly).Nonempty ∧ BddAbove (univalentRadii poly) ∧
    0 < maxUnivalentRadius poly ∧ maxUnivalentRadius poly ∈ univalentRadii poly :=
  sorry

/-- jn_normalization_witness. -/
theorem jn_normalization_witness :
    IsSchlichtNormalized 2 (Polynomial.X - Polynomial.C (1/4 : ℂ)*Polynomial.X^2) :=
  sorry

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
    ∃ func : ℂ → ℂ, IsConformalOnto func (disk 1) domain ∧ func 0 = 0 :=
  sorry

/-- conditional coefficient upper bound; the unconditional row stays open. -/
theorem capacity_conformal_coefficient_given_background (hcoefficientFact : Background.CoefficientUpperFact)
    (compactSet : Set ℂ) (hcompact : IsCompact compactSet) (hconnected : IsConnected compactSet)
    (hnontrivial : ∃ first ∈ compactSet, ∃ second ∈ compactSet, first ≠ second)
    (hcomplement : IsConnected compactSetᶜ) (phi : ℂ → ℂ)
    (hphi : IsConformalOnto phi {point : ℂ | 1 < ‖point‖} compactSetᶜ)
    (coefficient : ℂ) (hcoefficient : coefficient ≠ 0)
    (hexpansion : ∃ constant : ℂ, Tendsto (fun point : ℂ => phi point - coefficient * point)
      (cocompact ℂ) (𝓝 constant)) : capacityTD compactSet ≤ ‖coefficient‖ :=
  sorry


/-- conditional exterior_image_geometry; the original is now independently proved without this premise. -/
theorem exterior_image_geometry_given_jordan (hjordan : Background.JordanCurveFact)
    (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (hcritical : critical ≠ 0)
    (homit : critical ∉ inverse '' disk 1) :
    IsBoundedJordanDomain (exteriorImage inverse height critical) ∧
      (0 : ℂ) ∈ exteriorImage inverse height critical ∧ (-1 : ℂ) ∈ exteriorImage inverse height critical :=
  sorry


/-- conditional polynomial bound with both named facts explicit. -/
theorem polynomial_bound_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 2 ≤ degree)
    (poly : ℂ[X]) (hpoly : IsPd degree poly) (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    S poly ≤ yBound degree height :=
  sorry

/-- conditional Theorem1.1; original unconditional row stays open. -/
theorem thm_1_1_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 2 ≤ degree)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) : Kd degree ≤ (yBound degree height : EReal) :=
  sorry

/-- conditional Corollary1.2; original unconditional row stays open. -/
theorem cor_1_2_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 8 ≤ degree) :
    Kd degree < (target degree : EReal) :=
  sorry

/-- conditional small-degree bound; explicit named facts retained. -/
theorem small_bound_below_39_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 2 ≤ degree) (hupper : degree ≤ 7) :
    Kd degree ≤ ((Real.rpow 4 (5/6) : ℝ) : EReal) ∧ (4 : ℝ)^(5/6 : ℝ) < 39/10 :=
  sorry

/-- conditional intermediate degree bound; original remains open. -/
theorem bounds_below_39_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 8 ≤ degree)
    (hupper : (degree : ℝ) ≤ Real.exp 40) : Kd degree < ((39/10 : ℝ) : EReal) :=
  sorry

/-- conditional 3.9 degree example; original remains open. -/
theorem degree_example_39_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 2 ≤ degree)
    (poly : ℂ[X]) (hpoly : IsPd degree poly) (hlarge : 39/10 ≤ S poly) : 2 * 10^17 < degree :=
  sorry

/-- conditional strict all-degree bound; original remains open. -/
theorem kd_lt_four_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 2 ≤ degree) : Kd degree < (4 : EReal) :=
  sorry

/-- conditional weak all-degree bound; original remains open. -/
theorem smale_bound_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 2 ≤ degree) : Kd degree ≤ (4 : EReal) :=
  sorry

/-- conditional supremum finiteness; original unconditional row remains open. -/
theorem kd_finite_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 2 ≤ degree) :
    Kd degree ≠ ⊥ ∧ Kd degree ≠ ⊤ :=
  sorry

/-- conditional optimized bound; original unconditional row remains open. -/
theorem kd_le_best_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 2 ≤ degree) :
    Kd degree ≤ (bestBound degree : EReal) :=
  sorry

/-- conditional K-gap consequence; original unconditional row remains open. -/
theorem weaker_k_gap_liminf_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ degree : ℕ in atTop, Kd degree ≤ ((4 - (2*Real.pi^2-epsilon)/ell degree : ℝ) : EReal) :=
  sorry

/-- conditional Crane comparison for Kd; original remains open. -/
theorem crane_bound_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 8 ≤ degree) :
    Kd degree < (crane degree : EReal) :=
  sorry

/-- conditional Step1 majorant; original remains open. -/
theorem cor_step1_majorant_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 8 ≤ degree) :
    beta degree (Lchoice degree) < majorant degree ∧ Kd degree < (majorant degree : EReal) :=
  sorry

/-- conditional excluded-region bound; original remains open. -/
theorem figure1_excluded_regions_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 8 ≤ degree) :
    Kd degree ≤ ((min (fujikawa degree) (crane degree) : ℝ) : EReal) ∧
      bestBound degree < min (fujikawa degree) (crane degree) :=
  sorry


/-- scalar margins for the nine printed Crane numbers; no Kd hypothesis. -/
theorem crane_numeric_margins : ∀ entry ∈
    ([(8,3124),(9,3150),(10,3169),(11,3188),(12,3208),(16,3271),(25,3365),(100,3621),(10000,3955)] : List (ℕ × ℕ)),
    (389/1000 : ℝ) < (entry.2 : ℝ)/1000-target entry.1 ∧
      (entry.1 ≠ 10000 → (2/5 : ℝ) < (entry.2 : ℝ)/1000-target entry.1) :=
  sorry

/-- conditional nine-number Crane comparison; original unconditional rows remain open. -/
theorem crane_numbers_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    ∀ entry ∈ ([(8,3124),(9,3150),(10,3169),(11,3188),(12,3208),(16,3271),(25,3365),(100,3621),(10000,3955)] : List (ℕ × ℕ)),
    Kd entry.1 < (((entry.2 : ℝ)/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < (entry.2 : ℝ)/1000-target entry.1 :=
  sorry

/-- conditional Crane number at degree 8; original unconditional row remains open. -/
theorem crane_numeric_8_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    Kd 8 < ((3124/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < 3124/1000-target 8 :=
  sorry

/-- conditional Crane number at degree 9; original unconditional row remains open. -/
theorem crane_numeric_9_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    Kd 9 < ((3150/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < 3150/1000-target 9 :=
  sorry

/-- conditional Crane number at degree 10; original unconditional row remains open. -/
theorem crane_numeric_10_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    Kd 10 < ((3169/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < 3169/1000-target 10 :=
  sorry

/-- conditional Crane number at degree 11; original unconditional row remains open. -/
theorem crane_numeric_11_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    Kd 11 < ((3188/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < 3188/1000-target 11 :=
  sorry

/-- conditional Crane number at degree 12; original unconditional row remains open. -/
theorem crane_numeric_12_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    Kd 12 < ((3208/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < 3208/1000-target 12 :=
  sorry

/-- conditional Crane number at degree 16; original unconditional row remains open. -/
theorem crane_numeric_16_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    Kd 16 < ((3271/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < 3271/1000-target 16 :=
  sorry

/-- conditional Crane number at degree 25; original unconditional row remains open. -/
theorem crane_numeric_25_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    Kd 25 < ((3365/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < 3365/1000-target 25 :=
  sorry

/-- conditional Crane number at degree 100; original unconditional row remains open. -/
theorem crane_numeric_100_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    Kd 100 < ((3621/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < 3621/1000-target 100 :=
  sorry

/-- conditional Crane number at degree 10000; original unconditional row remains open. -/
theorem crane_numeric_10000_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    Kd 10000 < ((3955/1000 : ℝ) : EReal) ∧
      (389/1000 : ℝ) < 3955/1000-target 10000 :=
  sorry

/-- scalar Figure3 height lower bound; no Kd hypothesis. -/
theorem gap_gt_four (degree : ℕ) (hdegree : 8 ≤ degree) : 4 < gap degree :=
  sorry

/-- conditional Figure3 height; original unconditional row remains open. -/
theorem figure3_height_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) (degree : ℕ) (hdegree : 8 ≤ degree) :
    Kd degree ≤ ((4-gap degree/ell degree : ℝ) : EReal) ∧ 4 < gap degree :=
  sorry

/-- degree-seven target comparison; independent of the bestBound enclosure. -/
theorem degree_seven_target_upper : target 7 < (19445/10000 : ℝ) :=
  sorry

/-- degree-seven older-bound minimum and printed decimal enclosure. -/
theorem fujikawa_seven_scalar :
    fujikawa 7 ≤ conte 7 ∧ fujikawa 7 ≤ beardon 7 ∧ fujikawa 7 ≤ dubinin 7 ∧
      (24842/10000 : ℝ) < fujikawa 7 ∧ fujikawa 7 < 24843/10000 :=
  sorry

/-- elementary target entries in Table2, independent of the elliptic beta columns. -/
theorem table2_target_columns : target 8 ≤ (20765/10000 : ℝ) ∧
    target 100 ≤ (31315/10000 : ℝ) ∧ target 10000 ≤ (35658/10000 : ℝ) ∧
    target 1000000 ≤ (37105/10000 : ℝ) :=
  sorry

/-- finite Green existence from the analytic RMT; original unconditional row remains open. -/
theorem finite_green_exists_given_jordan (hjordan : Background.JordanCurveFact)
    (domain : Set ℂ) (hdomain : IsBoundedJordanDomain domain) (pole : ℂ) (hpole : pole ∈ domain) :
    ∃ green : ℂ → ℝ, IsClassicalGreen domain pole green :=
  sorry

/-- component-frontier polynomial modulus at the defining radius. -/
theorem lemniscate_frontier_value (poly : ℂ[X]) (hzero : poly.eval 0 = 0)
    (height : ℝ) (hheight : 0 < height) (point : ℂ)
    (hpoint : point ∈ frontier (lemniscateComponent poly height)) : ‖poly.eval point‖ = height :=
  sorry

/-- normalized boundary-critical witness has unit polynomial modulus. -/
theorem jatar_ng_boundary_value (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X])
    (hpoly : IsSchlichtNormalized degree poly) :
    ∃ point ∈ frontier (lemniscateComponent poly 1), point ∈ criticalPoints poly ∧ ‖poly.eval point‖ = 1 :=
  sorry

/-- positive leading coefficient; the strict upper bound is a separate cited row. -/
theorem jatar_ng_leading_coefficient_positive (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X])
    (hpoly : IsSchlichtNormalized degree poly) : 0 < ‖poly.leadingCoeff‖ :=
  sorry

/-- strict leading-coefficient upper restriction, direct external restatement. -/
theorem jatar_ng_leading_lt_one (degree : ℕ) (hdegree : 2 ≤ degree) (poly : ℂ[X])
    (hpoly : IsSchlichtNormalized degree poly) : ‖poly.leadingCoeff‖ < 1 :=
  sorry

/-- strict upper half of the degree-seven best-bound enclosure; lower cover remains separate. -/
theorem best_seven_upper : bestBound 7 < (20191/10000 : ℝ) :=
  sorry

/-- strict upper half of the degree-eight best-bound enclosure; lower cover remains separate. -/
theorem best_eight_upper : bestBound 8 < (20550/10000 : ℝ) :=
  sorry

/-- historical conditional Green coverage from disk coordinates; the original is independently proved without this premise. -/
theorem finite_green_conformal_invariance_given_jordan (hjordan : Background.JordanCurveFact)
    (domain image : Set ℂ) (hdomain : IsBoundedJordanDomain domain)
    (himage : IsBoundedJordanDomain image) (func : ℂ → ℂ)
    (hfunc : IsConformalOnto func domain image) (pole point : ℂ)
    (hpole : pole ∈ domain) (hpoint : point ∈ domain) (hdistinct : point ≠ pole)
    (greenDomain greenImage : ℂ → ℝ)
    (hgreenDomain : IsClassicalGreen domain pole greenDomain)
    (hgreenImage : IsClassicalGreen image (func pole) greenImage) :
    greenImage (func point) = greenDomain point :=
  sorry

/-- upper half of the concrete capacity formula; the original equality remains open. -/
theorem capacity_exterior_upper_given_coefficient
    (hcoefficient : Background.CoefficientUpperFact)
    (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (hcritical : critical ≠ 0)
    (homit : critical ∉ inverse '' disk 1) :
    capacityTD (closure (exteriorImage inverse height critical)) ≤
      ‖critical‖ / (height * ‖deriv inverse 0‖) :=
  sorry

/-- degree-seven comparison with explicit main-theorem premises; original unconditional row remains open. -/
theorem range_7_best_improvement_given_background (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact) :
    target 7 < bestBound 7 ∧ Kd 7 ≤ (bestBound 7 : EReal) ∧
      fujikawa 7 ≤ conte 7 ∧ fujikawa 7 ≤ beardon 7 ∧ fujikawa 7 ≤ dubinin 7 ∧
      (24842/10000 : ℝ) < fujikawa 7 ∧ fujikawa 7 < 24843/10000 :=
  sorry

end SmaleRate.Paper

