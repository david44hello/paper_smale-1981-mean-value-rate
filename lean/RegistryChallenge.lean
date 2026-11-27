/-
SmaleRate — standalone Palomar registry challenge statements (proof bodies left open).
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.MetricSpace.Basic

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section

namespace SmaleRate

open Polynomial Filter Set
open scoped Topology BigOperators

/-- Explicit `Nat.AtLeastTwo` instances so `2` and `4` synthesize identically across modules. -/
instance instAtLeastTwo2 : Nat.AtLeastTwo 2 := ⟨by decide⟩
instance instAtLeastTwo4 : Nat.AtLeastTwo 4 := ⟨by decide⟩

/-- Complex polynomials of degree `degree` normalized by `p(0) = 0` and `p'(0) ≠ 0`. -/
def IsPd (degree : ℕ) (poly : ℂ[X]) : Prop :=
  poly.natDegree = degree ∧ poly.eval 0 = 0 ∧ poly.derivative.eval 0 ≠ 0

/-- Critical points of `poly`, i.e., roots of `poly'`. -/
def criticalPoints (poly : ℂ[X]) : Set ℂ := {point | poly.derivative.eval point = 0}

/-- Normalized critical-value ratio `|p(ζ) / (ζ p'(0))|`. -/
def criticalRatio (poly : ℂ[X]) (point : ℂ) : ℝ :=
  ‖poly.eval point / (point * poly.derivative.eval 0)‖

/-- Set of critical-value ratios of `poly`. -/
def criticalRatios (poly : ℂ[X]) : Set ℝ := criticalRatio poly '' criticalPoints poly

/-- Smale functional `S(p) = inf_{p'(ζ) = 0} |p(ζ) / (ζ p'(0))|`. -/
def S (poly : ℂ[X]) : ℝ := sInf (criticalRatios poly)

/-- Degree-`d` Smale mean value constant `K(d) = sup_{p ∈ P_d} S(p)` in `EReal`. -/
def Kd (degree : ℕ) : EReal :=
  ⨆ poly : {poly : ℂ[X] // IsPd degree poly}, ((S poly.val : ℝ) : EReal)

/-- Complementary elliptic modulus `k' = sqrt(1 - k^2)`. -/
def complement (radius : ℝ) : ℝ := Real.sqrt (1 - radius ^ 2)

/-- Complete elliptic integral of the first kind `K(k)`. -/
def ellipticK (radius : ℝ) : ℝ :=
  ∫ param : ℝ in (0)..1, 1 / Real.sqrt ((1 - param ^ 2) * (1 - radius ^ 2 * param ^ 2))

/-- Grötzsch ring modulus `μ(r) = (π / 2) K(sqrt(1 - r^2)) / K(r)`. -/
def mu (radius : ℝ) : ℝ := Real.pi / 2 * ellipticK (complement radius) / ellipticK radius

/-- Natural logarithm `ℓ(d) = log d`. -/
def ell (degree : ℕ) : ℝ := Real.log degree

/-- Parameter choice `L(d) = 1 / (4 log d)` for Corollary 1.2. -/
def Lchoice (degree : ℕ) : ℝ := 1 / (4 * ell degree)

/-- Radius `r(d, L) = exp(-L / d)`. -/
def radius (degree : ℕ) (length : ℝ) : ℝ := Real.exp (-length / degree)

/-- Parametric upper bound `(4 / y) exp(-μ(y^{1/d}))` of Theorem 1.1. -/
def yBound (degree : ℕ) (height : ℝ) : ℝ :=
  (4 / height) * Real.exp (-mu (height ^ (1 / (degree : ℝ))))

/-- Optimal Theorem 1.1 bound `B(d) = inf_{y ∈ (0, 1)} yBound(d, y)`. -/
def bestBound (degree : ℕ) : ℝ := sInf (yBound degree '' Ioo 0 1)

/-- Elementary majorant `M(d)` used in Corollary 1.2 (Steps 1–3 and Table 3). -/
def majorant (degree : ℕ) : ℝ :=
  4 * Real.exp (Lchoice degree - Real.pi ^ 2 /
    (4 * Real.log (4 / complement (radius degree (Lchoice degree)))))

/-- Target bound `4 - 4 / log d` of Corollary 1.2. -/
def target (degree : ℕ) : ℝ := 4 - 4 / ell degree

/-- Normalized asymptotic gap `(4 - B(d)) log d` of Proposition 3.4. -/
def gap (degree : ℕ) : ℝ := (4 - bestBound degree) * ell degree

/-- Open disk `{z ∈ ℂ | |z| < bound}`. -/
def disk (bound : ℝ) : Set ℂ := Metric.ball 0 bound

/-- Holomorphic and injective map on a planar domain. -/
def IsUnivalentOn (func : ℂ → ℂ) (domain : Set ℂ) : Prop :=
  DifferentiableOn ℂ func domain ∧ InjOn func domain

/-- Conformal bijection from `domain` onto `image`. -/
def IsConformalOnto (func : ℂ → ℂ) (domain image : Set ℂ) : Prop :=
  IsUnivalentOn func domain ∧ func '' domain = image

/-- Bounded planar Jordan domain whose frontier is a continuous injective image of the unit circle. -/
def IsBoundedJordanDomain (domain : Set ℂ) : Prop :=
  IsOpen domain ∧ IsPreconnected domain ∧ domain.Nonempty ∧ Bornology.IsBounded domain ∧
    ∃ curve : ℂ → ℂ, ContinuousOn curve (Metric.sphere 0 1) ∧
      InjOn curve (Metric.sphere 0 1) ∧ curve '' Metric.sphere 0 1 = frontier domain

/-- Geometric `n`-diameter of a subset of `ℂ`. -/
def nDiameter (domain : Set ℂ) (count : ℕ) : ℝ :=
  sSup {value | ∃ points : Fin count → ℂ, (∀ index, points index ∈ domain) ∧
    value = (∏ first : Fin count, ∏ second ∈ Finset.univ.filter (first < ·),
      ‖points first - points second‖) ^ (2 / ((count : ℝ) * (count - 1 : ℕ)))}

/-- Geometric transfinite diameter `inf_{n ≥ 2} d_n(domain)`. -/
def transfiniteDiameter (domain : Set ℂ) : ℝ :=
  sInf {value | ∃ count ≥ 2, value = nDiameter domain count}

/-- Alias for geometric transfinite diameter. -/
def capacityTD (compactSet : Set ℂ) : ℝ := transfiniteDiameter compactSet

namespace Background

/-- Planar Jordan–Schoenflies topology hypothesis: a bounded Jordan domain has simply connected
interior and connected complement of its closure. -/
def JordanCurveFact : Prop :=
  ∀ domain : Set ℂ, IsBoundedJordanDomain domain →
    IsSimplyConnected domain ∧ IsConnected (closure domain)ᶜ

/-- Exterior conformal-map transfinite-diameter upper bound (Ransford 1995, Cor. 5.2.2 & Thm. 5.5.2):
if `phi` maps `{|z| > 1}` conformally onto `Kᶜ` with `phi(z) = a z + O(1)` at `∞`, then `d(K) ≤ |a|`. -/
def CoefficientUpperFact : Prop :=
  ∀ (compactSet : Set ℂ), IsCompact compactSet → IsConnected compactSet →
    (∃ first ∈ compactSet, ∃ second ∈ compactSet, first ≠ second) →
    IsConnected compactSetᶜ →
    ∀ (phi : ℂ → ℂ),
      IsConformalOnto phi {point : ℂ | 1 < ‖point‖} compactSetᶜ →
    ∀ (coefficient : ℂ), coefficient ≠ 0 →
      (∃ constant : ℂ, Tendsto (fun point : ℂ => phi point - coefficient * point)
        (cocompact ℂ) (𝓝 constant)) →
      capacityTD compactSet ≤ ‖coefficient‖

end Background

namespace Registry

/-- Refereed input: NIST DLMF 19.9.5 (Lehto–Virtanen 1973, p. 62) two-sided bound on `μ(k)`. -/
def DLMF1995Fact : Prop :=
  ∀ (modulus : ℝ), modulus ∈ Ioo 0 1 →
    Real.log ((1 + Real.sqrt (complement modulus)) ^ 2 / modulus) < mu modulus ∧
    mu modulus < Real.log (2 * (1 + complement modulus) / modulus)

/-- Refereed input: D. Betsakos, *J. Aust. Math. Soc.* 94 (2013), Theorem 1.1, p. 146
(transfinite-diameter growth inequality for bounded holomorphic maps on the unit disk). -/
def Betsakos2013Fact : Prop :=
  ∀ (func : ℂ → ℂ), DifferentiableOn ℂ func (disk 1) →
    Bornology.IsBounded (func '' disk 1) → func 0 = 0 →
    (∃ first ∈ disk 1, ∃ second ∈ disk 1, func first ≠ func second) →
    ∀ (point : ℂ), point ∈ disk 1 → point ≠ 0 →
      ‖func point‖ ≤ 4 * transfiniteDiameter (func '' disk 1) * Real.exp (-mu ‖point‖)

/-- Theorem 1.1 (conditional on the four explicit hypotheses): for every `d ≥ 2` and `y ∈ (0, 1)`,
`K(d) ≤ (4 / y) exp(-μ(y^{1/d}))`. -/
theorem thm_1_1_conditional
    (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact)
    (hbetsakos : Betsakos2013Fact)
    (hdlmf : DLMF1995Fact)
    (degree : ℕ) (hdegree : 2 ≤ degree)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    Kd degree ≤ (yBound degree height : EReal) := by sorry

/-- Corollary 1.2 (conditional on the four explicit hypotheses): for every `d ≥ 8`,
`K(d) < 4 - 4 / log d`. -/
theorem cor_1_2_conditional
    (hjordan : Background.JordanCurveFact)
    (hcoefficient : Background.CoefficientUpperFact)
    (hbetsakos : Betsakos2013Fact)
    (hdlmf : DLMF1995Fact)
    (degree : ℕ) (hdegree : 8 ≤ degree) :
    Kd degree < (target degree : EReal) := by sorry

/-- Proposition 3.4 (limit, conditional on DLMF 19.9.5 alone): `(4 - B(d)) log d → 2 π^2`. -/
theorem prop_3_4_limit_conditional (hdlmf : DLMF1995Fact) :
    Tendsto gap atTop (𝓝 (2 * Real.pi ^ 2)) := by sorry

/-- Proposition 3.4 (explicit upper bound, conditional on DLMF 19.9.5 alone):
for every `d ≥ 8`, `(4 - B(d)) log d ≤ 2 π^2 / (1 - π^2 / (d (log d)^2))`. -/
theorem prop_3_4_upper_conditional (hdlmf : DLMF1995Fact)
    (degree : ℕ) (hdegree : 8 ≤ degree) :
    gap degree ≤ 2 * Real.pi ^ 2 / (1 - Real.pi ^ 2 / ((degree : ℝ) * (ell degree) ^ 2)) := by sorry

/-- Corollary 1.2 Steps 2 & 3 (unconditional, standard axioms only): `M(d) ≤ 4 - 4 / log d`
for all `d ≥ 8`, with strict inequality `M(d) < 4 - 4 / log d` for all thirteen finite
Table 3 degrees `8 ≤ d ≤ 20`. -/
theorem cor_1_2_table3_and_majorant :
    (∀ degree : ℕ, 8 ≤ degree → majorant degree ≤ target degree) ∧
    (∀ degree : ℕ, 8 ≤ degree → degree ≤ 20 → majorant degree < target degree) := by sorry

end Registry

end SmaleRate
