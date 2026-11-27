/-
SmaleRate — definitions.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Mathlib

noncomputable section
namespace SmaleRate
open Polynomial Filter Set
open scoped Topology BigOperators

/-- The polynomial class of the Introduction, lines 27–35. -/
def IsPd (degree : ℕ) (poly : ℂ[X]) : Prop :=
  poly.natDegree = degree ∧ poly.eval 0 = 0 ∧ poly.derivative.eval 0 ≠ 0

def criticalPoints (poly : ℂ[X]) : Set ℂ := {point | poly.derivative.eval point = 0}

/-- Norm of the actual quotient in S(p), including p'(0). -/
def criticalRatio (poly : ℂ[X]) (point : ℂ) : ℝ :=
  ‖poly.eval point / (point * poly.derivative.eval 0)‖

def criticalRatios (poly : ℂ[X]) : Set ℝ := criticalRatio poly '' criticalPoints poly

/-- Attainment and nonemptiness are separate proof obligations for degree >= 2. -/
def S (poly : ℂ[X]) : ℝ := sInf (criticalRatios poly)

/-- Complete-lattice supremum; finiteness is proved separately, never assumed by definition. -/
def Kd (degree : ℕ) : EReal :=
  ⨆ poly : {poly : ℂ[X] // IsPd degree poly}, ((S poly.val : ℝ) : EReal)

def Kstar : EReal := ⨆ degree : {degree : ℕ // 2 ≤ degree}, Kd degree.val

def complement (radius : ℝ) : ℝ := Real.sqrt (1 - radius ^ 2)

/-- Complete elliptic integral, with its integrable endpoint singularity. -/
def ellipticK (radius : ℝ) : ℝ :=
  ∫ param : ℝ in (0)..1, 1 / Real.sqrt ((1 - param ^ 2) * (1 - radius ^ 2 * param ^ 2))

def mu (radius : ℝ) : ℝ := Real.pi / 2 * ellipticK (complement radius) / ellipticK radius

def ell (degree : ℕ) : ℝ := Real.log degree
def Lchoice (degree : ℕ) : ℝ := 1 / (4 * ell degree)
def radius (degree : ℕ) (length : ℝ) : ℝ := Real.exp (-length / degree)
def yBound (degree : ℕ) (height : ℝ) : ℝ :=
  (4 / height) * Real.exp (-mu (height ^ (1 / (degree : ℝ))))
def beta (degree : ℕ) (length : ℝ) : ℝ := 4 * Real.exp (length - mu (radius degree length))
def bestBound (degree : ℕ) : ℝ := sInf (yBound degree '' Ioo 0 1)
def majorant (degree : ℕ) : ℝ :=
  4 * Real.exp (Lchoice degree - Real.pi ^ 2 /
    (4 * Real.log (4 / complement (radius degree (Lchoice degree)))))
def target (degree : ℕ) : ℝ := 4 - 4 / ell degree
def lambda (degree : ℕ) (length : ℝ) : ℝ :=
  Real.log (8 * degree / (length * (1 - length / degree)))
def delta (degree : ℕ) (length : ℝ) : ℝ := 2 * Real.log (8 * degree / length) - 4 * length / degree
def gap (degree : ℕ) : ℝ := (4 - bestBound degree) * ell degree
def uniformLower (degree : ℕ) : ℝ :=
  4 * Real.exp (-Real.pi ^ 2 / (2 * ell degree - 2 * Real.pi ^ 2 / (ell degree * degree)))

def disk (bound : ℝ) : Set ℂ := Metric.ball 0 bound
/-- Holomorphic-and-injective instance of the paper's broader meromorphic univalence convention. -/
def IsUnivalentOn (func : ℂ → ℂ) (domain : Set ℂ) : Prop :=
  DifferentiableOn ℂ func domain ∧ InjOn func domain
def IsConformalOnto (func : ℂ → ℂ) (domain image : Set ℂ) : Prop :=
  IsUnivalentOn func domain ∧ func '' domain = image

/-- A bounded planar Jordan domain; the boundary is a continuous injective circle image. -/
def IsBoundedJordanDomain (domain : Set ℂ) : Prop :=
  IsOpen domain ∧ IsPreconnected domain ∧ domain.Nonempty ∧ Bornology.IsBounded domain ∧
    ∃ curve : ℂ → ℂ, ContinuousOn curve (Metric.sphere 0 1) ∧
      InjOn curve (Metric.sphere 0 1) ∧ curve '' Metric.sphere 0 1 = frontier domain

/-- The n-diameter. Only n >= 2 is used. -/
def nDiameter (domain : Set ℂ) (count : ℕ) : ℝ :=
  sSup {value | ∃ points : Fin count → ℂ, (∀ index, points index ∈ domain) ∧
    value = (∏ first : Fin count, ∏ second ∈ Finset.univ.filter (first < ·),
      ‖points first - points second‖) ^ (2 / ((count : ℝ) * (count - 1 : ℕ)))}

/-- Infimum of n-diameters for n >= 2. The bridge to the paper's decreasing-sequence limit
is the OPEN `diameter_decreasing` row (Ransford 5.5.2). -/
def transfiniteDiameter (domain : Set ℂ) : ℝ := sInf {value | ∃ count ≥ 2, value = nDiameter domain count}

/-- Alias for geometric transfinite diameter, not potential-theoretic capacity.
The conformal-coefficient boundary must cite Ransford 5.2.3 / Corollary 5.2.2 AND 5.5.2;
Fekete–Szegő is absorbed into that boundary, not proved by this alias. -/
def capacityTD (compactSet : Set ℂ) : ℝ := transfiniteDiameter compactSet

def inverseDomain (inverse : ℂ → ℂ) (height : ℝ) : Set ℂ := inverse '' disk height
def inversion (critical : ℂ) (point : ℂ) : ℂ := -critical / point

/-- Finite part of the inverted spherical exterior; 0 is the image of infinity. -/
def exteriorImage (inverse : ℂ → ℂ) (height : ℝ) (critical : ℂ) : Set ℂ :=
  {0} ∪ inversion critical '' (closure (inverseDomain inverse height))ᶜ

def IsInverseBranch (poly : ℂ[X]) (inverse : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ inverse (disk 1) ∧ inverse 0 = 0 ∧
    ∀ point ∈ disk 1, poly.eval (inverse point) = point

def NormalizedCriticalValues (poly : ℂ[X]) (critical : ℂ) : Prop :=
  critical ∈ criticalPoints poly ∧ ‖poly.eval critical‖ = 1 ∧
    ∀ point ∈ criticalPoints poly, 1 ≤ ‖poly.eval point‖

def agmPair (modulus : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, modulus)
  | index + 1 =>
    let previous := agmPair modulus index
    ((previous.1 + previous.2) / 2, Real.sqrt (previous.1 * previous.2))
def agm (modulus : ℝ) : ℝ := sInf (Set.range fun index => (agmPair modulus index).1)

def fujikawa (degree : ℕ) : ℝ :=
  4 * (1 + (degree - 2 : ℕ) * (4 : ℝ) ^ (-1 / ((degree : ℝ) - 1))) / ((degree : ℝ) + 1)
def conte (degree : ℕ) : ℝ := 4 * ((degree : ℝ) - 1) / ((degree : ℝ) + 1)
def beardon (degree : ℕ) : ℝ := (4 : ℝ) ^ (((degree : ℝ) - 2) / ((degree : ℝ) - 1))
def dubinin (degree : ℕ) : ℝ := ((degree : ℝ) - 1) / degree * beardon degree
def crane (degree : ℕ) : ℝ := 4 - (2263 / 1000) / Real.sqrt degree
def expandedLower (degree : ℕ) : ℝ := min (11 / 100000) ((56 / 1000) / Real.sqrt (ell degree))
def expandedUpper (degree : ℕ) : ℝ :=
  49000 * Real.sqrt (Real.log (Real.log (ell degree)) / ell degree)

end SmaleRate
