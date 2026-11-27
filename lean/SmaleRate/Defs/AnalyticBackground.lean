/-
SmaleRate — analytic background interfaces.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
These are concrete mathematical predicates, not asserted background facts or assumptions.
-/
import SmaleRate.Defs.Basic

noncomputable section
namespace SmaleRate
open Filter Set InnerProductSpace Polynomial
open scoped Topology

/-- Classical Green function for a finite pole on a regular bounded planar domain.
Values outside the domain are explicitly zero; the value at the pole is not used. -/
def IsClassicalGreen (domain : Set ℂ) (pole : ℂ) (green : ℂ → ℝ) : Prop :=
  Bornology.IsBounded domain ∧ pole ∈ domain ∧
  HarmonicOnNhd green (domain \ {pole}) ∧
  (∀ point ∈ domain \ {pole}, 0 < green point) ∧
  (∃ regular : ℂ → ℝ, HarmonicAt regular pole ∧
    ∀ᶠ point in 𝓝[≠] pole, green point + Real.log ‖point-pole‖ = regular point) ∧
  (∀ point ∈ frontier domain, Tendsto green (𝓝[domain] point) (𝓝 0)) ∧
  (∀ point ∉ domain, green point = 0)

/-- Classical exterior Green function with pole at infinity. The regular part at infinity
is specified in the u=1/z chart, not by treating infinity as a complex number. -/
def IsClassicalExteriorGreen (compactSet : Set ℂ) (green : ℂ → ℝ) : Prop :=
  HarmonicOnNhd green compactSetᶜ ∧
  (∀ point ∉ compactSet, 0 < green point) ∧
  (∃ regular : ℂ → ℝ, HarmonicAt regular 0 ∧
    ∀ᶠ point in 𝓝[≠] (0 : ℂ), green point⁻¹ + Real.log ‖point‖ = regular point) ∧
  (∀ point ∈ frontier compactSet, Tendsto green (𝓝[compactSetᶜ] point) (𝓝 0)) ∧
  (∀ point ∈ compactSet, green point = 0)

def diskGreen (point : ℂ) : ℝ := by
  classical
  exact if point ∈ disk 1 then Real.log (1/‖point‖) else 0

/-- Jatar–Ng's component of the polynomial lemniscate that contains the origin. -/
def lemniscateComponent (poly : ℂ[X]) (height : ℝ) : Set ℂ :=
  connectedComponentIn (poly.eval ⁻¹' disk height) 0
def univalentRadii (poly : ℂ[X]) : Set ℝ :=
  {height | 0 < height ∧ IsConformalOnto poly.eval (lemniscateComponent poly height) (disk height)}
def maxUnivalentRadius (poly : ℂ[X]) : ℝ := sSup (univalentRadii poly)

/-- Source normalization: p'(0)=1 and maximal UNIVALENT radius=1.
This is distinct from least modulus of ALL critical values being 1. -/
def IsSchlichtNormalized (degree : ℕ) (poly : ℂ[X]) : Prop :=
  IsPd degree poly ∧ poly.derivative.eval 0 = 1 ∧ maxUnivalentRadius poly = 1

def jatarNgBound (degree : ℕ) : ℝ :=
  1 + 3*(degree : ℝ)^(-1/4 : ℝ)*Real.sqrt (Real.log (2*Real.exp 1*Real.sqrt degree))

/-- Rational data for a finite interval-cover certificate, without asserting any check. -/
structure CertifiedBoxData where
  left : ℚ
  right : ℚ
  lower : ℚ

def BoxEndpointBound (degree : ℕ) (box : CertifiedBoxData) : Prop :=
  (box.lower : ℝ) ≤ 4*Real.exp (box.left : ℝ)*Real.exp (-mu (radius degree (box.right : ℝ)))
def ValidBox (box : CertifiedBoxData) : Prop := 0 ≤ box.left ∧ box.left < box.right ∧ box.right ≤ 1
def CoversUnit (boxes : List CertifiedBoxData) : Prop :=
  ∀ length ∈ Ioc (0 : ℝ) 1, ∃ box ∈ boxes, (box.left : ℝ) < length ∧ length ≤ (box.right : ℝ)

end SmaleRate
