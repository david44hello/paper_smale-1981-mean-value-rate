/-
SmaleRate — approved external inputs.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
No result proved by this paper is included here.
-/
import SmaleRate.Defs.Basic

namespace SmaleRate.Cited
open Set

/-- REFEREED reference: NIST DLMF 19.9.5, https://dlmf.nist.gov/19.9.E5 .
Source domain: "Throughout this subsection 0<k<1" (exception 19.9.4 is not used).
Source equation, verbatim mathematical notation:
  ln((1+sqrt(k'))^2/k) < pi K'(k)/(2 K(k)) < ln(2(1+k')/k).
DLMF attributes this to Lehto–Virtanen (1973), p.62.
Definition match: DLMF 19.2.4, 19.2.8, 19.2.9; K' = K(sqrt(1-k^2)).
Our sqrt-of-product integrand equals the product-of-sqrts integrand on [0,1].
This imports neither the derived mu<log(4/k) nor the paper's Delta estimates. -/
axiom dlmf_19_9_5 (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) :
    Real.log ((1 + Real.sqrt (complement modulus)) ^ 2 / modulus) < mu modulus ∧
    mu modulus < Real.log (2 * (1 + complement modulus) / modulus)

/-- REFEREED reference: NIST DLMF 19.8.5, https://dlmf.nist.gov/19.8.E5 .
Source equation: K(k) = pi/(2 M(1,k')), with -infinity<k^2<1.
Only the weaker instance 0<k<1 is imported here.
DLMF section19.8(i) source note: Cox (1984,1985); Borwein–Borwein (1987), Chapter1.
Definition match: K,K' from DLMF 19.2.4/19.2.8/19.2.9; AGM recurrence from19.8.1:
  a_(n+1)=(a_n+g_n)/2, g_(n+1)=sqrt(a_n*g_n).
Our agm is inf(a_n). Monotone bracketing and the common-limit bridge remain proofs;
the derived mu/AGM quotient is not an additional imported claim. -/
axiom dlmf_19_8_5 (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) :
    ellipticK modulus = Real.pi / (2 * agm (complement modulus))

/-- REFEREED: D. Betsakos, J. Aust. Math. Soc.94 (2013),145–157,
Theorem1.1, p.146, DOI10.1017/S1446788712000559.
Source hypothesis: "Let f be a nonconstant bounded holomorphic function in D with f(0)=0."
Source (1.2): |f(z)| <= 4 d(f(D))/e^(mu(|z|)), z in D.
Source definitions: mu(r)=pi K'(r)/(2 K(r)), K'(r)=K(sqrt(1-r^2)),
K(r)=integral_0^1 dt/sqrt((1-t^2)(1-r^2*t^2)).
https://doi.org/10.1017/S1446788712000559
The nonzero-point restriction is weaker than the source's zero-point limit convention.
Our inf-TD matches the source's limit-TD through the separate OWN diameter_decreasing bridge
(Ransford5.5.2); this declaration does not prove that bridge. Equality is unused context
and is deliberately NOT included. Neither the constructed domain nor its coefficient bound
is imported. -/
axiom betsakos_2013
    (func : ℂ → ℂ) (hhol : DifferentiableOn ℂ func (disk 1))
    (hbound : Bornology.IsBounded (func '' disk 1)) (hzero : func 0 = 0)
    (hnonconstant : ∃ first ∈ disk 1, ∃ second ∈ disk 1, func first ≠ func second)
    (point : ℂ) (hpoint : point ∈ disk 1) (hnonzero : point ≠ 0) :
    ‖func point‖ ≤ 4 * transfiniteDiameter (func '' disk 1) * Real.exp (-mu ‖point‖)

end SmaleRate.Cited
