/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.GreenCoordinates
import SmaleRate.Proofs.UnivalentDomain

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric
open scoped Topology

theorem finite_green_conformal_given_jordan (hjordan : Background.JordanCurveFact)
    (domain image : Set ℂ) (hdomain : IsBoundedJordanDomain domain)
    (himage : IsBoundedJordanDomain image) (func : ℂ → ℂ)
    (hfunc : IsConformalOnto func domain image) (pole point : ℂ)
    (hpole : pole ∈ domain) (hpoint : point ∈ domain) (hdistinct : point ≠ pole)
    (greenDomain greenImage : ℂ → ℝ)
    (hgreenDomain : IsClassicalGreen domain pole greenDomain)
    (hgreenImage : IsClassicalGreen image (func pole) greenImage) :
    greenImage (func point) = greenDomain point := by
  have hmap : MapsTo func domain image := by
    intro member hmember
    rw [← hfunc.2]
    exact mem_image_of_mem func hmember
  obtain ⟨coordinate, hsource, hunit, hzero, hanalytic, hderivative⟩ :=
    disk_equivalence_given_jordan hjordan image himage (func pole) (hmap hpole)
  have hinjective : InjOn (coordinate : ℂ → ℂ) image := by
    rw [← hsource]
    exact coordinate.injOn
  have hcomposed : IsUnivalentOn ((coordinate : ℂ → ℂ) ∘ func) domain :=
    ⟨hanalytic.differentiableOn.comp hfunc.1.1 hmap,
      hinjective.comp hfunc.1.2 hmap⟩
  have hcomposed_image : ((coordinate : ℂ → ℂ) ∘ func) '' domain = disk 1 := by
    change (fun member : ℂ => coordinate (func member)) '' domain = disk 1
    rw [← image_image (coordinate : ℂ → ℂ) func, hfunc.2, ← hsource,
      coordinate.image_source_eq_target, hunit]
  let equiv : OpenPartialHomeomorph ℂ ℂ :=
    univalentOpenPartialHomeomorph ((coordinate : ℂ → ℂ) ∘ func) domain
      hdomain.1 hdomain.2.1 hdomain.2.2.1 hcomposed
  have htarget : equiv.target = disk 1 := hcomposed_image
  have hcomposed_analytic : AnalyticOnNhd ℂ (equiv : ℂ → ℂ) equiv.source :=
    (Complex.analyticOnNhd_iff_differentiableOn hdomain.1).mpr hcomposed.1
  have hcomposed_deriv : deriv (equiv : ℂ → ℂ) pole ≠ 0 :=
    univalent_domain_deriv_ne_zero ((coordinate : ℂ → ℂ) ∘ func) domain
      hdomain.1 hdomain.2.1 hdomain.2.2.1 hcomposed pole hpole
  have hcomposed_zero : equiv pole = 0 := hzero
  have hdomain_coordinate := green_eq_disk_coordinate equiv htarget hdomain.2.1 pole hpole
    hcomposed_zero hcomposed_analytic hcomposed_deriv greenDomain hgreenDomain
    point hpoint hdistinct
  have himage_coordinate := green_eq_disk_coordinate coordinate hunit
    (by rw [hsource]; exact himage.2.1) (func pole)
    (by rw [hsource]; exact hmap hpole) hzero
    (by rw [hsource]; exact hanalytic) hderivative greenImage
    (by rw [hsource]; exact hgreenImage) (func point)
    (by rw [hsource]; exact hmap hpoint)
    (fun heq => hdistinct (hfunc.1.2 hpoint hpole heq))
  exact himage_coordinate.trans hdomain_coordinate.symm

end SmaleRate.Proofs

#check SmaleRate.Proofs.finite_green_conformal_given_jordan
#print axioms SmaleRate.Proofs.finite_green_conformal_given_jordan
