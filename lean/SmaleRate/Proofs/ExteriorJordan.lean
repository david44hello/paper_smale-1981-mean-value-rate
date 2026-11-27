/-
SmaleRate — Jordan geometry of the inverted exterior.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.ExteriorGeometry
import SmaleRate.Defs.BackgroundFacts
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology

theorem inverseDomain_regular (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1))
    (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    interior (closure (inverseDomain inverse height)) = inverseDomain inverse height := by
  apply subset_antisymm
  · intro point hpoint
    have hclosure := interior_subset hpoint
    rw [inverse_image_closure inverse hinverse height hheight] at hclosure
    obtain ⟨source, hsource, rfl⟩ := hclosure
    have hsource_disk := smaller_closed_disk_subset height hheight hsource
    have hcont := hinverse.1.continuousOn.continuousAt (isOpen_ball.mem_nhds hsource_disk)
    have hlocal := hcont.preimage_mem_nhds (isOpen_interior.mem_nhds hpoint)
    have hclosed_nhds : closedBall (0 : ℂ) height ∈ 𝓝 source := by
      filter_upwards [hlocal, isOpen_ball.mem_nhds hsource_disk] with other hother hother_disk
      have himage := interior_subset hother
      rw [inverse_image_closure inverse hinverse height hheight] at himage
      obtain ⟨preimage, hpreimage, heq⟩ := himage
      have hequal := hinverse.2 (smaller_closed_disk_subset height hheight hpreimage) hother_disk heq
      exact hequal ▸ hpreimage
    have hball : source ∈ ball (0 : ℂ) height := by
      simpa only [interior_closedBall (0 : ℂ) hheight.1.ne'] using
        mem_interior_iff_mem_nhds.mpr hclosed_nhds
    exact ⟨source, hball, rfl⟩
  · have hsubset := interior_mono (subset_closure : inverseDomain inverse height ⊆
        closure (inverseDomain inverse height))
    simpa only [(inverse_image_open inverse hinverse height hheight).interior_eq] using hsubset

theorem invertedExterior_frontier (domain : Set ℂ) (hopen : IsOpen domain)
    (hbounded : Bornology.IsBounded domain) (hzero : (0 : ℂ) ∈ domain)
    (hregular : interior (closure domain) = domain) (critical : ℂ) (hcritical : critical ≠ 0) :
    frontier (invertedExterior domain critical) = inversion critical '' frontier domain := by
  have hfrontier : frontier (closure domain) = frontier domain := by
    simp only [frontier, closure_closure, hregular, hopen.interior_eq]
  let equiv := inversionPartialHomeomorph critical hcritical
  have himage : equiv.IsImage (closure domain)ᶜ (invertedExterior domain critical) := by
    intro point hpoint
    change inversion critical point ∈ invertedExterior domain critical ↔ point ∉ closure domain
    rw [mem_invertedExterior_iff domain critical hcritical _
      (inversion_ne_zero critical hcritical point hpoint), inversion_involutive critical hcritical]
  apply subset_antisymm
  · intro point hpoint
    exact ⟨inversion critical point,
      invertedExterior_frontier_subset domain hbounded critical hcritical point hpoint,
      inversion_involutive critical hcritical point⟩
  · rintro point ⟨source, hsource, rfl⟩
    have hsource_ne : source ≠ 0 := by
      intro heq
      subst source
      exact hsource.2 (by simpa only [hopen.interior_eq] using hzero)
    have hmember : source ∈ frontier ((closure domain)ᶜ) := by
      simpa only [frontier_compl, hfrontier] using hsource
    exact (himage.frontier hsource_ne).mpr hmember

theorem invertedExterior_connected (domain : Set ℂ) (hbounded : Bornology.IsBounded domain)
    (hzero : (0 : ℂ) ∈ domain) (houtside : IsConnected (closure domain)ᶜ)
    (critical : ℂ) (hcritical : critical ≠ 0) : IsConnected (invertedExterior domain critical) := by
  have hcont : ContinuousOn (inversion critical) (closure domain)ᶜ := by
    intro point hpoint
    have hpoint_ne : point ≠ 0 := by
      rintro rfl
      exact hpoint (subset_closure hzero)
    exact (continuousAt_const.div continuousAt_id hpoint_ne).continuousWithinAt
  have hconnected := houtside.image (inversion critical) hcont
  have hzero_closure : (0 : ℂ) ∈ closure (inversion critical '' (closure domain)ᶜ) := by
    rw [mem_closure_iff_nhds]
    intro neighborhood hneighborhood
    have hlocal : ∀ᶠ point in 𝓝[≠] (0 : ℂ),
        point ∈ neighborhood ∧ point ∈ invertedExterior domain critical ∧ point ≠ 0 := by
      filter_upwards [nhdsWithin_le_nhds hneighborhood,
        nhdsWithin_le_nhds (invertedExterior_zero_nhds domain hbounded critical hcritical),
        self_mem_nhdsWithin] with point hp he hn
      exact ⟨hp, he, hn⟩
    obtain ⟨point, hp, he, hn⟩ := hlocal.exists
    refine ⟨point, hp, ?_⟩
    exact he.resolve_left hn
  apply hconnected.subset_closure (fun _ hp => Or.inr hp)
  rintro point (hpoint | hpoint)
  · exact hpoint ▸ hzero_closure
  · exact subset_closure hpoint

theorem exterior_image_geometry_given_jordan (hjordan : Background.JordanCurveFact)
    (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (hcritical : critical ≠ 0)
    (homit : critical ∉ inverse '' disk 1) :
    IsBoundedJordanDomain (exteriorImage inverse height critical) ∧
      (0 : ℂ) ∈ exteriorImage inverse height critical ∧
      (-1 : ℂ) ∈ exteriorImage inverse height critical := by
  let domain := inverseDomain inverse height
  have hgeometry := (inverse_jordan_domain_proved inverse hinverse hzero height hheight).1
  have hbase : (0 : ℂ) ∈ domain := ⟨0, by simp [disk, hheight.1], hzero⟩
  have hconnected := invertedExterior_connected domain hgeometry.2.2.2.1 hbase
    (hjordan domain hgeometry).2 critical hcritical
  have hfrontier := invertedExterior_frontier domain hgeometry.1 hgeometry.2.2.2.1 hbase
    (inverseDomain_regular inverse hinverse height hheight) critical hcritical
  have hout : critical ∉ closure domain := by
    intro hmember
    exact homit (inverse_image_closure_subset inverse hinverse height hheight hmember)
  refine ⟨⟨invertedExterior_open domain hgeometry.2.2.2.1 critical hcritical,
    hconnected.2, ⟨0, Or.inl rfl⟩,
    invertedExterior_bounded domain hgeometry.1 hbase critical hcritical, ?_⟩,
    Or.inl rfl, ?_⟩
  · obtain ⟨curve, hcurve_cont, hcurve_inj, hcurve_image⟩ := hgeometry.2.2.2.2
    have hcurve_frontier : MapsTo curve (sphere 0 1) (frontier domain) := by
      intro point hpoint
      rw [← hcurve_image]
      exact mem_image_of_mem curve hpoint
    have hfrontier_ne : ∀ point ∈ frontier domain, point ≠ 0 := by
      intro point hpoint heq
      subst point
      have hopen_domain : IsOpen domain := hgeometry.1
      exact hpoint.2 (by simpa only [hopen_domain.interior_eq] using hbase)
    refine ⟨inversion critical ∘ curve, ?_, ?_, ?_⟩
    · exact ((continuousOn_const.div continuousOn_id
        (fun point hp => hfrontier_ne point hp)).comp hcurve_cont hcurve_frontier)
    · intro first hfirst second hsecond heq
      exact hcurve_inj hfirst hsecond ((inversion_involutive critical hcritical).injective heq)
    · change (inversion critical ∘ curve) '' sphere 0 1 = frontier (invertedExterior domain critical)
      simp only [Function.comp_def]
      rw [← image_image (inversion critical) curve, hcurve_image, ← hfrontier]
  · apply (mem_invertedExterior_iff domain critical hcritical (-1) (by norm_num)).mpr
    simpa only [inversion, div_neg, div_one, neg_neg] using hout

end SmaleRate.Proofs


