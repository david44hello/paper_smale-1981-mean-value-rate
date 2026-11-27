/-
SmaleRate — concrete exterior geometry.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.ExteriorMap
import Smale.Proofs.JNUnivalent
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology

/-- The actual compact subdisk image has preconnected complement; no Jordan theorem is assumed. -/
theorem inverse_closure_compl_isPreconnected (inverse : ℂ → ℂ)
    (hinverse : IsUnivalentOn inverse (disk 1))
    (height : ℝ) (hheight : height ∈ Ioo 0 1) :
    IsPreconnected (closure (inverseDomain inverse height))ᶜ := by
  rw [inverse_image_closure inverse hinverse height hheight]
  exact Smale.compl_image_closedBall_isPreconnected hinverse hheight.1.le hheight.2

/-- The same concrete geometry as the old conditional helper, with its Jordan premise removed. -/
theorem exterior_image_geometry_proved
    (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (hcritical : critical ≠ 0)
    (homit : critical ∉ inverse '' disk 1) :
    IsBoundedJordanDomain (exteriorImage inverse height critical) ∧
      (0 : ℂ) ∈ exteriorImage inverse height critical ∧
      (-1 : ℂ) ∈ exteriorImage inverse height critical := by
  let domain := inverseDomain inverse height
  have hgeometry := (inverse_jordan_domain_proved inverse hinverse hzero height hheight).1
  have hbase : (0 : ℂ) ∈ domain := ⟨0, by simp [disk, hheight.1], hzero⟩
  have hout : critical ∉ closure domain := by
    intro hmember
    exact homit (inverse_image_closure_subset inverse hinverse height hheight hmember)
  have houtside : IsConnected (closure domain)ᶜ :=
    ⟨⟨critical, hout⟩, inverse_closure_compl_isPreconnected inverse hinverse height hheight⟩
  have hconnected := invertedExterior_connected domain hgeometry.2.2.2.1 hbase
    houtside critical hcritical
  have hfrontier := invertedExterior_frontier domain hgeometry.1 hgeometry.2.2.2.1 hbase
    (inverseDomain_regular inverse hinverse height hheight) critical hcritical
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

/-- Reciprocal inversion sends the connected punctured disk onto the exterior unit disk. -/
theorem exterior_unit_disk_isConnected : IsConnected {point : ℂ | 1 < ‖point‖} := by
  let annulus : Set ℂ := {point : ℂ | 0 < ‖point‖ ∧ ‖point‖ < 1}
  have hannulus : IsConnected annulus := by
    refine ⟨⟨(1 / 2 : ℂ), ?_⟩, Smale.annulus_isPreconnected (by norm_num)⟩
    norm_num [annulus]
  have hcont : ContinuousOn (fun point : ℂ => 1 / point) annulus := by
    intro point hpoint
    exact (continuousAt_const.div continuousAt_id
      (norm_pos_iff.mp hpoint.1)).continuousWithinAt
  have himage : (fun point : ℂ => 1 / point) '' annulus = {point : ℂ | 1 < ‖point‖} := by
    ext point
    constructor
    · rintro ⟨source, hsource, rfl⟩
      change 1 < ‖(1 : ℂ) / source‖
      rw [norm_div, norm_one]
      exact (one_lt_div hsource.1).mpr hsource.2
    · intro hpoint
      have hnorm : 0 < ‖point‖ := lt_trans zero_lt_one hpoint
      refine ⟨1 / point, ?_, by simp⟩
      change 0 < ‖(1 : ℂ) / point‖ ∧ ‖(1 : ℂ) / point‖ < 1
      rw [norm_div, norm_one]
      exact ⟨div_pos zero_lt_one hnorm, (div_lt_one hnorm).mpr hpoint⟩
  rw [← himage]
  exact hannulus.image _ hcont

/-- Connectedness of the actual exterior closure complement follows from its proved conformal range. -/
theorem exterior_image_closure_compl_isConnected
    (inverse : ℂ → ℂ) (hinverse : IsUnivalentOn inverse (disk 1)) (hzero : inverse 0 = 0)
    (height : ℝ) (hheight : height ∈ Ioo 0 1) (critical : ℂ) (hcritical : critical ≠ 0) :
    IsConnected (closure (exteriorImage inverse height critical))ᶜ := by
  have hconformal := exterior_conformal_map_proved inverse hinverse hzero height hheight
    critical hcritical
  rw [← hconformal.2]
  exact exterior_unit_disk_isConnected.image _ hconformal.1.1.continuousOn

end SmaleRate.Proofs

#check SmaleRate.Proofs.inverse_closure_compl_isPreconnected
#check SmaleRate.Proofs.exterior_image_geometry_proved
#check SmaleRate.Proofs.exterior_unit_disk_isConnected
#check SmaleRate.Proofs.exterior_image_closure_compl_isConnected
#print axioms SmaleRate.Proofs.inverse_closure_compl_isPreconnected
#print axioms SmaleRate.Proofs.exterior_image_geometry_proved
#print axioms SmaleRate.Proofs.exterior_unit_disk_isConnected
#print axioms SmaleRate.Proofs.exterior_image_closure_compl_isConnected
