/-
SmaleRate — boundary obstruction at a maximal univalent radius.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import SmaleRate.Proofs.JnRadius
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SmaleRate.Proofs
open Set Filter Metric Topology Polynomial

theorem local_sheet_lens_subset (poly : ℂ[X]) (hzero : poly.eval 0 = 0)
    (point : ℂ) (hpoint : point ∈ closure (lemniscateComponent poly 1))
    (equiv : OpenPartialHomeomorph ℂ ℂ) (hequiv : (equiv : ℂ → ℂ) = poly.eval)
    (hsource : point ∈ equiv.source) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (htarget : ball (poly.eval point) epsilon ⊆ equiv.target) :
    equiv.symm '' (ball (poly.eval point) epsilon ∩ disk 1) ⊆ lemniscateComponent poly 1 := by
  let lens := ball (poly.eval point) epsilon ∩ disk 1
  have hlens : lens ⊆ equiv.target := fun _ hp => htarget hp.1
  have hneighborhood : IsOpen (equiv.source ∩ poly.eval ⁻¹' ball (poly.eval point) epsilon) :=
    equiv.open_source.inter (isOpen_ball.preimage poly.continuous)
  have hpoint_nhds : point ∈ equiv.source ∩ poly.eval ⁻¹' ball (poly.eval point) epsilon :=
    ⟨hsource, mem_ball_self hepsilon⟩
  obtain ⟨nearby, hnearby_nhds, hnearby_component⟩ :=
    mem_closure_iff_nhds.mp hpoint _ (hneighborhood.mem_nhds hpoint_nhds)
  have hnearby_value : poly.eval nearby ∈ lens := ⟨hnearby_nhds.2,
    connectedComponentIn_subset (poly.eval ⁻¹' disk 1) 0 hnearby_component⟩
  have hnearby_image : nearby ∈ equiv.symm '' lens := by
    refine ⟨poly.eval nearby, hnearby_value, ?_⟩
    rw [← congrFun hequiv nearby]
    exact equiv.left_inv hnearby_nhds.1
  have hpreconnected : IsPreconnected (equiv.symm '' lens) :=
    ((convex_ball (poly.eval point) epsilon).inter (convex_ball (0 : ℂ) 1)).isPreconnected.image
      equiv.symm (equiv.symm.continuousOn.mono hlens)
  have hunion : IsPreconnected (lemniscateComponent poly 1 ∪ equiv.symm '' lens) :=
    IsPreconnected.union nearby hnearby_component hnearby_image
      isPreconnected_connectedComponentIn hpreconnected
  have hsubset : lemniscateComponent poly 1 ∪ equiv.symm '' lens ⊆ poly.eval ⁻¹' disk 1 := by
    intro member hmember
    rcases hmember with hmember | ⟨value, hvalue, rfl⟩
    · exact connectedComponentIn_subset (poly.eval ⁻¹' disk 1) 0 hmember
    · change poly.eval (equiv.symm value) ∈ disk 1
      rw [← congrFun hequiv (equiv.symm value), equiv.right_inv (hlens hvalue)]
      exact hvalue.2
  exact fun member hmember => hunion.subset_connectedComponentIn
    (Or.inl (lemniscate_zero poly hzero 1 (by norm_num))) hsubset (Or.inr hmember)

theorem closure_injective_of_local_sheets (poly : ℂ[X]) (hzero : poly.eval 0 = 0)
    (hunivalent : InjOn poly.eval (lemniscateComponent poly 1))
    (hsheets : ∀ point ∈ closure (lemniscateComponent poly 1),
      ∃ equiv : OpenPartialHomeomorph ℂ ℂ,
        (equiv : ℂ → ℂ) = poly.eval ∧ point ∈ equiv.source) :
    InjOn poly.eval (closure (lemniscateComponent poly 1)) := by
  intro first hfirst second hsecond hsame
  change poly.eval first = poly.eval second at hsame
  obtain ⟨left, hleft, hleft_source⟩ := hsheets first hfirst
  obtain ⟨right, hright, hright_source⟩ := hsheets second hsecond
  have hleft_target : poly.eval first ∈ left.target := by
    simpa only [hleft] using left.map_source hleft_source
  have hright_target : poly.eval first ∈ right.target := by
    simpa only [hright, ← hsame] using right.map_source hright_source
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp
    ((left.open_target.inter right.open_target).mem_nhds ⟨hleft_target, hright_target⟩)
  have hleft_ball : ball (poly.eval first) epsilon ⊆ left.target :=
    fun _ hp => (hball hp).1
  have hright_ball : ball (poly.eval second) epsilon ⊆ right.target := by
    rw [← hsame]
    exact fun _ hp => (hball hp).2
  let lens := ball (poly.eval first) epsilon ∩ disk 1
  have hleft_image := local_sheet_lens_subset poly hzero first hfirst left hleft
    hleft_source epsilon hepsilon hleft_ball
  have hright_image : right.symm '' lens ⊆ lemniscateComponent poly 1 := by
    simpa only [lens, hsame] using local_sheet_lens_subset poly hzero second hsecond right hright
      hright_source epsilon hepsilon hright_ball
  have heq : EqOn (left.symm : ℂ → ℂ) right.symm lens := by
    intro value hvalue
    apply hunivalent (hleft_image (mem_image_of_mem left.symm hvalue))
      (hright_image (mem_image_of_mem right.symm hvalue))
    have hleft_inv : poly.eval (left.symm value) = value := by
      simpa only [hleft] using left.right_inv (hleft_ball hvalue.1)
    have hright_inv : poly.eval (right.symm value) = value := by
      simpa only [hright] using right.right_inv ((hball hvalue.1).2)
    exact hleft_inv.trans hright_inv.symm
  have hclosure : poly.eval first ∈ closure (disk 1) := by
    have h := image_closure_subset_closure_image poly.continuous (mem_image_of_mem poly.eval hfirst)
    exact closure_mono (by
      rintro value ⟨point, hp, rfl⟩
      exact connectedComponentIn_subset (poly.eval ⁻¹' disk 1) 0 hp) h
  have hcenter : poly.eval first ∈ closure lens :=
    isOpen_ball.inter_closure ⟨mem_ball_self hepsilon, hclosure⟩
  haveI : NeBot (𝓝[lens] (poly.eval first)) := mem_closure_iff_nhdsWithin_neBot.mp hcenter
  have hleft_cont := left.symm.continuousOn.continuousAt (left.open_target.mem_nhds hleft_target)
  have hright_cont := right.symm.continuousOn.continuousAt (right.open_target.mem_nhds hright_target)
  have hlimit_eq : left.symm (poly.eval first) = right.symm (poly.eval first) :=
    tendsto_nhds_unique_of_eventuallyEq (hleft_cont.tendsto.mono_left nhdsWithin_le_nhds)
      (hright_cont.tendsto.mono_left nhdsWithin_le_nhds)
      (heq.eventuallyEq_of_mem self_mem_nhdsWithin)
  have hleft_inv : left.symm (poly.eval first) = first := by
    simpa only [hleft] using left.left_inv hleft_source
  have hright_inv : right.symm (poly.eval first) = second := by
    simpa only [hright, ← hsame] using right.left_inv hright_source
  exact hleft_inv.symm.trans (hlimit_eq.trans hright_inv)

theorem radius_mem_of_open_inverse (poly : ℂ[X]) (height : ℝ) (hheight : 0 < height)
    (inverse : ℂ → ℂ) (hcontinuous : ContinuousOn inverse (disk height))
    (hzero : inverse 0 = 0) (hright : ∀ point ∈ disk height, poly.eval (inverse point) = point)
    (hopen : IsOpen (inverse '' disk height)) : height ∈ univalentRadii poly := by
  have himage := inverse_image_eq_lemniscate poly height hheight inverse hcontinuous hzero hright hopen
  refine ⟨hheight, ⟨poly.differentiable.differentiableOn, ?_⟩, ?_⟩
  · intro first hfirst second hsecond heq
    rw [← himage] at hfirst hsecond
    obtain ⟨left, hleft, rfl⟩ := hfirst
    obtain ⟨right, hright_mem, rfl⟩ := hsecond
    have heq' : left = right := (hright left hleft).symm.trans
      (heq.trans (hright right hright_mem))
    exact congrArg inverse heq'
  · apply subset_antisymm
    · rintro value ⟨point, hpoint, rfl⟩
      exact connectedComponentIn_subset (poly.eval ⁻¹' disk height) 0 hpoint
    · intro value hvalue
      exact ⟨inverse value, himage ▸ mem_image_of_mem inverse hvalue, hright value hvalue⟩

theorem larger_radius_of_local_sheets (poly : ℂ[X]) (hdegree : poly.natDegree ≠ 0)
    (hzero : poly.eval 0 = 0)
    (hconformal : IsConformalOnto poly.eval (lemniscateComponent poly 1) (disk 1))
    (hsheets : ∀ point ∈ closure (lemniscateComponent poly 1),
      ∃ equiv : OpenPartialHomeomorph ℂ ℂ,
        (equiv : ℂ → ℂ) = poly.eval ∧ point ∈ equiv.source) :
    ∃ height ∈ univalentRadii poly, 1 < height := by
  classical
  have hopenmap : IsOpenMap poly.eval := (poly.isOpenQuotientMap_eval hdegree).isOpenMap
  have hdegree' : 0 < poly.degree := natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdegree)
  have hclosure_image : poly.eval '' closure (lemniscateComponent poly 1) = closedBall 0 1 := by
    rw [← poly.isClosedMap_eval.closure_image_eq_of_continuous poly.continuous,
      hconformal.2, disk, closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
  have hcompact : IsCompact (closure (lemniscateComponent poly 1)) :=
    ((poly.isProperMap_eval hdegree').isCompact_preimage (isCompact_closedBall (0 : ℂ) 1)).of_isClosed_subset
      isClosed_closure (fun point hpoint => by
        have hmem := mem_image_of_mem poly.eval hpoint
        rw [hclosure_image] at hmem
        exact hmem)
  have hinj := closure_injective_of_local_sheets poly hzero hconformal.1.2 hsheets
  obtain ⟨domain, hopen, hsubset, hinj_domain⟩ := hinj.exists_isOpen_superset hcompact
    (fun point _ => poly.continuous.continuousAt) (by
      intro point hpoint
      obtain ⟨equiv, hequiv, hsource⟩ := hsheets point hpoint
      exact ⟨equiv.source, equiv.open_source.mem_nhds hsource, by simpa only [hequiv] using equiv.injOn⟩)
  let extension : OpenPartialHomeomorph ℂ ℂ := OpenPartialHomeomorph.ofContinuousOpen
    (hinj_domain.toPartialEquiv poly.eval domain) poly.continuous.continuousOn hopenmap hopen
  have hclosed_target : closedBall (0 : ℂ) 1 ⊆ extension.target := by
    rw [← hclosure_image]
    exact image_mono hsubset
  obtain ⟨epsilon, hepsilon, hthick⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open
    extension.open_target hclosed_target
  have hball : disk (epsilon+1) ⊆ extension.target := by
    rw [disk, ← thickening_closedBall hepsilon (by norm_num : (0 : ℝ) ≤ 1) (0 : ℂ)]
    exact hthick
  have hsource_zero : (0 : ℂ) ∈ extension.source :=
    hsubset (subset_closure (lemniscate_zero poly hzero 1 (by norm_num)))
  have hzero_inverse : extension.symm 0 = 0 := by
    have h := extension.left_inv hsource_zero
    change extension.symm (poly.eval 0) = 0 at h
    simpa only [hzero] using h
  have hright : ∀ value ∈ disk (epsilon+1), poly.eval (extension.symm value) = value :=
    fun value hvalue => extension.right_inv (hball hvalue)
  refine ⟨epsilon+1, radius_mem_of_open_inverse poly (epsilon+1) (by linarith) extension.symm
    (extension.symm.continuousOn.mono hball) hzero_inverse hright
    (extension.symm.isOpen_image_of_subset_source isOpen_ball hball), by linarith⟩

theorem jatar_ng_boundary_critical_exists_proved (degree : ℕ) (hdegree : 2 ≤ degree)
    (poly : ℂ[X]) (hpoly : IsSchlichtNormalized degree poly) :
    ∃ point ∈ frontier (lemniscateComponent poly 1), point ∈ criticalPoints poly := by
  classical
  have hdegree_ne : poly.natDegree ≠ 0 := by rw [hpoly.1.1]; omega
  have hone : (1 : ℝ) ∈ univalentRadii poly := by
    rw [← hpoly.2.2]
    exact (jn_radius_well_defined_proved degree hdegree poly hpoly.1).2.2.2
  have hopenmap : IsOpenMap poly.eval := (poly.isOpenQuotientMap_eval hdegree_ne).isOpenMap
  let interiorMap : OpenPartialHomeomorph ℂ ℂ := OpenPartialHomeomorph.ofContinuousOpen
    (hone.2.1.2.toPartialEquiv poly.eval (lemniscateComponent poly 1))
    poly.continuous.continuousOn hopenmap (lemniscate_open poly 1)
  by_contra hnone
  push Not at hnone
  have hsheets : ∀ point ∈ closure (lemniscateComponent poly 1),
      ∃ equiv : OpenPartialHomeomorph ℂ ℂ,
        (equiv : ℂ → ℂ) = poly.eval ∧ point ∈ equiv.source := by
    intro point hpoint
    by_cases hinterior : point ∈ lemniscateComponent poly 1
    · exact ⟨interiorMap, rfl, hinterior⟩
    · have hfrontier : point ∈ frontier (lemniscateComponent poly 1) :=
        ⟨hpoint, by simpa only [(lemniscate_open poly 1).interior_eq] using hinterior⟩
      have hderivative : poly.derivative.eval point ≠ 0 := hnone point hfrontier
      have hstrict := (poly.hasStrictDerivAt point).hasStrictFDerivAt_equiv hderivative
      exact ⟨hstrict.toOpenPartialHomeomorph poly.eval, rfl,
        hstrict.mem_toOpenPartialHomeomorph_source⟩
  obtain ⟨height, hheight, hlarge⟩ := larger_radius_of_local_sheets poly hdegree_ne hpoly.1.2.1 hone.2 hsheets
  have hbound := le_csSup (univalentRadii_bddAbove degree hdegree poly hpoly.1) hheight
  change height ≤ maxUnivalentRadius poly at hbound
  rw [hpoly.2.2] at hbound
  linarith

end SmaleRate.Proofs

#check SmaleRate.Proofs.closure_injective_of_local_sheets
#print axioms SmaleRate.Proofs.local_sheet_lens_subset
#print axioms SmaleRate.Proofs.closure_injective_of_local_sheets
#check SmaleRate.Proofs.jatar_ng_boundary_critical_exists_proved
#print axioms SmaleRate.Proofs.larger_radius_of_local_sheets
#print axioms SmaleRate.Proofs.jatar_ng_boundary_critical_exists_proved
