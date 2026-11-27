/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1000; no trusted numerical premise.
theorem cover8_leaf1000_exp_radius : (998003065362868493/1000000000000000000 : ℝ) ≤ Real.exp ((-67073/4194304 : ℝ)/8) ∧ Real.exp ((-67073/4194304 : ℝ)/8) ≤ (499001532681434247/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67073/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1000_exp_lower : (920113469390913773/1000000000000000000 : ℝ) ≤ Real.exp ((-666066241999/1000000000000 : ℝ)/8) ∧ Real.exp ((-666066241999/1000000000000 : ℝ)/8) ≤ (460056734695456887/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666066241999/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1000_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (5137254799/2500000000 : ℝ) ≤ 4*Real.exp (131/1024 : ℝ)*Real.exp (-mu (radius 8 (67073/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (5137254799/2500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67073/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1000_exp_radius
  have hrNumeric : (984135735013/1000000000000 : ℝ) ≤ Real.exp (-67073/4194304 : ℝ) ∧ Real.exp (-67073/4194304 : ℝ) ≤ (492067867507/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984135735013/1000000000000 : ℝ) ≤ (radius 8 (67073/524288 : ℝ)) ∧ (radius 8 (67073/524288 : ℝ)) ≤ (492067867507/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67073/524288 : ℝ)) (984135735013/1000000000000 : ℝ) (492067867507/500000000000 : ℝ) (177417178053/1000000000000 : ℝ) (8870858903/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67073/524288 : ℝ)) (984135735013/1000000000000 : ℝ) (492067867507/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67073/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984135735013/1000000000000 : ℝ) (492067867507/500000000000 : ℝ) (496033933753/500000000000 : ℝ) (992067867507/1000000000000 : ℝ) (992036156101/1000000000000 : ℝ) (992036156103/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67073/524288 : ℝ)) 1 (496033933753/500000000000 : ℝ) (992067867507/1000000000000 : ℝ) (992036156101/1000000000000 : ℝ) (992036156103/1000000000000 : ℝ) (992052011803/1000000000000 : ℝ) (198410402361/200000000000 : ℝ) (248013002919/250000000000 : ℝ) (992052011679/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67073/524288 : ℝ)) 2 (992052011803/1000000000000 : ℝ) (198410402361/200000000000 : ℝ) (248013002919/250000000000 : ℝ) (992052011679/1000000000000 : ℝ) (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ) (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67073/524288 : ℝ)) 3 (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ) (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ) (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ) (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67073/524288 : ℝ)) 4 (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ) (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ) (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ) (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67073/524288 : ℝ)) 5 (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ) (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ) (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ) (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67073/524288 : ℝ)) 6 (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ) (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ) (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ) (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67073/524288 : ℝ)) 7 (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ) (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ) (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ) (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67073/524288 : ℝ))) (177417178053/1000000000000 : ℝ) (8870858903/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67073/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177417178053/1000000000000 : ℝ) (8870858903/50000000000 : ℝ) (294354294513/500000000000 : ℝ) (58870858903/100000000000 : ℝ) (210604592811/500000000000 : ℝ) (13162787051/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67073/524288 : ℝ))) 1 (294354294513/500000000000 : ℝ) (58870858903/100000000000 : ℝ) (210604592811/500000000000 : ℝ) (13162787051/31250000000 : ℝ) (126239721831/250000000000 : ℝ) (504958887331/1000000000000 : ℝ) (497965325451/1000000000000 : ℝ) (24898266273/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67073/524288 : ℝ))) 2 (126239721831/250000000000 : ℝ) (504958887331/1000000000000 : ℝ) (497965325451/1000000000000 : ℝ) (24898266273/50000000000 : ℝ) (501462106387/1000000000000 : ℝ) (125365526599/250000000000 : ℝ) (501449914413/1000000000000 : ℝ) (250724957211/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67073/524288 : ℝ))) 3 (501462106387/1000000000000 : ℝ) (125365526599/250000000000 : ℝ) (501449914413/1000000000000 : ℝ) (250724957211/500000000000 : ℝ) (626820013/1250000000 : ℝ) (501456010409/1000000000000 : ℝ) (250728005181/500000000000 : ℝ) (125364002593/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67073/524288 : ℝ))) 4 (626820013/1250000000 : ℝ) (501456010409/1000000000000 : ℝ) (250728005181/500000000000 : ℝ) (125364002593/250000000000 : ℝ) (501456010381/1000000000000 : ℝ) (501456010391/1000000000000 : ℝ) (25072800519/50000000000 : ℝ) (501456010391/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67073/524288 : ℝ))) 5 (501456010381/1000000000000 : ℝ) (501456010391/1000000000000 : ℝ) (25072800519/50000000000 : ℝ) (501456010391/1000000000000 : ℝ) (25072800519/50000000000 : ℝ) (501456010391/1000000000000 : ℝ) (25072800519/50000000000 : ℝ) (501456010391/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67073/524288 : ℝ))) 6 (25072800519/50000000000 : ℝ) (501456010391/1000000000000 : ℝ) (25072800519/50000000000 : ℝ) (501456010391/1000000000000 : ℝ) (25072800519/50000000000 : ℝ) (501456010391/1000000000000 : ℝ) (25072800519/50000000000 : ℝ) (501456010391/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67073/524288 : ℝ))) 7 (25072800519/50000000000 : ℝ) (501456010391/1000000000000 : ℝ) (25072800519/50000000000 : ℝ) (501456010391/1000000000000 : ℝ) (25072800519/50000000000 : ℝ) (501456010391/1000000000000 : ℝ) (25072800519/50000000000 : ℝ) (501456010391/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67073/524288 : ℝ)) hmem 8 (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ) (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67073/524288 : ℝ))) hcmem 8 (25072800519/50000000000 : ℝ) (501456010391/1000000000000 : ℝ) (25072800519/50000000000 : ℝ) (501456010391/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67073/524288 : ℝ)) (992052011739/1000000000000 : ℝ) (496026005871/500000000000 : ℝ) (25072800519/50000000000 : ℝ) (501456010391/1000000000000 : ℝ) (396997964739/500000000000 : ℝ) (793995929499/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1000_exp_lower
  have heNumeric : (5137254799/2500000000 : ℝ)/4 ≤ Real.exp (-666066241999/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (5137254799/2500000000 : ℝ)/4 ≤ Real.exp ((131/1024 : ℝ)-(793995929499/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (131/1024 : ℝ) (67073/524288 : ℝ) (793995929499/1000000000000 : ℝ) (5137254799/2500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1001; no trusted numerical premise.
theorem cover8_leaf1001_exp_radius : (998003035620059839/1000000000000000000 : ℝ) ≤ Real.exp ((-33537/2097152 : ℝ)/8) ∧ Real.exp ((-33537/2097152 : ℝ)/8) ≤ (3118759486312687/3125000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33537/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1001_exp_lower : (184022693940604007/200000000000000000 : ℝ) ≤ Real.exp ((-85256478628527/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256478628527/128000000000000 : ℝ)/8) ≤ (230028367425755009/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256478628527/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1001_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862740647/125000000000 : ℝ) ≤ 4*Real.exp (67073/524288 : ℝ)*Real.exp (-mu (radius 8 (33537/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256862740647/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33537/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1001_exp_radius
  have hrNumeric : (984135500377/1000000000000 : ℝ) ≤ Real.exp (-33537/2097152 : ℝ) ∧ Real.exp (-33537/2097152 : ℝ) ≤ (492067750189/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984135500377/1000000000000 : ℝ) ≤ (radius 8 (33537/262144 : ℝ)) ∧ (radius 8 (33537/262144 : ℝ)) ≤ (492067750189/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33537/262144 : ℝ)) (984135500377/1000000000000 : ℝ) (492067750189/500000000000 : ℝ) (177418479577/1000000000000 : ℝ) (5544327487/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33537/262144 : ℝ)) (984135500377/1000000000000 : ℝ) (492067750189/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33537/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984135500377/1000000000000 : ℝ) (492067750189/500000000000 : ℝ) (248016937547/250000000000 : ℝ) (992067750189/1000000000000 : ℝ) (992036037841/1000000000000 : ℝ) (992036037843/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33537/262144 : ℝ)) 1 (248016937547/250000000000 : ℝ) (992067750189/1000000000000 : ℝ) (992036037841/1000000000000 : ℝ) (992036037843/1000000000000 : ℝ) (496025947007/500000000000 : ℝ) (3875202711/3906250000 : ℝ) (992051893887/1000000000000 : ℝ) (99205189389/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33537/262144 : ℝ)) 2 (496025947007/500000000000 : ℝ) (3875202711/3906250000 : ℝ) (992051893887/1000000000000 : ℝ) (99205189389/100000000000 : ℝ) (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ) (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33537/262144 : ℝ)) 3 (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ) (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ) (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ) (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33537/262144 : ℝ)) 4 (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ) (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ) (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ) (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33537/262144 : ℝ)) 5 (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ) (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ) (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ) (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33537/262144 : ℝ)) 6 (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ) (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ) (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ) (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33537/262144 : ℝ)) 7 (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ) (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ) (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ) (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33537/262144 : ℝ))) (177418479577/1000000000000 : ℝ) (5544327487/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33537/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177418479577/1000000000000 : ℝ) (5544327487/31250000000 : ℝ) (147177309947/250000000000 : ℝ) (36794327487/62500000000 : ℝ) (84242146121/200000000000 : ℝ) (210605365307/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33537/262144 : ℝ))) 1 (147177309947/250000000000 : ℝ) (36794327487/62500000000 : ℝ) (84242146121/200000000000 : ℝ) (210605365307/500000000000 : ℝ) (126239996299/250000000000 : ℝ) (504959985203/1000000000000 : ℝ) (497966513939/1000000000000 : ℝ) (497966513947/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33537/262144 : ℝ))) 2 (126239996299/250000000000 : ℝ) (504959985203/1000000000000 : ℝ) (497966513939/1000000000000 : ℝ) (497966513947/1000000000000 : ℝ) (501463249567/1000000000000 : ℝ) (20058529983/40000000000 : ℝ) (501451057937/1000000000000 : ℝ) (250725528973/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33537/262144 : ℝ))) 3 (501463249567/1000000000000 : ℝ) (20058529983/40000000000 : ℝ) (501451057937/1000000000000 : ℝ) (250725528973/500000000000 : ℝ) (62682144219/125000000000 : ℝ) (501457153761/1000000000000 : ℝ) (250728576857/500000000000 : ℝ) (125364288431/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33537/262144 : ℝ))) 4 (62682144219/125000000000 : ℝ) (501457153761/1000000000000 : ℝ) (250728576857/500000000000 : ℝ) (125364288431/250000000000 : ℝ) (501457153733/1000000000000 : ℝ) (501457153743/1000000000000 : ℝ) (125364288433/250000000000 : ℝ) (501457153743/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33537/262144 : ℝ))) 5 (501457153733/1000000000000 : ℝ) (501457153743/1000000000000 : ℝ) (125364288433/250000000000 : ℝ) (501457153743/1000000000000 : ℝ) (125364288433/250000000000 : ℝ) (501457153743/1000000000000 : ℝ) (125364288433/250000000000 : ℝ) (501457153743/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33537/262144 : ℝ))) 6 (125364288433/250000000000 : ℝ) (501457153743/1000000000000 : ℝ) (125364288433/250000000000 : ℝ) (501457153743/1000000000000 : ℝ) (125364288433/250000000000 : ℝ) (501457153743/1000000000000 : ℝ) (125364288433/250000000000 : ℝ) (501457153743/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33537/262144 : ℝ))) 7 (125364288433/250000000000 : ℝ) (501457153743/1000000000000 : ℝ) (125364288433/250000000000 : ℝ) (501457153743/1000000000000 : ℝ) (125364288433/250000000000 : ℝ) (501457153743/1000000000000 : ℝ) (125364288433/250000000000 : ℝ) (501457153743/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33537/262144 : ℝ)) hmem 8 (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ) (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33537/262144 : ℝ))) hcmem 8 (125364288433/250000000000 : ℝ) (501457153743/1000000000000 : ℝ) (125364288433/250000000000 : ℝ) (501457153743/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33537/262144 : ℝ)) (19841037879/20000000000 : ℝ) (992051893953/1000000000000 : ℝ) (125364288433/250000000000 : ℝ) (501457153743/1000000000000 : ℝ) (793997834113/1000000000000 : ℝ) (396998917067/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1001_exp_lower
  have heNumeric : (256862740647/125000000000 : ℝ)/4 ≤ Real.exp (-85256478628527/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862740647/125000000000 : ℝ)/4 ≤ Real.exp ((67073/524288 : ℝ)-(396998917067/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67073/524288 : ℝ) (33537/262144 : ℝ) (396998917067/500000000000 : ℝ) (256862740647/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1002; no trusted numerical premise.
theorem cover8_leaf1002_exp_radius : (99800300587725207/100000000000000000 : ℝ) ≤ Real.exp ((-67075/4194304 : ℝ)/8) ∧ Real.exp ((-67075/4194304 : ℝ)/8) ≤ (998003005877252071/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67075/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1002_exp_lower : (57507091876081973/62500000000000000 : ℝ) ≤ Real.exp ((-68205182623/102400000000 : ℝ)/8) ∧ Real.exp ((-68205182623/102400000000 : ℝ)/8) ≤ (920113470017311569/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-68205182623/102400000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1002_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862741349/125000000000 : ℝ) ≤ 4*Real.exp (33537/262144 : ℝ)*Real.exp (-mu (radius 8 (67075/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862741349/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67075/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1002_exp_radius
  have hrNumeric : (984135265741/1000000000000 : ℝ) ≤ Real.exp (-67075/4194304 : ℝ) ∧ Real.exp (-67075/4194304 : ℝ) ≤ (492067632871/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984135265741/1000000000000 : ℝ) ≤ (radius 8 (67075/524288 : ℝ)) ∧ (radius 8 (67075/524288 : ℝ)) ≤ (492067632871/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67075/524288 : ℝ)) (984135265741/1000000000000 : ℝ) (492067632871/500000000000 : ℝ) (44354945273/250000000000 : ℝ) (177419781099/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67075/524288 : ℝ)) (984135265741/1000000000000 : ℝ) (492067632871/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67075/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984135265741/1000000000000 : ℝ) (492067632871/500000000000 : ℝ) (99206763287/100000000000 : ℝ) (992067632871/1000000000000 : ℝ) (496017959791/500000000000 : ℝ) (992035919583/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67075/524288 : ℝ)) 1 (99206763287/100000000000 : ℝ) (992067632871/1000000000000 : ℝ) (496017959791/500000000000 : ℝ) (992035919583/1000000000000 : ℝ) (496025888113/500000000000 : ℝ) (992051776227/1000000000000 : ℝ) (992051776099/1000000000000 : ℝ) (992051776101/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67075/524288 : ℝ)) 2 (496025888113/500000000000 : ℝ) (992051776227/1000000000000 : ℝ) (992051776099/1000000000000 : ℝ) (992051776101/1000000000000 : ℝ) (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ) (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67075/524288 : ℝ)) 3 (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ) (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ) (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ) (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67075/524288 : ℝ)) 4 (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ) (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ) (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ) (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67075/524288 : ℝ)) 5 (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ) (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ) (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ) (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67075/524288 : ℝ)) 6 (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ) (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ) (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ) (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67075/524288 : ℝ)) 7 (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ) (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ) (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ) (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67075/524288 : ℝ))) (44354945273/250000000000 : ℝ) (177419781099/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67075/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44354945273/250000000000 : ℝ) (177419781099/1000000000000 : ℝ) (294354945273/500000000000 : ℝ) (11774197811/20000000000 : ℝ) (421212275571/1000000000000 : ℝ) (21060613779/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67075/524288 : ℝ))) 1 (294354945273/500000000000 : ℝ) (11774197811/20000000000 : ℝ) (421212275571/1000000000000 : ℝ) (21060613779/50000000000 : ℝ) (252480541529/500000000000 : ℝ) (100992216613/200000000000 : ℝ) (248983851207/500000000000 : ℝ) (248983851211/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67075/524288 : ℝ))) 2 (252480541529/500000000000 : ℝ) (100992216613/200000000000 : ℝ) (248983851207/500000000000 : ℝ) (248983851211/500000000000 : ℝ) (15670762273/31250000000 : ℝ) (62683049093/125000000000 : ℝ) (501452201449/1000000000000 : ℝ) (250726100729/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67075/524288 : ℝ))) 3 (15670762273/31250000000 : ℝ) (62683049093/125000000000 : ℝ) (501452201449/1000000000000 : ℝ) (250726100729/500000000000 : ℝ) (125364574273/250000000000 : ℝ) (501458297101/1000000000000 : ℝ) (100291659411/200000000000 : ℝ) (62682287133/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67075/524288 : ℝ))) 4 (125364574273/250000000000 : ℝ) (501458297101/1000000000000 : ℝ) (100291659411/200000000000 : ℝ) (62682287133/125000000000 : ℝ) (501458297073/1000000000000 : ℝ) (501458297083/1000000000000 : ℝ) (501458297073/1000000000000 : ℝ) (501458297083/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67075/524288 : ℝ))) 5 (501458297073/1000000000000 : ℝ) (501458297083/1000000000000 : ℝ) (501458297073/1000000000000 : ℝ) (501458297083/1000000000000 : ℝ) (501458297073/1000000000000 : ℝ) (501458297083/1000000000000 : ℝ) (501458297073/1000000000000 : ℝ) (501458297083/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67075/524288 : ℝ))) 6 (501458297073/1000000000000 : ℝ) (501458297083/1000000000000 : ℝ) (501458297073/1000000000000 : ℝ) (501458297083/1000000000000 : ℝ) (501458297073/1000000000000 : ℝ) (501458297083/1000000000000 : ℝ) (501458297073/1000000000000 : ℝ) (501458297083/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67075/524288 : ℝ))) 7 (501458297073/1000000000000 : ℝ) (501458297083/1000000000000 : ℝ) (501458297073/1000000000000 : ℝ) (501458297083/1000000000000 : ℝ) (501458297073/1000000000000 : ℝ) (501458297083/1000000000000 : ℝ) (501458297073/1000000000000 : ℝ) (501458297083/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67075/524288 : ℝ)) hmem 8 (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ) (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67075/524288 : ℝ))) hcmem 8 (501458297073/1000000000000 : ℝ) (501458297083/1000000000000 : ℝ) (501458297073/1000000000000 : ℝ) (501458297083/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67075/524288 : ℝ)) (496025888081/500000000000 : ℝ) (248012944041/250000000000 : ℝ) (501458297073/1000000000000 : ℝ) (501458297083/1000000000000 : ℝ) (198499934683/250000000000 : ℝ) (635199791/800000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1002_exp_lower
  have heNumeric : (256862741349/125000000000 : ℝ)/4 ≤ Real.exp (-68205182623/102400000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862741349/125000000000 : ℝ)/4 ≤ Real.exp ((33537/262144 : ℝ)-(635199791/800000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33537/262144 : ℝ) (67075/524288 : ℝ) (635199791/800000000 : ℝ) (256862741349/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1003; no trusted numerical premise.
theorem cover8_leaf1003_exp_radius : (249500744033611297/250000000000000000 : ℝ) ≤ Real.exp ((-16769/1048576 : ℝ)/8) ∧ Real.exp ((-16769/1048576 : ℝ)/8) ≤ (998002976134445189/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16769/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1003_exp_lower : (92011347033378837/100000000000000000 : ℝ) ≤ Real.exp ((-85256477926541/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256477926541/128000000000000 : ℝ)/8) ≤ (920113470333788371/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256477926541/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1003_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450968223/500000000000 : ℝ) ≤ 4*Real.exp (67075/524288 : ℝ)*Real.exp (-mu (radius 8 (16769/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450968223/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16769/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1003_exp_radius
  have hrNumeric : (196827006221/200000000000 : ℝ) ≤ Real.exp (-16769/1048576 : ℝ) ∧ Real.exp (-16769/1048576 : ℝ) ≤ (492067515553/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196827006221/200000000000 : ℝ) ≤ (radius 8 (16769/131072 : ℝ)) ∧ (radius 8 (16769/131072 : ℝ)) ≤ (492067515553/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16769/131072 : ℝ)) (196827006221/200000000000 : ℝ) (492067515553/500000000000 : ℝ) (177421082597/1000000000000 : ℝ) (177421082603/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16769/131072 : ℝ)) (196827006221/200000000000 : ℝ) (492067515553/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16769/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196827006221/200000000000 : ℝ) (492067515553/500000000000 : ℝ) (31002109861/31250000000 : ℝ) (992067515553/1000000000000 : ℝ) (496017900661/500000000000 : ℝ) (992035801323/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16769/131072 : ℝ)) 1 (31002109861/31250000000 : ℝ) (992067515553/1000000000000 : ℝ) (496017900661/500000000000 : ℝ) (992035801323/1000000000000 : ℝ) (992051658437/1000000000000 : ℝ) (496025829219/500000000000 : ℝ) (99205165831/100000000000 : ℝ) (124006457289/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16769/131072 : ℝ)) 2 (992051658437/1000000000000 : ℝ) (496025829219/500000000000 : ℝ) (99205165831/100000000000 : ℝ) (124006457289/125000000000 : ℝ) (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ) (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16769/131072 : ℝ)) 3 (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ) (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ) (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ) (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16769/131072 : ℝ)) 4 (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ) (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ) (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ) (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16769/131072 : ℝ)) 5 (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ) (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ) (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ) (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16769/131072 : ℝ)) 6 (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ) (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ) (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ) (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16769/131072 : ℝ)) 7 (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ) (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ) (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ) (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16769/131072 : ℝ))) (177421082597/1000000000000 : ℝ) (177421082603/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16769/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177421082597/1000000000000 : ℝ) (177421082603/1000000000000 : ℝ) (294355270649/500000000000 : ℝ) (294355270651/500000000000 : ℝ) (421213820519/1000000000000 : ℝ) (26325863783/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16769/131072 : ℝ))) 1 (294355270649/500000000000 : ℝ) (294355270651/500000000000 : ℝ) (421213820519/1000000000000 : ℝ) (26325863783/62500000000 : ℝ) (126240545227/250000000000 : ℝ) (100992436183/200000000000 : ℝ) (3983751127/8000000000 : ℝ) (497968890883/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16769/131072 : ℝ))) 2 (126240545227/250000000000 : ℝ) (100992436183/200000000000 : ℝ) (3983751127/8000000000 : ℝ) (497968890883/1000000000000 : ℝ) (501465535891/1000000000000 : ℝ) (501465535899/1000000000000 : ℝ) (501453344949/1000000000000 : ℝ) (501453344957/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16769/131072 : ℝ))) 3 (501465535891/1000000000000 : ℝ) (501465535899/1000000000000 : ℝ) (501453344949/1000000000000 : ℝ) (501453344957/1000000000000 : ℝ) (25072972021/50000000000 : ℝ) (125364860107/250000000000 : ℝ) (250729720191/500000000000 : ℝ) (501459440391/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16769/131072 : ℝ))) 4 (25072972021/50000000000 : ℝ) (125364860107/250000000000 : ℝ) (250729720191/500000000000 : ℝ) (501459440391/1000000000000 : ℝ) (501459440401/1000000000000 : ℝ) (50145944041/100000000000 : ℝ) (1253648601/2500000000 : ℝ) (50145944041/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16769/131072 : ℝ))) 5 (501459440401/1000000000000 : ℝ) (50145944041/100000000000 : ℝ) (1253648601/2500000000 : ℝ) (50145944041/100000000000 : ℝ) (1253648601/2500000000 : ℝ) (50145944041/100000000000 : ℝ) (1253648601/2500000000 : ℝ) (50145944041/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16769/131072 : ℝ))) 6 (1253648601/2500000000 : ℝ) (50145944041/100000000000 : ℝ) (1253648601/2500000000 : ℝ) (50145944041/100000000000 : ℝ) (1253648601/2500000000 : ℝ) (50145944041/100000000000 : ℝ) (1253648601/2500000000 : ℝ) (50145944041/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16769/131072 : ℝ))) 7 (1253648601/2500000000 : ℝ) (50145944041/100000000000 : ℝ) (1253648601/2500000000 : ℝ) (50145944041/100000000000 : ℝ) (1253648601/2500000000 : ℝ) (50145944041/100000000000 : ℝ) (1253648601/2500000000 : ℝ) (50145944041/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16769/131072 : ℝ)) hmem 8 (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ) (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16769/131072 : ℝ))) hcmem 8 (1253648601/2500000000 : ℝ) (50145944041/100000000000 : ℝ) (1253648601/2500000000 : ℝ) (50145944041/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16769/131072 : ℝ)) (992051658373/1000000000000 : ℝ) (7936413267/8000000000 : ℝ) (1253648601/2500000000 : ℝ) (50145944041/100000000000 : ℝ) (12406275677/15625000000 : ℝ) (794001643347/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1003_exp_lower
  have heNumeric : (1027450968223/500000000000 : ℝ)/4 ≤ Real.exp (-85256477926541/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450968223/500000000000 : ℝ)/4 ≤ Real.exp ((67075/524288 : ℝ)-(794001643347/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67075/524288 : ℝ) (16769/131072 : ℝ) (794001643347/1000000000000 : ℝ) (1027450968223/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1004; no trusted numerical premise.
theorem cover8_leaf1004_exp_radius : (998002946391639193/1000000000000000000 : ℝ) ≤ Real.exp ((-67077/4194304 : ℝ)/8) ∧ Real.exp ((-67077/4194304 : ℝ)/8) ≤ (499001473195819597/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67077/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1004_exp_lower : (920113470652220413/1000000000000000000 : ℝ) ≤ Real.exp ((-21314119393039/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314119393039/32000000000000 : ℝ)/8) ≤ (460056735326110207/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314119393039/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1004_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980388427/200000000000 : ℝ) ≤ 4*Real.exp (16769/131072 : ℝ)*Real.exp (-mu (radius 8 (67077/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980388427/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67077/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1004_exp_radius
  have hrNumeric : (984134796469/1000000000000 : ℝ) ≤ Real.exp (-67077/4194304 : ℝ) ∧ Real.exp (-67077/4194304 : ℝ) ≤ (98413479647/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984134796469/1000000000000 : ℝ) ≤ (radius 8 (67077/524288 : ℝ)) ∧ (radius 8 (67077/524288 : ℝ)) ≤ (98413479647/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67077/524288 : ℝ)) (984134796469/1000000000000 : ℝ) (98413479647/100000000000 : ℝ) (44355596023/250000000000 : ℝ) (88711192049/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67077/524288 : ℝ)) (984134796469/1000000000000 : ℝ) (98413479647/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67077/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984134796469/1000000000000 : ℝ) (98413479647/100000000000 : ℝ) (496033699117/500000000000 : ℝ) (198413479647/200000000000 : ℝ) (496017841531/500000000000 : ℝ) (992035683063/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67077/524288 : ℝ)) 1 (496033699117/500000000000 : ℝ) (198413479647/200000000000 : ℝ) (496017841531/500000000000 : ℝ) (992035683063/1000000000000 : ℝ) (124006442581/125000000000 : ℝ) (992051540649/1000000000000 : ℝ) (992051540521/1000000000000 : ℝ) (992051540523/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67077/524288 : ℝ)) 2 (124006442581/125000000000 : ℝ) (992051540649/1000000000000 : ℝ) (992051540521/1000000000000 : ℝ) (992051540523/1000000000000 : ℝ) (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ) (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67077/524288 : ℝ)) 3 (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ) (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ) (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ) (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67077/524288 : ℝ)) 4 (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ) (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ) (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ) (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67077/524288 : ℝ)) 5 (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ) (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ) (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ) (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67077/524288 : ℝ)) 6 (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ) (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ) (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ) (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67077/524288 : ℝ)) 7 (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ) (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ) (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ) (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67077/524288 : ℝ))) (44355596023/250000000000 : ℝ) (88711192049/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67077/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44355596023/250000000000 : ℝ) (88711192049/500000000000 : ℝ) (294355596023/500000000000 : ℝ) (588711192049/1000000000000 : ℝ) (8424307309/20000000000 : ℝ) (421215365459/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67077/524288 : ℝ))) 1 (294355596023/500000000000 : ℝ) (588711192049/1000000000000 : ℝ) (8424307309/20000000000 : ℝ) (421215365459/1000000000000 : ℝ) (126240819687/250000000000 : ℝ) (252481639377/500000000000 : ℝ) (124492519831/250000000000 : ℝ) (497970079331/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67077/524288 : ℝ))) 2 (126240819687/250000000000 : ℝ) (252481639377/500000000000 : ℝ) (124492519831/250000000000 : ℝ) (497970079331/1000000000000 : ℝ) (125366669759/250000000000 : ℝ) (501466679043/1000000000000 : ℝ) (501454488437/1000000000000 : ℝ) (125363622111/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67077/524288 : ℝ))) 3 (125366669759/250000000000 : ℝ) (501466679043/1000000000000 : ℝ) (501454488437/1000000000000 : ℝ) (125363622111/250000000000 : ℝ) (62682572967/125000000000 : ℝ) (7835321621/15625000000 : ℝ) (501460583699/1000000000000 : ℝ) (501460583707/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67077/524288 : ℝ))) 4 (62682572967/125000000000 : ℝ) (7835321621/15625000000 : ℝ) (501460583699/1000000000000 : ℝ) (501460583707/1000000000000 : ℝ) (501460583717/1000000000000 : ℝ) (250730291863/500000000000 : ℝ) (501460583717/1000000000000 : ℝ) (250730291863/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67077/524288 : ℝ))) 5 (501460583717/1000000000000 : ℝ) (250730291863/500000000000 : ℝ) (501460583717/1000000000000 : ℝ) (250730291863/500000000000 : ℝ) (501460583717/1000000000000 : ℝ) (250730291863/500000000000 : ℝ) (501460583717/1000000000000 : ℝ) (250730291863/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67077/524288 : ℝ))) 6 (501460583717/1000000000000 : ℝ) (250730291863/500000000000 : ℝ) (501460583717/1000000000000 : ℝ) (250730291863/500000000000 : ℝ) (501460583717/1000000000000 : ℝ) (250730291863/500000000000 : ℝ) (501460583717/1000000000000 : ℝ) (250730291863/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67077/524288 : ℝ))) 7 (501460583717/1000000000000 : ℝ) (250730291863/500000000000 : ℝ) (501460583717/1000000000000 : ℝ) (250730291863/500000000000 : ℝ) (501460583717/1000000000000 : ℝ) (250730291863/500000000000 : ℝ) (501460583717/1000000000000 : ℝ) (250730291863/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67077/524288 : ℝ)) hmem 8 (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ) (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67077/524288 : ℝ))) hcmem 8 (501460583717/1000000000000 : ℝ) (250730291863/500000000000 : ℝ) (501460583717/1000000000000 : ℝ) (250730291863/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67077/524288 : ℝ)) (124006442573/125000000000 : ℝ) (496025770293/500000000000 : ℝ) (501460583717/1000000000000 : ℝ) (250730291863/500000000000 : ℝ) (79400354791/100000000000 : ℝ) (794003547927/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1004_exp_lower
  have heNumeric : (410980388427/200000000000 : ℝ)/4 ≤ Real.exp (-21314119393039/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980388427/200000000000 : ℝ)/4 ≤ Real.exp ((16769/131072 : ℝ)-(794003547927/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16769/131072 : ℝ) (67077/524288 : ℝ) (794003547927/1000000000000 : ℝ) (410980388427/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1005; no trusted numerical premise.
theorem cover8_leaf1005_exp_radius : (249500729162208521/250000000000000000 : ℝ) ≤ Real.exp ((-33539/2097152 : ℝ)/8) ∧ Real.exp ((-33539/2097152 : ℝ)/8) ≤ (199600583329766817/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33539/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1005_exp_lower : (460056735486533877/500000000000000000 : ℝ) ≤ Real.exp ((-85256477215083/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256477215083/128000000000000 : ℝ)/8) ≤ (184022694194613551/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256477215083/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1005_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725486967/250000000000 : ℝ) ≤ 4*Real.exp (67077/524288 : ℝ)*Real.exp (-mu (radius 8 (33539/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725486967/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33539/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1005_exp_radius
  have hrNumeric : (984134561833/1000000000000 : ℝ) ≤ Real.exp (-33539/2097152 : ℝ) ∧ Real.exp (-33539/2097152 : ℝ) ≤ (492067280917/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984134561833/1000000000000 : ℝ) ≤ (radius 8 (33539/262144 : ℝ)) ∧ (radius 8 (33539/262144 : ℝ)) ≤ (492067280917/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33539/262144 : ℝ)) (984134561833/1000000000000 : ℝ) (492067280917/500000000000 : ℝ) (177423685577/1000000000000 : ℝ) (177423685583/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33539/262144 : ℝ)) (984134561833/1000000000000 : ℝ) (492067280917/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33539/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984134561833/1000000000000 : ℝ) (492067280917/500000000000 : ℝ) (248016820229/250000000000 : ℝ) (992067280917/1000000000000 : ℝ) (496017782401/500000000000 : ℝ) (992035564803/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33539/262144 : ℝ)) 1 (248016820229/250000000000 : ℝ) (992067280917/1000000000000 : ℝ) (496017782401/500000000000 : ℝ) (992035564803/1000000000000 : ℝ) (992051422859/1000000000000 : ℝ) (49602571143/50000000000 : ℝ) (248012855683/250000000000 : ℝ) (496025711367/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33539/262144 : ℝ)) 2 (992051422859/1000000000000 : ℝ) (49602571143/50000000000 : ℝ) (248012855683/250000000000 : ℝ) (496025711367/500000000000 : ℝ) (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ) (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33539/262144 : ℝ)) 3 (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ) (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ) (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ) (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33539/262144 : ℝ)) 4 (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ) (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ) (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ) (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33539/262144 : ℝ)) 5 (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ) (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ) (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ) (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33539/262144 : ℝ)) 6 (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ) (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ) (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ) (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33539/262144 : ℝ)) 7 (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ) (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ) (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ) (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33539/262144 : ℝ))) (177423685577/1000000000000 : ℝ) (177423685583/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33539/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177423685577/1000000000000 : ℝ) (177423685583/1000000000000 : ℝ) (147177960697/250000000000 : ℝ) (73588980349/125000000000 : ℝ) (105304227591/250000000000 : ℝ) (105304227593/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33539/262144 : ℝ))) 1 (147177960697/250000000000 : ℝ) (73588980349/125000000000 : ℝ) (105304227591/250000000000 : ℝ) (105304227593/250000000000 : ℝ) (246564637/488281250 : ℝ) (252482188291/500000000000 : ℝ) (497971267759/1000000000000 : ℝ) (248985633883/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33539/262144 : ℝ))) 2 (246564637/488281250 : ℝ) (252482188291/500000000000 : ℝ) (497971267759/1000000000000 : ℝ) (248985633883/500000000000 : ℝ) (501467822167/1000000000000 : ℝ) (250733911087/500000000000 : ℝ) (62681953989/125000000000 : ℝ) (501455631919/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33539/262144 : ℝ))) 3 (501467822167/1000000000000 : ℝ) (250733911087/500000000000 : ℝ) (62681953989/125000000000 : ℝ) (501455631919/1000000000000 : ℝ) (501461727039/1000000000000 : ℝ) (501461727047/1000000000000 : ℝ) (250730863501/500000000000 : ℝ) (50146172701/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33539/262144 : ℝ))) 4 (501461727039/1000000000000 : ℝ) (501461727047/1000000000000 : ℝ) (250730863501/500000000000 : ℝ) (50146172701/100000000000 : ℝ) (25073086351/50000000000 : ℝ) (501461727029/1000000000000 : ℝ) (25073086351/50000000000 : ℝ) (501461727029/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33539/262144 : ℝ))) 5 (25073086351/50000000000 : ℝ) (501461727029/1000000000000 : ℝ) (25073086351/50000000000 : ℝ) (501461727029/1000000000000 : ℝ) (25073086351/50000000000 : ℝ) (501461727029/1000000000000 : ℝ) (25073086351/50000000000 : ℝ) (501461727029/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33539/262144 : ℝ))) 6 (25073086351/50000000000 : ℝ) (501461727029/1000000000000 : ℝ) (25073086351/50000000000 : ℝ) (501461727029/1000000000000 : ℝ) (25073086351/50000000000 : ℝ) (501461727029/1000000000000 : ℝ) (25073086351/50000000000 : ℝ) (501461727029/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33539/262144 : ℝ))) 7 (25073086351/50000000000 : ℝ) (501461727029/1000000000000 : ℝ) (25073086351/50000000000 : ℝ) (501461727029/1000000000000 : ℝ) (25073086351/50000000000 : ℝ) (501461727029/1000000000000 : ℝ) (25073086351/50000000000 : ℝ) (501461727029/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33539/262144 : ℝ)) hmem 8 (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ) (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33539/262144 : ℝ))) hcmem 8 (25073086351/50000000000 : ℝ) (501461727029/1000000000000 : ℝ) (25073086351/50000000000 : ℝ) (501461727029/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33539/262144 : ℝ)) (198410284559/200000000000 : ℝ) (992051422797/1000000000000 : ℝ) (25073086351/50000000000 : ℝ) (501461727029/1000000000000 : ℝ) (794005452469/1000000000000 : ℝ) (397002726243/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1005_exp_lower
  have heNumeric : (513725486967/250000000000 : ℝ)/4 ≤ Real.exp (-85256477215083/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725486967/250000000000 : ℝ)/4 ≤ Real.exp ((67077/524288 : ℝ)-(397002726243/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67077/524288 : ℝ) (33539/262144 : ℝ) (397002726243/500000000000 : ℝ) (513725486967/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1006; no trusted numerical premise.
theorem cover8_leaf1006_exp_radius : (998002886906029861/1000000000000000000 : ℝ) ≤ Real.exp ((-67079/4194304 : ℝ)/8) ∧ Real.exp ((-67079/4194304 : ℝ)/8) ≤ (499001443453014931/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67079/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1006_exp_lower : (460056735647877661/500000000000000000 : ℝ) ≤ Real.exp ((-42628238427981/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628238427981/64000000000000 : ℝ)/8) ≤ (920113471295755323/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628238427981/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1006_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901953633/1000000000000 : ℝ) ≤ 4*Real.exp (33539/262144 : ℝ)*Real.exp (-mu (radius 8 (67079/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901953633/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67079/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1006_exp_radius
  have hrNumeric : (984134327197/1000000000000 : ℝ) ≤ Real.exp (-67079/4194304 : ℝ) ∧ Real.exp (-67079/4194304 : ℝ) ≤ (492067163599/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984134327197/1000000000000 : ℝ) ≤ (radius 8 (67079/524288 : ℝ)) ∧ (radius 8 (67079/524288 : ℝ)) ≤ (492067163599/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67079/524288 : ℝ)) (984134327197/1000000000000 : ℝ) (492067163599/500000000000 : ℝ) (44356246763/250000000000 : ℝ) (88712493529/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67079/524288 : ℝ)) (984134327197/1000000000000 : ℝ) (492067163599/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67079/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984134327197/1000000000000 : ℝ) (492067163599/500000000000 : ℝ) (496033581799/500000000000 : ℝ) (992067163599/1000000000000 : ℝ) (496017723271/500000000000 : ℝ) (62002215409/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67079/524288 : ℝ)) 1 (496033581799/500000000000 : ℝ) (992067163599/1000000000000 : ℝ) (496017723271/500000000000 : ℝ) (62002215409/62500000000 : ℝ) (99205130507/100000000000 : ℝ) (62003206567/62500000000 : ℝ) (992051304943/1000000000000 : ℝ) (198410260989/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67079/524288 : ℝ)) 2 (99205130507/100000000000 : ℝ) (62003206567/62500000000 : ℝ) (992051304943/1000000000000 : ℝ) (198410260989/200000000000 : ℝ) (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ) (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67079/524288 : ℝ)) 3 (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ) (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ) (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ) (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67079/524288 : ℝ)) 4 (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ) (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ) (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ) (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67079/524288 : ℝ)) 5 (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ) (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ) (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ) (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67079/524288 : ℝ)) 6 (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ) (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ) (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ) (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67079/524288 : ℝ)) 7 (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ) (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ) (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ) (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67079/524288 : ℝ))) (44356246763/250000000000 : ℝ) (88712493529/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67079/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44356246763/250000000000 : ℝ) (88712493529/500000000000 : ℝ) (294356246763/500000000000 : ℝ) (588712493529/1000000000000 : ℝ) (21060922763/50000000000 : ℝ) (105304613817/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67079/524288 : ℝ))) 1 (294356246763/500000000000 : ℝ) (588712493529/1000000000000 : ℝ) (21060922763/50000000000 : ℝ) (105304613817/250000000000 : ℝ) (504965474393/1000000000000 : ℝ) (504965474399/1000000000000 : ℝ) (497972456181/1000000000000 : ℝ) (124493114047/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67079/524288 : ℝ))) 2 (504965474393/1000000000000 : ℝ) (504965474399/1000000000000 : ℝ) (497972456181/1000000000000 : ℝ) (124493114047/250000000000 : ℝ) (501468965287/1000000000000 : ℝ) (250734482647/500000000000 : ℝ) (4011654203/8000000000 : ℝ) (501456775383/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67079/524288 : ℝ))) 3 (501468965287/1000000000000 : ℝ) (250734482647/500000000000 : ℝ) (4011654203/8000000000 : ℝ) (501456775383/1000000000000 : ℝ) (501462870331/1000000000000 : ℝ) (501462870339/1000000000000 : ℝ) (501462870293/1000000000000 : ℝ) (250731435151/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67079/524288 : ℝ))) 4 (501462870331/1000000000000 : ℝ) (501462870339/1000000000000 : ℝ) (501462870293/1000000000000 : ℝ) (250731435151/500000000000 : ℝ) (62682858789/125000000000 : ℝ) (501462870321/1000000000000 : ℝ) (501462870311/1000000000000 : ℝ) (501462870321/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67079/524288 : ℝ))) 5 (62682858789/125000000000 : ℝ) (501462870321/1000000000000 : ℝ) (501462870311/1000000000000 : ℝ) (501462870321/1000000000000 : ℝ) (501462870311/1000000000000 : ℝ) (501462870321/1000000000000 : ℝ) (501462870311/1000000000000 : ℝ) (501462870321/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67079/524288 : ℝ))) 6 (501462870311/1000000000000 : ℝ) (501462870321/1000000000000 : ℝ) (501462870311/1000000000000 : ℝ) (501462870321/1000000000000 : ℝ) (501462870311/1000000000000 : ℝ) (501462870321/1000000000000 : ℝ) (501462870311/1000000000000 : ℝ) (501462870321/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67079/524288 : ℝ))) 7 (501462870311/1000000000000 : ℝ) (501462870321/1000000000000 : ℝ) (501462870311/1000000000000 : ℝ) (501462870321/1000000000000 : ℝ) (501462870311/1000000000000 : ℝ) (501462870321/1000000000000 : ℝ) (501462870311/1000000000000 : ℝ) (501462870321/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67079/524288 : ℝ)) hmem 8 (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ) (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67079/524288 : ℝ))) hcmem 8 (501462870311/1000000000000 : ℝ) (501462870321/1000000000000 : ℝ) (501462870311/1000000000000 : ℝ) (501462870321/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67079/524288 : ℝ)) (496025652503/500000000000 : ℝ) (992051305009/1000000000000 : ℝ) (501462870311/1000000000000 : ℝ) (501462870321/1000000000000 : ℝ) (79400735701/100000000000 : ℝ) (794007357029/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1006_exp_lower
  have heNumeric : (2054901953633/1000000000000 : ℝ)/4 ≤ Real.exp (-42628238427981/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901953633/1000000000000 : ℝ)/4 ≤ Real.exp ((33539/262144 : ℝ)-(794007357029/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33539/262144 : ℝ) (67079/524288 : ℝ) (794007357029/1000000000000 : ℝ) (2054901953633/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1007; no trusted numerical premise.
theorem cover8_leaf1007_exp_radius : (39920114286529061/40000000000000000 : ℝ) ≤ Real.exp ((-8385/524288 : ℝ)/8) ∧ Real.exp ((-8385/524288 : ℝ)/8) ≤ (499001428581613263/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8385/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1007_exp_lower : (920113471620858189/1000000000000000000 : ℝ) ≤ Real.exp ((-85256476494153/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256476494153/128000000000000 : ℝ)/8) ≤ (92011347162085819/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256476494153/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1007_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901959441/1000000000000 : ℝ) ≤ 4*Real.exp (67079/524288 : ℝ)*Real.exp (-mu (radius 8 (8385/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901959441/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8385/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1007_exp_radius
  have hrNumeric : (984134092561/1000000000000 : ℝ) ≤ Real.exp (-8385/524288 : ℝ) ∧ Real.exp (-8385/524288 : ℝ) ≤ (492067046281/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984134092561/1000000000000 : ℝ) ≤ (radius 8 (8385/65536 : ℝ)) ∧ (radius 8 (8385/65536 : ℝ)) ≤ (492067046281/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8385/65536 : ℝ)) (984134092561/1000000000000 : ℝ) (492067046281/500000000000 : ℝ) (177426288517/1000000000000 : ℝ) (44356572131/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8385/65536 : ℝ)) (984134092561/1000000000000 : ℝ) (492067046281/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8385/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984134092561/1000000000000 : ℝ) (492067046281/500000000000 : ℝ) (24801676157/25000000000 : ℝ) (992067046281/1000000000000 : ℝ) (496017664141/500000000000 : ℝ) (248008832071/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8385/65536 : ℝ)) 1 (24801676157/25000000000 : ℝ) (992067046281/1000000000000 : ℝ) (496017664141/500000000000 : ℝ) (248008832071/250000000000 : ℝ) (992051187281/1000000000000 : ℝ) (992051187283/1000000000000 : ℝ) (496025593577/500000000000 : ℝ) (248012796789/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8385/65536 : ℝ)) 2 (992051187281/1000000000000 : ℝ) (992051187283/1000000000000 : ℝ) (496025593577/500000000000 : ℝ) (248012796789/250000000000 : ℝ) (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ) (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8385/65536 : ℝ)) 3 (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ) (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ) (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ) (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8385/65536 : ℝ)) 4 (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ) (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ) (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ) (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8385/65536 : ℝ)) 5 (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ) (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ) (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ) (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8385/65536 : ℝ)) 6 (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ) (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ) (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ) (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8385/65536 : ℝ)) 7 (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ) (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ) (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ) (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8385/65536 : ℝ))) (177426288517/1000000000000 : ℝ) (44356572131/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8385/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177426288517/1000000000000 : ℝ) (44356572131/250000000000 : ℝ) (294356572129/500000000000 : ℝ) (294356572131/500000000000 : ℝ) (210610000069/500000000000 : ℝ) (105305000037/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8385/65536 : ℝ))) 1 (294356572129/500000000000 : ℝ) (294356572131/500000000000 : ℝ) (210610000069/500000000000 : ℝ) (105305000037/250000000000 : ℝ) (252483286099/500000000000 : ℝ) (100993314441/200000000000 : ℝ) (497973644589/1000000000000 : ℝ) (497973644597/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8385/65536 : ℝ))) 2 (252483286099/500000000000 : ℝ) (100993314441/200000000000 : ℝ) (497973644589/1000000000000 : ℝ) (497973644597/1000000000000 : ℝ) (501470108393/1000000000000 : ℝ) (501470108401/1000000000000 : ℝ) (20058316753/40000000000 : ℝ) (250728959417/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8385/65536 : ℝ))) 3 (501470108393/1000000000000 : ℝ) (501470108401/1000000000000 : ℝ) (20058316753/40000000000 : ℝ) (250728959417/500000000000 : ℝ) (501464013609/1000000000000 : ℝ) (250732006809/500000000000 : ℝ) (501464013571/1000000000000 : ℝ) (501464013581/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8385/65536 : ℝ))) 4 (501464013609/1000000000000 : ℝ) (250732006809/500000000000 : ℝ) (501464013571/1000000000000 : ℝ) (501464013581/1000000000000 : ℝ) (50146401359/100000000000 : ℝ) (626830017/1250000000 : ℝ) (501464013589/1000000000000 : ℝ) (626830017/1250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8385/65536 : ℝ))) 5 (50146401359/100000000000 : ℝ) (626830017/1250000000 : ℝ) (501464013589/1000000000000 : ℝ) (626830017/1250000000 : ℝ) (501464013589/1000000000000 : ℝ) (626830017/1250000000 : ℝ) (501464013589/1000000000000 : ℝ) (626830017/1250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8385/65536 : ℝ))) 6 (501464013589/1000000000000 : ℝ) (626830017/1250000000 : ℝ) (501464013589/1000000000000 : ℝ) (626830017/1250000000 : ℝ) (501464013589/1000000000000 : ℝ) (626830017/1250000000 : ℝ) (501464013589/1000000000000 : ℝ) (626830017/1250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8385/65536 : ℝ))) 7 (501464013589/1000000000000 : ℝ) (626830017/1250000000 : ℝ) (501464013589/1000000000000 : ℝ) (626830017/1250000000 : ℝ) (501464013589/1000000000000 : ℝ) (626830017/1250000000 : ℝ) (501464013589/1000000000000 : ℝ) (626830017/1250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8385/65536 : ℝ)) hmem 8 (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ) (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8385/65536 : ℝ))) hcmem 8 (501464013589/1000000000000 : ℝ) (626830017/1250000000 : ℝ) (501464013589/1000000000000 : ℝ) (626830017/1250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8385/65536 : ℝ)) (992051187217/1000000000000 : ℝ) (49602559361/50000000000 : ℝ) (501464013589/1000000000000 : ℝ) (626830017/1250000000 : ℝ) (79400926153/100000000000 : ℝ) (794009261551/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1007_exp_lower
  have heNumeric : (2054901959441/1000000000000 : ℝ)/4 ≤ Real.exp (-85256476494153/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901959441/1000000000000 : ℝ)/4 ≤ Real.exp ((67079/524288 : ℝ)-(794009261551/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67079/524288 : ℝ) (8385/65536 : ℝ) (794009261551/1000000000000 : ℝ) (2054901959441/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1008; no trusted numerical premise.
theorem cover8_leaf1008_exp_radius : (39920113096816963/40000000000000000 : ℝ) ≤ Real.exp ((-67081/4194304 : ℝ)/8) ∧ Real.exp ((-67081/4194304 : ℝ)/8) ≤ (249500706855106019/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67081/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1008_exp_lower : (92011347194803131/100000000000000000 : ℝ) ≤ Real.exp ((-2131411903251/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131411903251/3200000000000 : ℝ)/8) ≤ (920113471948031311/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131411903251/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1008_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901965287/1000000000000 : ℝ) ≤ 4*Real.exp (8385/65536 : ℝ)*Real.exp (-mu (radius 8 (67081/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901965287/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67081/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1008_exp_radius
  have hrNumeric : (39365354317/40000000000 : ℝ) ≤ Real.exp (-67081/4194304 : ℝ) ∧ Real.exp (-67081/4194304 : ℝ) ≤ (492066928963/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39365354317/40000000000 : ℝ) ≤ (radius 8 (67081/524288 : ℝ)) ∧ (radius 8 (67081/524288 : ℝ)) ≤ (492066928963/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67081/524288 : ℝ)) (39365354317/40000000000 : ℝ) (492066928963/500000000000 : ℝ) (177427589973/1000000000000 : ℝ) (177427589979/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67081/524288 : ℝ)) (39365354317/40000000000 : ℝ) (492066928963/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67081/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39365354317/40000000000 : ℝ) (492066928963/500000000000 : ℝ) (496033464481/500000000000 : ℝ) (992066928963/1000000000000 : ℝ) (496017605011/500000000000 : ℝ) (124004401253/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67081/524288 : ℝ)) 1 (496033464481/500000000000 : ℝ) (992066928963/1000000000000 : ℝ) (496017605011/500000000000 : ℝ) (124004401253/125000000000 : ℝ) (248012767373/250000000000 : ℝ) (496025534747/500000000000 : ℝ) (198410213873/200000000000 : ℝ) (992051069367/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67081/524288 : ℝ)) 2 (248012767373/250000000000 : ℝ) (496025534747/500000000000 : ℝ) (198410213873/200000000000 : ℝ) (992051069367/1000000000000 : ℝ) (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ) (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67081/524288 : ℝ)) 3 (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ) (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ) (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ) (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67081/524288 : ℝ)) 4 (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ) (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ) (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ) (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67081/524288 : ℝ)) 5 (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ) (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ) (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ) (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67081/524288 : ℝ)) 6 (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ) (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ) (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ) (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67081/524288 : ℝ)) 7 (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ) (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ) (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ) (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67081/524288 : ℝ))) (177427589973/1000000000000 : ℝ) (177427589979/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67081/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177427589973/1000000000000 : ℝ) (177427589979/1000000000000 : ℝ) (294356897493/500000000000 : ℝ) (58871379499/100000000000 : ℝ) (84244309/200000000 : ℝ) (421221545009/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67081/524288 : ℝ))) 1 (294356897493/500000000000 : ℝ) (58871379499/100000000000 : ℝ) (84244309/200000000 : ℝ) (421221545009/1000000000000 : ℝ) (504967669993/1000000000000 : ℝ) (50496767/100000000 : ℝ) (99594966597/200000000000 : ℝ) (497974832993/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67081/524288 : ℝ))) 2 (504967669993/1000000000000 : ℝ) (50496767/100000000 : ℝ) (99594966597/200000000000 : ℝ) (497974832993/1000000000000 : ℝ) (501471251489/1000000000000 : ℝ) (501471251497/1000000000000 : ℝ) (62682382783/125000000000 : ℝ) (501459062273/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67081/524288 : ℝ))) 3 (501471251489/1000000000000 : ℝ) (501471251497/1000000000000 : ℝ) (62682382783/125000000000 : ℝ) (501459062273/1000000000000 : ℝ) (125366289219/250000000000 : ℝ) (100293031377/200000000000 : ℝ) (501465156839/1000000000000 : ℝ) (31341572303/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67081/524288 : ℝ))) 4 (125366289219/250000000000 : ℝ) (100293031377/200000000000 : ℝ) (501465156839/1000000000000 : ℝ) (31341572303/62500000000 : ℝ) (501465156857/1000000000000 : ℝ) (501465156867/1000000000000 : ℝ) (501465156857/1000000000000 : ℝ) (501465156867/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67081/524288 : ℝ))) 5 (501465156857/1000000000000 : ℝ) (501465156867/1000000000000 : ℝ) (501465156857/1000000000000 : ℝ) (501465156867/1000000000000 : ℝ) (501465156857/1000000000000 : ℝ) (501465156867/1000000000000 : ℝ) (501465156857/1000000000000 : ℝ) (501465156867/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67081/524288 : ℝ))) 6 (501465156857/1000000000000 : ℝ) (501465156867/1000000000000 : ℝ) (501465156857/1000000000000 : ℝ) (501465156867/1000000000000 : ℝ) (501465156857/1000000000000 : ℝ) (501465156867/1000000000000 : ℝ) (501465156857/1000000000000 : ℝ) (501465156867/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67081/524288 : ℝ))) 7 (501465156857/1000000000000 : ℝ) (501465156867/1000000000000 : ℝ) (501465156857/1000000000000 : ℝ) (501465156867/1000000000000 : ℝ) (501465156857/1000000000000 : ℝ) (501465156867/1000000000000 : ℝ) (501465156857/1000000000000 : ℝ) (501465156867/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67081/524288 : ℝ)) hmem 8 (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ) (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67081/524288 : ℝ))) hcmem 8 (501465156857/1000000000000 : ℝ) (501465156867/1000000000000 : ℝ) (501465156857/1000000000000 : ℝ) (501465156867/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67081/524288 : ℝ)) (248012767357/250000000000 : ℝ) (992051069431/1000000000000 : ℝ) (501465156857/1000000000000 : ℝ) (501465156867/1000000000000 : ℝ) (198502791509/250000000000 : ℝ) (158802233211/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1008_exp_lower
  have heNumeric : (2054901965287/1000000000000 : ℝ)/4 ≤ Real.exp (-2131411903251/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901965287/1000000000000 : ℝ)/4 ≤ Real.exp ((8385/65536 : ℝ)-(158802233211/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8385/65536 : ℝ) (67081/524288 : ℝ) (158802233211/200000000000 : ℝ) (2054901965287/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1009; no trusted numerical premise.
theorem cover8_leaf1009_exp_radius : (62375174854851407/62500000000000000 : ℝ) ≤ Real.exp ((-33541/2097152 : ℝ)/8) ∧ Real.exp ((-33541/2097152 : ℝ)/8) ≤ (998002797677622513/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33541/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1009_exp_lower : (230028368069376179/250000000000000000 : ℝ) ≤ Real.exp ((-85256475763367/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256475763367/128000000000000 : ℝ)/8) ≤ (920113472277504717/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256475763367/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1009_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901971173/1000000000000 : ℝ) ≤ 4*Real.exp (67081/524288 : ℝ)*Real.exp (-mu (radius 8 (33541/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901971173/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33541/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1009_exp_radius
  have hrNumeric : (984133623289/1000000000000 : ℝ) ≤ Real.exp (-33541/2097152 : ℝ) ∧ Real.exp (-33541/2097152 : ℝ) ≤ (98413362329/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984133623289/1000000000000 : ℝ) ≤ (radius 8 (33541/262144 : ℝ)) ∧ (radius 8 (33541/262144 : ℝ)) ≤ (98413362329/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33541/262144 : ℝ)) (984133623289/1000000000000 : ℝ) (98413362329/100000000000 : ℝ) (88714445709/500000000000 : ℝ) (7097155657/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33541/262144 : ℝ)) (984133623289/1000000000000 : ℝ) (98413362329/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33541/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984133623289/1000000000000 : ℝ) (98413362329/100000000000 : ℝ) (248016702911/250000000000 : ℝ) (198413362329/200000000000 : ℝ) (496017545881/500000000000 : ℝ) (248008772941/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33541/262144 : ℝ)) 1 (248016702911/250000000000 : ℝ) (198413362329/200000000000 : ℝ) (496017545881/500000000000 : ℝ) (248008772941/250000000000 : ℝ) (992050951703/1000000000000 : ℝ) (198410190341/200000000000 : ℝ) (124006368947/125000000000 : ℝ) (496025475789/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33541/262144 : ℝ)) 2 (992050951703/1000000000000 : ℝ) (198410190341/200000000000 : ℝ) (124006368947/125000000000 : ℝ) (496025475789/500000000000 : ℝ) (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ) (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33541/262144 : ℝ)) 3 (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ) (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ) (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ) (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33541/262144 : ℝ)) 4 (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ) (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ) (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ) (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33541/262144 : ℝ)) 5 (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ) (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ) (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ) (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33541/262144 : ℝ)) 6 (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ) (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ) (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ) (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33541/262144 : ℝ)) 7 (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ) (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ) (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ) (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33541/262144 : ℝ))) (88714445709/500000000000 : ℝ) (7097155657/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33541/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88714445709/500000000000 : ℝ) (7097155657/40000000000 : ℝ) (588714445709/1000000000000 : ℝ) (588714445713/1000000000000 : ℝ) (105305772461/250000000000 : ℝ) (421223089853/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33541/262144 : ℝ))) 1 (588714445709/1000000000000 : ℝ) (588714445713/1000000000000 : ℝ) (105305772461/250000000000 : ℝ) (421223089853/1000000000000 : ℝ) (15780273993/31250000000 : ℝ) (504968767783/1000000000000 : ℝ) (497976021367/1000000000000 : ℝ) (3983808171/8000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33541/262144 : ℝ))) 2 (15780273993/31250000000 : ℝ) (504968767783/1000000000000 : ℝ) (497976021367/1000000000000 : ℝ) (3983808171/8000000000 : ℝ) (501472394571/1000000000000 : ℝ) (501472394579/1000000000000 : ℝ) (501460205691/1000000000000 : ℝ) (501460205699/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33541/262144 : ℝ))) 3 (501472394571/1000000000000 : ℝ) (501472394579/1000000000000 : ℝ) (501460205691/1000000000000 : ℝ) (501460205699/1000000000000 : ℝ) (501466300131/1000000000000 : ℝ) (501466300139/1000000000000 : ℝ) (501466300093/1000000000000 : ℝ) (250733150051/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33541/262144 : ℝ))) 4 (501466300131/1000000000000 : ℝ) (501466300139/1000000000000 : ℝ) (501466300093/1000000000000 : ℝ) (250733150051/500000000000 : ℝ) (31341643757/62500000000 : ℝ) (501466300121/1000000000000 : ℝ) (501466300111/1000000000000 : ℝ) (501466300121/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33541/262144 : ℝ))) 5 (31341643757/62500000000 : ℝ) (501466300121/1000000000000 : ℝ) (501466300111/1000000000000 : ℝ) (501466300121/1000000000000 : ℝ) (501466300111/1000000000000 : ℝ) (501466300121/1000000000000 : ℝ) (501466300111/1000000000000 : ℝ) (501466300121/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33541/262144 : ℝ))) 6 (501466300111/1000000000000 : ℝ) (501466300121/1000000000000 : ℝ) (501466300111/1000000000000 : ℝ) (501466300121/1000000000000 : ℝ) (501466300111/1000000000000 : ℝ) (501466300121/1000000000000 : ℝ) (501466300111/1000000000000 : ℝ) (501466300121/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33541/262144 : ℝ))) 7 (501466300111/1000000000000 : ℝ) (501466300121/1000000000000 : ℝ) (501466300111/1000000000000 : ℝ) (501466300121/1000000000000 : ℝ) (501466300111/1000000000000 : ℝ) (501466300121/1000000000000 : ℝ) (501466300111/1000000000000 : ℝ) (501466300121/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33541/262144 : ℝ)) hmem 8 (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ) (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33541/262144 : ℝ))) hcmem 8 (501466300111/1000000000000 : ℝ) (501466300121/1000000000000 : ℝ) (501466300111/1000000000000 : ℝ) (501466300121/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33541/262144 : ℝ)) (992050951639/1000000000000 : ℝ) (496025475821/500000000000 : ℝ) (501466300111/1000000000000 : ℝ) (501466300121/1000000000000 : ℝ) (19850326763/25000000000 : ℝ) (794013070539/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1009_exp_lower
  have heNumeric : (2054901971173/1000000000000 : ℝ)/4 ≤ Real.exp (-85256475763367/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901971173/1000000000000 : ℝ)/4 ≤ Real.exp ((67081/524288 : ℝ)-(794013070539/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67081/524288 : ℝ) (33541/262144 : ℝ) (794013070539/1000000000000 : ℝ) (2054901971173/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1010; no trusted numerical premise.
theorem cover8_leaf1010_exp_radius : (199600553586964367/200000000000000000 : ℝ) ≤ Real.exp ((-67083/4194304 : ℝ)/8) ∧ Real.exp ((-67083/4194304 : ℝ)/8) ≤ (249500691983705459/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67083/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1010_exp_lower : (230028368152204587/250000000000000000 : ℝ) ≤ Real.exp ((-42628237697323/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628237697323/64000000000000 : ℝ)/8) ≤ (920113472608818349/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628237697323/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1010_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901977093/1000000000000 : ℝ) ≤ 4*Real.exp (33541/262144 : ℝ)*Real.exp (-mu (radius 8 (67083/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901977093/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67083/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1010_exp_radius
  have hrNumeric : (984133388653/1000000000000 : ℝ) ≤ Real.exp (-67083/4194304 : ℝ) ∧ Real.exp (-67083/4194304 : ℝ) ≤ (492066694327/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984133388653/1000000000000 : ℝ) ≤ (radius 8 (67083/524288 : ℝ)) ∧ (radius 8 (67083/524288 : ℝ)) ≤ (492066694327/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67083/524288 : ℝ)) (984133388653/1000000000000 : ℝ) (492066694327/500000000000 : ℝ) (88715096427/500000000000 : ℝ) (177430192861/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67083/524288 : ℝ)) (984133388653/1000000000000 : ℝ) (492066694327/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67083/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984133388653/1000000000000 : ℝ) (492066694327/500000000000 : ℝ) (496033347163/500000000000 : ℝ) (992066694327/1000000000000 : ℝ) (496017486751/500000000000 : ℝ) (15500546461/15625000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67083/524288 : ℝ)) 1 (496033347163/500000000000 : ℝ) (992066694327/1000000000000 : ℝ) (496017486751/500000000000 : ℝ) (15500546461/15625000000 : ℝ) (496025416957/500000000000 : ℝ) (248012708479/250000000000 : ℝ) (992050833787/1000000000000 : ℝ) (992050833789/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67083/524288 : ℝ)) 2 (496025416957/500000000000 : ℝ) (248012708479/250000000000 : ℝ) (992050833787/1000000000000 : ℝ) (992050833789/1000000000000 : ℝ) (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ) (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67083/524288 : ℝ)) 3 (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ) (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ) (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ) (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67083/524288 : ℝ)) 4 (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ) (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ) (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ) (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67083/524288 : ℝ)) 5 (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ) (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ) (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ) (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67083/524288 : ℝ)) 6 (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ) (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ) (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ) (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67083/524288 : ℝ)) 7 (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ) (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ) (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ) (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67083/524288 : ℝ))) (88715096427/500000000000 : ℝ) (177430192861/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67083/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88715096427/500000000000 : ℝ) (177430192861/1000000000000 : ℝ) (588715096427/1000000000000 : ℝ) (588715096431/1000000000000 : ℝ) (421224634671/1000000000000 : ℝ) (10530615867/25000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67083/524288 : ℝ))) 1 (588715096427/1000000000000 : ℝ) (588715096431/1000000000000 : ℝ) (421224634671/1000000000000 : ℝ) (10530615867/25000000000 : ℝ) (504969865549/1000000000000 : ℝ) (126242466389/250000000000 : ℝ) (497977209737/1000000000000 : ℝ) (99595441949/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67083/524288 : ℝ))) 2 (504969865549/1000000000000 : ℝ) (126242466389/250000000000 : ℝ) (497977209737/1000000000000 : ℝ) (99595441949/200000000000 : ℝ) (501473537643/1000000000000 : ℝ) (501473537651/1000000000000 : ℝ) (250730674553/500000000000 : ℝ) (250730674557/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67083/524288 : ℝ))) 3 (501473537643/1000000000000 : ℝ) (501473537651/1000000000000 : ℝ) (250730674553/500000000000 : ℝ) (250730674557/500000000000 : ℝ) (250733721687/500000000000 : ℝ) (501467443383/1000000000000 : ℝ) (501467443337/1000000000000 : ℝ) (250733721673/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67083/524288 : ℝ))) 4 (250733721687/500000000000 : ℝ) (501467443383/1000000000000 : ℝ) (501467443337/1000000000000 : ℝ) (250733721673/500000000000 : ℝ) (100293488671/200000000000 : ℝ) (100293488673/200000000000 : ℝ) (100293488671/200000000000 : ℝ) (100293488673/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67083/524288 : ℝ))) 5 (100293488671/200000000000 : ℝ) (100293488673/200000000000 : ℝ) (100293488671/200000000000 : ℝ) (100293488673/200000000000 : ℝ) (100293488671/200000000000 : ℝ) (100293488673/200000000000 : ℝ) (100293488671/200000000000 : ℝ) (100293488673/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67083/524288 : ℝ))) 6 (100293488671/200000000000 : ℝ) (100293488673/200000000000 : ℝ) (100293488671/200000000000 : ℝ) (100293488673/200000000000 : ℝ) (100293488671/200000000000 : ℝ) (100293488673/200000000000 : ℝ) (100293488671/200000000000 : ℝ) (100293488673/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67083/524288 : ℝ))) 7 (100293488671/200000000000 : ℝ) (100293488673/200000000000 : ℝ) (100293488671/200000000000 : ℝ) (100293488673/200000000000 : ℝ) (100293488671/200000000000 : ℝ) (100293488673/200000000000 : ℝ) (100293488671/200000000000 : ℝ) (100293488673/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67083/524288 : ℝ)) hmem 8 (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ) (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67083/524288 : ℝ))) hcmem 8 (100293488671/200000000000 : ℝ) (100293488673/200000000000 : ℝ) (100293488671/200000000000 : ℝ) (100293488673/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67083/524288 : ℝ)) (19841016677/20000000000 : ℝ) (992050833853/1000000000000 : ℝ) (100293488671/200000000000 : ℝ) (100293488673/200000000000 : ℝ) (198503743747/250000000000 : ℝ) (794014975007/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1010_exp_lower
  have heNumeric : (2054901977093/1000000000000 : ℝ)/4 ≤ Real.exp (-42628237697323/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901977093/1000000000000 : ℝ)/4 ≤ Real.exp ((33541/262144 : ℝ)-(794014975007/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33541/262144 : ℝ) (67083/524288 : ℝ) (794014975007/1000000000000 : ℝ) (2054901977093/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1011; no trusted numerical premise.
theorem cover8_leaf1011_exp_radius : (249500684548005511/250000000000000000 : ℝ) ≤ Real.exp ((-16771/1048576 : ℝ)/8) ∧ Real.exp ((-16771/1048576 : ℝ)/8) ≤ (199600547638404409/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16771/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1011_exp_lower : (460056736471791203/500000000000000000 : ℝ) ≤ Real.exp ((-17051295004417/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051295004417/25600000000000 : ℝ)/8) ≤ (920113472943582407/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051295004417/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1011_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450991537/500000000000 : ℝ) ≤ 4*Real.exp (67083/524288 : ℝ)*Real.exp (-mu (radius 8 (16771/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450991537/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16771/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1011_exp_radius
  have hrNumeric : (492066577009/500000000000 : ℝ) ≤ Real.exp (-16771/1048576 : ℝ) ∧ Real.exp (-16771/1048576 : ℝ) ≤ (984133154019/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492066577009/500000000000 : ℝ) ≤ (radius 8 (16771/131072 : ℝ)) ∧ (radius 8 (16771/131072 : ℝ)) ≤ (984133154019/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16771/131072 : ℝ)) (492066577009/500000000000 : ℝ) (984133154019/1000000000000 : ℝ) (88715747137/500000000000 : ℝ) (177431494281/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16771/131072 : ℝ)) (492066577009/500000000000 : ℝ) (984133154019/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16771/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492066577009/500000000000 : ℝ) (984133154019/1000000000000 : ℝ) (992066577009/1000000000000 : ℝ) (99206657701/100000000000 : ℝ) (992034855243/1000000000000 : ℝ) (198406971049/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16771/131072 : ℝ)) 1 (992066577009/1000000000000 : ℝ) (99206657701/100000000000 : ℝ) (992034855243/1000000000000 : ℝ) (198406971049/200000000000 : ℝ) (496025358063/500000000000 : ℝ) (31001584879/31250000000 : ℝ) (992050715999/1000000000000 : ℝ) (992050716001/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16771/131072 : ℝ)) 2 (496025358063/500000000000 : ℝ) (31001584879/31250000000 : ℝ) (992050715999/1000000000000 : ℝ) (992050716001/1000000000000 : ℝ) (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ) (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16771/131072 : ℝ)) 3 (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ) (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ) (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ) (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16771/131072 : ℝ)) 4 (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ) (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ) (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ) (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16771/131072 : ℝ)) 5 (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ) (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ) (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ) (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16771/131072 : ℝ)) 6 (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ) (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ) (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ) (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16771/131072 : ℝ)) 7 (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ) (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ) (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ) (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16771/131072 : ℝ))) (88715747137/500000000000 : ℝ) (177431494281/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16771/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88715747137/500000000000 : ℝ) (177431494281/1000000000000 : ℝ) (588715747137/1000000000000 : ℝ) (588715747141/1000000000000 : ℝ) (421226179473/1000000000000 : ℝ) (210613089741/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16771/131072 : ℝ))) 1 (588715747137/1000000000000 : ℝ) (588715747141/1000000000000 : ℝ) (421226179473/1000000000000 : ℝ) (210613089741/500000000000 : ℝ) (100994192661/200000000000 : ℝ) (31560685207/62500000000 : ℝ) (497978398087/1000000000000 : ℝ) (99595679619/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16771/131072 : ℝ))) 2 (100994192661/200000000000 : ℝ) (31560685207/62500000000 : ℝ) (497978398087/1000000000000 : ℝ) (99595679619/200000000000 : ℝ) (62684335087/125000000000 : ℝ) (3917770943/7812500000 : ℝ) (250731246251/500000000000 : ℝ) (501462492511/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16771/131072 : ℝ))) 3 (62684335087/125000000000 : ℝ) (3917770943/7812500000 : ℝ) (250731246251/500000000000 : ℝ) (501462492511/1000000000000 : ℝ) (501468586599/1000000000000 : ℝ) (31341786663/62500000000 : ℝ) (501468586561/1000000000000 : ℝ) (501468586571/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16771/131072 : ℝ))) 4 (501468586599/1000000000000 : ℝ) (31341786663/62500000000 : ℝ) (501468586561/1000000000000 : ℝ) (501468586571/1000000000000 : ℝ) (25073429329/50000000000 : ℝ) (50146858659/100000000000 : ℝ) (501468586579/1000000000000 : ℝ) (50146858659/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16771/131072 : ℝ))) 5 (25073429329/50000000000 : ℝ) (50146858659/100000000000 : ℝ) (501468586579/1000000000000 : ℝ) (50146858659/100000000000 : ℝ) (501468586579/1000000000000 : ℝ) (50146858659/100000000000 : ℝ) (501468586579/1000000000000 : ℝ) (50146858659/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16771/131072 : ℝ))) 6 (501468586579/1000000000000 : ℝ) (50146858659/100000000000 : ℝ) (501468586579/1000000000000 : ℝ) (50146858659/100000000000 : ℝ) (501468586579/1000000000000 : ℝ) (50146858659/100000000000 : ℝ) (501468586579/1000000000000 : ℝ) (50146858659/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16771/131072 : ℝ))) 7 (501468586579/1000000000000 : ℝ) (50146858659/100000000000 : ℝ) (501468586579/1000000000000 : ℝ) (50146858659/100000000000 : ℝ) (501468586579/1000000000000 : ℝ) (50146858659/100000000000 : ℝ) (501468586579/1000000000000 : ℝ) (50146858659/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16771/131072 : ℝ)) hmem 8 (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ) (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16771/131072 : ℝ))) hcmem 8 (501468586579/1000000000000 : ℝ) (50146858659/100000000000 : ℝ) (501468586579/1000000000000 : ℝ) (50146858659/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16771/131072 : ℝ)) (496025358031/500000000000 : ℝ) (198410143213/200000000000 : ℝ) (501468586579/1000000000000 : ℝ) (50146858659/100000000000 : ℝ) (31760675177/40000000000 : ℝ) (158803375889/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1011_exp_lower
  have heNumeric : (1027450991537/500000000000 : ℝ)/4 ≤ Real.exp (-17051295004417/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450991537/500000000000 : ℝ)/4 ≤ Real.exp ((67083/524288 : ℝ)-(158803375889/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67083/524288 : ℝ) (16771/131072 : ℝ) (158803375889/200000000000 : ℝ) (1027450991537/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1012; no trusted numerical premise.
theorem cover8_leaf1012_exp_radius : (49900135422461157/50000000000000000 : ℝ) ≤ Real.exp ((-67085/4194304 : ℝ)/8) ∧ Real.exp ((-67085/4194304 : ℝ)/8) ≤ (998002708449223141/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67085/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1012_exp_lower : (115014184159922699/125000000000000000 : ℝ) ≤ Real.exp ((-21314118662093/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314118662093/32000000000000 : ℝ)/8) ≤ (920113473279381593/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314118662093/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1012_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901989073/1000000000000 : ℝ) ≤ 4*Real.exp (16771/131072 : ℝ)*Real.exp (-mu (radius 8 (67085/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901989073/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67085/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1012_exp_radius
  have hrNumeric : (492066459691/500000000000 : ℝ) ≤ Real.exp (-67085/4194304 : ℝ) ∧ Real.exp (-67085/4194304 : ℝ) ≤ (984132919383/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492066459691/500000000000 : ℝ) ≤ (radius 8 (67085/524288 : ℝ)) ∧ (radius 8 (67085/524288 : ℝ)) ≤ (984132919383/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67085/524288 : ℝ)) (492066459691/500000000000 : ℝ) (984132919383/1000000000000 : ℝ) (17743279569/100000000000 : ℝ) (177432795697/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67085/524288 : ℝ)) (492066459691/500000000000 : ℝ) (984132919383/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67085/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492066459691/500000000000 : ℝ) (984132919383/1000000000000 : ℝ) (992066459691/1000000000000 : ℝ) (248016614923/250000000000 : ℝ) (992034736983/1000000000000 : ℝ) (198406947397/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67085/524288 : ℝ)) 1 (992066459691/1000000000000 : ℝ) (248016614923/250000000000 : ℝ) (992034736983/1000000000000 : ℝ) (198406947397/200000000000 : ℝ) (992050598337/1000000000000 : ℝ) (992050598339/1000000000000 : ℝ) (99205059821/100000000000 : ℝ) (248012649553/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67085/524288 : ℝ)) 2 (992050598337/1000000000000 : ℝ) (992050598339/1000000000000 : ℝ) (99205059821/100000000000 : ℝ) (248012649553/250000000000 : ℝ) (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ) (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67085/524288 : ℝ)) 3 (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ) (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ) (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ) (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67085/524288 : ℝ)) 4 (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ) (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ) (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ) (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67085/524288 : ℝ)) 5 (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ) (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ) (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ) (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67085/524288 : ℝ)) 6 (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ) (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ) (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ) (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67085/524288 : ℝ)) 7 (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ) (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ) (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ) (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67085/524288 : ℝ))) (17743279569/100000000000 : ℝ) (177432795697/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67085/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17743279569/100000000000 : ℝ) (177432795697/1000000000000 : ℝ) (117743279569/200000000000 : ℝ) (588716397849/1000000000000 : ℝ) (84245544853/200000000000 : ℝ) (210613862137/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67085/524288 : ℝ))) 1 (117743279569/200000000000 : ℝ) (588716397849/1000000000000 : ℝ) (84245544853/200000000000 : ℝ) (210613862137/500000000000 : ℝ) (100994412211/200000000000 : ℝ) (252486030531/500000000000 : ℝ) (49797958643/100000000000 : ℝ) (248989793219/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67085/524288 : ℝ))) 2 (100994412211/200000000000 : ℝ) (252486030531/500000000000 : ℝ) (49797958643/100000000000 : ℝ) (248989793219/500000000000 : ℝ) (250737911871/500000000000 : ℝ) (401180659/800000000 : ℝ) (125365908973/250000000000 : ℝ) (501463635901/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67085/524288 : ℝ))) 3 (250737911871/500000000000 : ℝ) (401180659/800000000 : ℝ) (125365908973/250000000000 : ℝ) (501463635901/1000000000000 : ℝ) (501469729817/1000000000000 : ℝ) (250734864913/500000000000 : ℝ) (501469729779/1000000000000 : ℝ) (501469729789/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67085/524288 : ℝ))) 4 (501469729817/1000000000000 : ℝ) (250734864913/500000000000 : ℝ) (501469729779/1000000000000 : ℝ) (501469729789/1000000000000 : ℝ) (250734864899/500000000000 : ℝ) (31341858113/62500000000 : ℝ) (501469729797/1000000000000 : ℝ) (31341858113/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67085/524288 : ℝ))) 5 (250734864899/500000000000 : ℝ) (31341858113/62500000000 : ℝ) (501469729797/1000000000000 : ℝ) (31341858113/62500000000 : ℝ) (501469729797/1000000000000 : ℝ) (31341858113/62500000000 : ℝ) (501469729797/1000000000000 : ℝ) (31341858113/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67085/524288 : ℝ))) 6 (501469729797/1000000000000 : ℝ) (31341858113/62500000000 : ℝ) (501469729797/1000000000000 : ℝ) (31341858113/62500000000 : ℝ) (501469729797/1000000000000 : ℝ) (31341858113/62500000000 : ℝ) (501469729797/1000000000000 : ℝ) (31341858113/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67085/524288 : ℝ))) 7 (501469729797/1000000000000 : ℝ) (31341858113/62500000000 : ℝ) (501469729797/1000000000000 : ℝ) (31341858113/62500000000 : ℝ) (501469729797/1000000000000 : ℝ) (31341858113/62500000000 : ℝ) (501469729797/1000000000000 : ℝ) (31341858113/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67085/524288 : ℝ)) hmem 8 (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ) (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67085/524288 : ℝ))) hcmem 8 (501469729797/1000000000000 : ℝ) (31341858113/62500000000 : ℝ) (501469729797/1000000000000 : ℝ) (31341858113/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67085/524288 : ℝ)) (992050598273/1000000000000 : ℝ) (248012649569/250000000000 : ℝ) (501469729797/1000000000000 : ℝ) (31341858113/62500000000 : ℝ) (794018783853/1000000000000 : ℝ) (397009391937/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1012_exp_lower
  have heNumeric : (2054901989073/1000000000000 : ℝ)/4 ≤ Real.exp (-21314118662093/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901989073/1000000000000 : ℝ)/4 ≤ Real.exp ((16771/131072 : ℝ)-(397009391937/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16771/131072 : ℝ) (67085/524288 : ℝ) (397009391937/500000000000 : ℝ) (2054901989073/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1013; no trusted numerical premise.
theorem cover8_leaf1013_exp_radius : (499001339353212561/500000000000000000 : ℝ) ≤ Real.exp ((-33543/2097152 : ℝ)/8) ∧ Real.exp ((-33543/2097152 : ℝ)/8) ≤ (998002678706425123/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33543/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1013_exp_lower : (36804538944736047/40000000000000000 : ℝ) ≤ Real.exp ((-3410258970843/5120000000000 : ℝ)/8) ∧ Real.exp ((-3410258970843/5120000000000 : ℝ)/8) ≤ (115014184202300147/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3410258970843/5120000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1013_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490199513/100000000000 : ℝ) ≤ 4*Real.exp (67085/524288 : ℝ)*Real.exp (-mu (radius 8 (33543/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (205490199513/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33543/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1013_exp_radius
  have hrNumeric : (984132684747/1000000000000 : ℝ) ≤ Real.exp (-33543/2097152 : ℝ) ∧ Real.exp (-33543/2097152 : ℝ) ≤ (246033171187/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984132684747/1000000000000 : ℝ) ≤ (radius 8 (33543/262144 : ℝ)) ∧ (radius 8 (33543/262144 : ℝ)) ≤ (246033171187/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33543/262144 : ℝ)) (984132684747/1000000000000 : ℝ) (246033171187/250000000000 : ℝ) (177434097091/1000000000000 : ℝ) (88717048549/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33543/262144 : ℝ)) (984132684747/1000000000000 : ℝ) (246033171187/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33543/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984132684747/1000000000000 : ℝ) (246033171187/250000000000 : ℝ) (992066342373/1000000000000 : ℝ) (496033171187/500000000000 : ℝ) (248008654681/250000000000 : ℝ) (39681384749/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33543/262144 : ℝ)) 1 (992066342373/1000000000000 : ℝ) (496033171187/500000000000 : ℝ) (248008654681/250000000000 : ℝ) (39681384749/40000000000 : ℝ) (248012620137/250000000000 : ℝ) (19841009611/20000000000 : ℝ) (992050480421/1000000000000 : ℝ) (992050480423/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33543/262144 : ℝ)) 2 (248012620137/250000000000 : ℝ) (19841009611/20000000000 : ℝ) (992050480421/1000000000000 : ℝ) (992050480423/1000000000000 : ℝ) (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ) (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33543/262144 : ℝ)) 3 (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ) (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ) (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ) (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33543/262144 : ℝ)) 4 (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ) (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ) (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ) (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33543/262144 : ℝ)) 5 (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ) (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ) (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ) (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33543/262144 : ℝ)) 6 (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ) (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ) (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ) (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33543/262144 : ℝ)) 7 (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ) (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ) (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ) (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33543/262144 : ℝ))) (177434097091/1000000000000 : ℝ) (88717048549/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33543/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177434097091/1000000000000 : ℝ) (88717048549/500000000000 : ℝ) (117743409709/200000000000 : ℝ) (588717048549/1000000000000 : ℝ) (210614634517/500000000000 : ℝ) (421229269043/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33543/262144 : ℝ))) 1 (117743409709/200000000000 : ℝ) (588717048549/1000000000000 : ℝ) (210614634517/500000000000 : ℝ) (421229269043/1000000000000 : ℝ) (504973158789/1000000000000 : ℝ) (126243289699/250000000000 : ℝ) (99596154951/200000000000 : ℝ) (497980774763/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33543/262144 : ℝ))) 2 (504973158789/1000000000000 : ℝ) (126243289699/250000000000 : ℝ) (99596154951/200000000000 : ℝ) (497980774763/1000000000000 : ℝ) (125369241693/250000000000 : ℝ) (25073848339/50000000000 : ℝ) (100292955853/200000000000 : ℝ) (250732389637/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33543/262144 : ℝ))) 3 (125369241693/250000000000 : ℝ) (25073848339/50000000000 : ℝ) (100292955853/200000000000 : ℝ) (250732389637/500000000000 : ℝ) (250735436509/500000000000 : ℝ) (501470873027/1000000000000 : ℝ) (501470872981/1000000000000 : ℝ) (50147087299/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33543/262144 : ℝ))) 4 (250735436509/500000000000 : ℝ) (501470873027/1000000000000 : ℝ) (501470872981/1000000000000 : ℝ) (50147087299/100000000000 : ℝ) (501470872999/1000000000000 : ℝ) (501470873009/1000000000000 : ℝ) (501470872999/1000000000000 : ℝ) (501470873009/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33543/262144 : ℝ))) 5 (501470872999/1000000000000 : ℝ) (501470873009/1000000000000 : ℝ) (501470872999/1000000000000 : ℝ) (501470873009/1000000000000 : ℝ) (501470872999/1000000000000 : ℝ) (501470873009/1000000000000 : ℝ) (501470872999/1000000000000 : ℝ) (501470873009/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33543/262144 : ℝ))) 6 (501470872999/1000000000000 : ℝ) (501470873009/1000000000000 : ℝ) (501470872999/1000000000000 : ℝ) (501470873009/1000000000000 : ℝ) (501470872999/1000000000000 : ℝ) (501470873009/1000000000000 : ℝ) (501470872999/1000000000000 : ℝ) (501470873009/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33543/262144 : ℝ))) 7 (501470872999/1000000000000 : ℝ) (501470873009/1000000000000 : ℝ) (501470872999/1000000000000 : ℝ) (501470873009/1000000000000 : ℝ) (501470872999/1000000000000 : ℝ) (501470873009/1000000000000 : ℝ) (501470872999/1000000000000 : ℝ) (501470873009/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33543/262144 : ℝ)) hmem 8 (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ) (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33543/262144 : ℝ))) hcmem 8 (501470872999/1000000000000 : ℝ) (501470873009/1000000000000 : ℝ) (501470872999/1000000000000 : ℝ) (501470873009/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33543/262144 : ℝ)) (248012620121/250000000000 : ℝ) (992050480487/1000000000000 : ℝ) (501470872999/1000000000000 : ℝ) (501470873009/1000000000000 : ℝ) (6203286627/7812500000 : ℝ) (31760827531/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1013_exp_lower
  have heNumeric : (205490199513/100000000000 : ℝ)/4 ≤ Real.exp (-3410258970843/5120000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490199513/100000000000 : ℝ)/4 ≤ Real.exp ((67085/524288 : ℝ)-(31760827531/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67085/524288 : ℝ) (33543/262144 : ℝ) (31760827531/40000000000 : ℝ) (205490199513/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1014; no trusted numerical premise.
theorem cover8_leaf1014_exp_radius : (998002648963627991/1000000000000000000 : ℝ) ≤ Real.exp ((-67087/4194304 : ℝ)/8) ∧ Real.exp ((-67087/4194304 : ℝ)/8) ≤ (124750331120453499/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67087/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1014_exp_lower : (9201134739585709/10000000000000000 : ℝ) ≤ Real.exp ((-42628236946249/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628236946249/64000000000000 : ℝ)/8) ≤ (920113473958570901/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628236946249/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1014_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862750151/125000000000 : ℝ) ≤ 4*Real.exp (33543/262144 : ℝ)*Real.exp (-mu (radius 8 (67087/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862750151/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67087/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1014_exp_radius
  have hrNumeric : (984132450111/1000000000000 : ℝ) ≤ Real.exp (-67087/4194304 : ℝ) ∧ Real.exp (-67087/4194304 : ℝ) ≤ (15377069533/15625000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984132450111/1000000000000 : ℝ) ≤ (radius 8 (67087/524288 : ℝ)) ∧ (radius 8 (67087/524288 : ℝ)) ≤ (15377069533/15625000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67087/524288 : ℝ)) (984132450111/1000000000000 : ℝ) (15377069533/15625000000 : ℝ) (177435398487/1000000000000 : ℝ) (88717699247/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67087/524288 : ℝ)) (984132450111/1000000000000 : ℝ) (15377069533/15625000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67087/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984132450111/1000000000000 : ℝ) (15377069533/15625000000 : ℝ) (198413245011/200000000000 : ℝ) (31002069533/31250000000 : ℝ) (62002156279/62500000000 : ℝ) (198406900093/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67087/524288 : ℝ)) 1 (198413245011/200000000000 : ℝ) (31002069533/31250000000 : ℝ) (62002156279/62500000000 : ℝ) (198406900093/200000000000 : ℝ) (992050362759/1000000000000 : ℝ) (992050362761/1000000000000 : ℝ) (124006295329/125000000000 : ℝ) (496025181317/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67087/524288 : ℝ)) 2 (992050362759/1000000000000 : ℝ) (992050362761/1000000000000 : ℝ) (124006295329/125000000000 : ℝ) (496025181317/500000000000 : ℝ) (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ) (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67087/524288 : ℝ)) 3 (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ) (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ) (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ) (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67087/524288 : ℝ)) 4 (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ) (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ) (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ) (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67087/524288 : ℝ)) 5 (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ) (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ) (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ) (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67087/524288 : ℝ)) 6 (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ) (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ) (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ) (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67087/524288 : ℝ)) 7 (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ) (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ) (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ) (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67087/524288 : ℝ))) (177435398487/1000000000000 : ℝ) (88717699247/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67087/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177435398487/1000000000000 : ℝ) (88717699247/500000000000 : ℝ) (588717699243/1000000000000 : ℝ) (588717699247/1000000000000 : ℝ) (42123081379/100000000000 : ℝ) (2106154069/5000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67087/524288 : ℝ))) 1 (588717699243/1000000000000 : ℝ) (588717699247/1000000000000 : ℝ) (42123081379/100000000000 : ℝ) (2106154069/5000000000 : ℝ) (126243564129/250000000000 : ℝ) (126243564131/250000000000 : ℝ) (497981963071/1000000000000 : ℝ) (12449549077/25000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67087/524288 : ℝ))) 2 (126243564129/250000000000 : ℝ) (126243564131/250000000000 : ℝ) (497981963071/1000000000000 : ℝ) (12449549077/25000000000 : ℝ) (501478109793/1000000000000 : ℝ) (250739054901/500000000000 : ℝ) (50146592263/100000000000 : ℝ) (6268324033/12500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67087/524288 : ℝ))) 3 (501478109793/1000000000000 : ℝ) (250739054901/500000000000 : ℝ) (50146592263/100000000000 : ℝ) (6268324033/12500000000 : ℝ) (501472016211/1000000000000 : ℝ) (501472016221/1000000000000 : ℝ) (250736008087/500000000000 : ℝ) (62684002023/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67087/524288 : ℝ))) 4 (501472016211/1000000000000 : ℝ) (501472016221/1000000000000 : ℝ) (250736008087/500000000000 : ℝ) (62684002023/125000000000 : ℝ) (7835500253/15625000000 : ℝ) (501472016203/1000000000000 : ℝ) (7835500253/15625000000 : ℝ) (501472016203/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67087/524288 : ℝ))) 5 (7835500253/15625000000 : ℝ) (501472016203/1000000000000 : ℝ) (7835500253/15625000000 : ℝ) (501472016203/1000000000000 : ℝ) (7835500253/15625000000 : ℝ) (501472016203/1000000000000 : ℝ) (7835500253/15625000000 : ℝ) (501472016203/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67087/524288 : ℝ))) 6 (7835500253/15625000000 : ℝ) (501472016203/1000000000000 : ℝ) (7835500253/15625000000 : ℝ) (501472016203/1000000000000 : ℝ) (7835500253/15625000000 : ℝ) (501472016203/1000000000000 : ℝ) (7835500253/15625000000 : ℝ) (501472016203/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67087/524288 : ℝ))) 7 (7835500253/15625000000 : ℝ) (501472016203/1000000000000 : ℝ) (7835500253/15625000000 : ℝ) (501472016203/1000000000000 : ℝ) (7835500253/15625000000 : ℝ) (501472016203/1000000000000 : ℝ) (7835500253/15625000000 : ℝ) (501472016203/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67087/524288 : ℝ)) hmem 8 (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ) (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67087/524288 : ℝ))) hcmem 8 (7835500253/15625000000 : ℝ) (501472016203/1000000000000 : ℝ) (7835500253/15625000000 : ℝ) (501472016203/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67087/524288 : ℝ)) (198410072539/200000000000 : ℝ) (496025181349/500000000000 : ℝ) (7835500253/15625000000 : ℝ) (501472016203/1000000000000 : ℝ) (158804518529/200000000000 : ℝ) (397011296333/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1014_exp_lower
  have heNumeric : (256862750151/125000000000 : ℝ)/4 ≤ Real.exp (-42628236946249/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862750151/125000000000 : ℝ)/4 ≤ Real.exp ((33543/262144 : ℝ)-(397011296333/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33543/262144 : ℝ) (67087/524288 : ℝ) (397011296333/500000000000 : ℝ) (256862750151/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1015; no trusted numerical premise.
theorem cover8_leaf1015_exp_radius : (499001309610415873/500000000000000000 : ℝ) ≤ Real.exp ((-4193/262144 : ℝ)/8) ∧ Real.exp ((-4193/262144 : ℝ)/8) ≤ (998002619220831747/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4193/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1015_exp_lower : (920113474301846009/1000000000000000000 : ℝ) ≤ Real.exp ((-17051294702093/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051294702093/25600000000000 : ℝ)/8) ≤ (92011347430184601/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051294702093/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1015_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902007341/1000000000000 : ℝ) ≤ 4*Real.exp (67087/524288 : ℝ)*Real.exp (-mu (radius 8 (4193/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902007341/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4193/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1015_exp_radius
  have hrNumeric : (246033053869/250000000000 : ℝ) ≤ Real.exp (-4193/262144 : ℝ) ∧ Real.exp (-4193/262144 : ℝ) ≤ (984132215477/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246033053869/250000000000 : ℝ) ≤ (radius 8 (4193/32768 : ℝ)) ∧ (radius 8 (4193/32768 : ℝ)) ≤ (984132215477/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4193/32768 : ℝ)) (246033053869/250000000000 : ℝ) (984132215477/1000000000000 : ℝ) (44359174967/250000000000 : ℝ) (1419493599/8000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4193/32768 : ℝ)) (246033053869/250000000000 : ℝ) (984132215477/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4193/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246033053869/250000000000 : ℝ) (984132215477/1000000000000 : ℝ) (496033053869/500000000000 : ℝ) (992066107739/1000000000000 : ℝ) (248008595551/250000000000 : ℝ) (496017191103/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4193/32768 : ℝ)) 1 (496033053869/500000000000 : ℝ) (992066107739/1000000000000 : ℝ) (248008595551/250000000000 : ℝ) (496017191103/500000000000 : ℝ) (992050244971/1000000000000 : ℝ) (992050244973/1000000000000 : ℝ) (248012561211/250000000000 : ℝ) (496025122423/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4193/32768 : ℝ)) 2 (992050244971/1000000000000 : ℝ) (992050244973/1000000000000 : ℝ) (248012561211/250000000000 : ℝ) (496025122423/500000000000 : ℝ) (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ) (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4193/32768 : ℝ)) 3 (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ) (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ) (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ) (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4193/32768 : ℝ)) 4 (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ) (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ) (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ) (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4193/32768 : ℝ)) 5 (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ) (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ) (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ) (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4193/32768 : ℝ)) 6 (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ) (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ) (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ) (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4193/32768 : ℝ)) 7 (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ) (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ) (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ) (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4193/32768 : ℝ))) (44359174967/250000000000 : ℝ) (1419493599/8000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4193/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44359174967/250000000000 : ℝ) (1419493599/8000000000 : ℝ) (294359174967/500000000000 : ℝ) (294359174969/500000000000 : ℝ) (105308089631/250000000000 : ℝ) (421232358533/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4193/32768 : ℝ))) 1 (294359174967/500000000000 : ℝ) (294359174969/500000000000 : ℝ) (105308089631/250000000000 : ℝ) (421232358533/1000000000000 : ℝ) (504975354229/1000000000000 : ℝ) (126243838559/250000000000 : ℝ) (49798315137/100000000000 : ℝ) (248991575689/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4193/32768 : ℝ))) 2 (504975354229/1000000000000 : ℝ) (126243838559/250000000000 : ℝ) (49798315137/100000000000 : ℝ) (248991575689/500000000000 : ℝ) (501479252799/1000000000000 : ℝ) (501479252807/1000000000000 : ℝ) (25073353299/50000000000 : ℝ) (501467065989/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4193/32768 : ℝ))) 3 (501479252799/1000000000000 : ℝ) (501479252807/1000000000000 : ℝ) (25073353299/50000000000 : ℝ) (501467065989/1000000000000 : ℝ) (501473159389/1000000000000 : ℝ) (250736579699/500000000000 : ℝ) (62684144919/125000000000 : ℝ) (501473159361/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4193/32768 : ℝ))) 4 (501473159389/1000000000000 : ℝ) (250736579699/500000000000 : ℝ) (62684144919/125000000000 : ℝ) (501473159361/1000000000000 : ℝ) (50147315937/100000000000 : ℝ) (25073657969/50000000000 : ℝ) (50147315937/100000000000 : ℝ) (25073657969/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4193/32768 : ℝ))) 5 (50147315937/100000000000 : ℝ) (25073657969/50000000000 : ℝ) (50147315937/100000000000 : ℝ) (25073657969/50000000000 : ℝ) (50147315937/100000000000 : ℝ) (25073657969/50000000000 : ℝ) (50147315937/100000000000 : ℝ) (25073657969/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4193/32768 : ℝ))) 6 (50147315937/100000000000 : ℝ) (25073657969/50000000000 : ℝ) (50147315937/100000000000 : ℝ) (25073657969/50000000000 : ℝ) (50147315937/100000000000 : ℝ) (25073657969/50000000000 : ℝ) (50147315937/100000000000 : ℝ) (25073657969/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4193/32768 : ℝ))) 7 (50147315937/100000000000 : ℝ) (25073657969/50000000000 : ℝ) (50147315937/100000000000 : ℝ) (25073657969/50000000000 : ℝ) (50147315937/100000000000 : ℝ) (25073657969/50000000000 : ℝ) (50147315937/100000000000 : ℝ) (25073657969/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4193/32768 : ℝ)) hmem 8 (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ) (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4193/32768 : ℝ))) hcmem 8 (50147315937/100000000000 : ℝ) (25073657969/50000000000 : ℝ) (50147315937/100000000000 : ℝ) (25073657969/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4193/32768 : ℝ)) (992050244907/1000000000000 : ℝ) (99205024491/100000000000 : ℝ) (50147315937/100000000000 : ℝ) (25073657969/50000000000 : ℝ) (794024497011/1000000000000 : ℝ) (79402449703/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1015_exp_lower
  have heNumeric : (2054902007341/1000000000000 : ℝ)/4 ≤ Real.exp (-17051294702093/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902007341/1000000000000 : ℝ)/4 ≤ Real.exp ((67087/524288 : ℝ)-(79402449703/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67087/524288 : ℝ) (4193/32768 : ℝ) (79402449703/100000000000 : ℝ) (2054902007341/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1016; no trusted numerical premise.
theorem cover8_leaf1016_exp_radius : (998002589478036387/1000000000000000000 : ℝ) ≤ Real.exp ((-67089/4194304 : ℝ)/8) ∧ Real.exp ((-67089/4194304 : ℝ)/8) ≤ (249500647369509097/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67089/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1016_exp_lower : (920113474646271259/1000000000000000000 : ℝ) ≤ Real.exp ((-5328529570447/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328529570447/8000000000000 : ℝ)/8) ≤ (46005673732313563/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328529570447/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1016_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980402699/200000000000 : ℝ) ≤ 4*Real.exp (4193/32768 : ℝ)*Real.exp (-mu (radius 8 (67089/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980402699/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67089/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1016_exp_radius
  have hrNumeric : (24603299521/25000000000 : ℝ) ≤ Real.exp (-67089/4194304 : ℝ) ∧ Real.exp (-67089/4194304 : ℝ) ≤ (984131980841/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24603299521/25000000000 : ℝ) ≤ (radius 8 (67089/524288 : ℝ)) ∧ (radius 8 (67089/524288 : ℝ)) ≤ (984131980841/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67089/524288 : ℝ)) (24603299521/25000000000 : ℝ) (984131980841/1000000000000 : ℝ) (35487600249/200000000000 : ℝ) (177438001251/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67089/524288 : ℝ)) (24603299521/25000000000 : ℝ) (984131980841/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67089/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24603299521/25000000000 : ℝ) (984131980841/1000000000000 : ℝ) (49603299521/50000000000 : ℝ) (992065990421/1000000000000 : ℝ) (124004282993/125000000000 : ℝ) (496017131973/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67089/524288 : ℝ)) 1 (49603299521/50000000000 : ℝ) (992065990421/1000000000000 : ℝ) (124004282993/125000000000 : ℝ) (496017131973/500000000000 : ℝ) (496025063591/500000000000 : ℝ) (62003132949/62500000000 : ℝ) (198410025411/200000000000 : ℝ) (992050127057/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67089/524288 : ℝ)) 2 (496025063591/500000000000 : ℝ) (62003132949/62500000000 : ℝ) (198410025411/200000000000 : ℝ) (992050127057/1000000000000 : ℝ) (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ) (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67089/524288 : ℝ)) 3 (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ) (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ) (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ) (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67089/524288 : ℝ)) 4 (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ) (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ) (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ) (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67089/524288 : ℝ)) 5 (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ) (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ) (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ) (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67089/524288 : ℝ)) 6 (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ) (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ) (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ) (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67089/524288 : ℝ)) 7 (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ) (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ) (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ) (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67089/524288 : ℝ))) (35487600249/200000000000 : ℝ) (177438001251/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67089/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35487600249/200000000000 : ℝ) (177438001251/1000000000000 : ℝ) (294359500311/500000000000 : ℝ) (294359500313/500000000000 : ℝ) (421233903247/1000000000000 : ℝ) (84246780651/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67089/524288 : ℝ))) 1 (294359500311/500000000000 : ℝ) (294359500313/500000000000 : ℝ) (421233903247/1000000000000 : ℝ) (84246780651/200000000000 : ℝ) (252488225967/500000000000 : ℝ) (504976451941/1000000000000 : ℝ) (497984339661/1000000000000 : ℝ) (124496084917/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67089/524288 : ℝ))) 2 (252488225967/500000000000 : ℝ) (504976451941/1000000000000 : ℝ) (497984339661/1000000000000 : ℝ) (124496084917/250000000000 : ℝ) (501480395797/1000000000000 : ℝ) (100296079161/200000000000 : ℝ) (250734104661/500000000000 : ℝ) (50146820933/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67089/524288 : ℝ))) 3 (501480395797/1000000000000 : ℝ) (100296079161/200000000000 : ℝ) (250734104661/500000000000 : ℝ) (50146820933/100000000000 : ℝ) (501474302559/1000000000000 : ℝ) (62684287821/125000000000 : ℝ) (250737151261/500000000000 : ℝ) (501474302531/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67089/524288 : ℝ))) 4 (501474302559/1000000000000 : ℝ) (62684287821/125000000000 : ℝ) (250737151261/500000000000 : ℝ) (501474302531/1000000000000 : ℝ) (25073715127/50000000000 : ℝ) (10029486051/20000000000 : ℝ) (25073715127/50000000000 : ℝ) (10029486051/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67089/524288 : ℝ))) 5 (25073715127/50000000000 : ℝ) (10029486051/20000000000 : ℝ) (25073715127/50000000000 : ℝ) (10029486051/20000000000 : ℝ) (25073715127/50000000000 : ℝ) (10029486051/20000000000 : ℝ) (25073715127/50000000000 : ℝ) (10029486051/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67089/524288 : ℝ))) 6 (25073715127/50000000000 : ℝ) (10029486051/20000000000 : ℝ) (25073715127/50000000000 : ℝ) (10029486051/20000000000 : ℝ) (25073715127/50000000000 : ℝ) (10029486051/20000000000 : ℝ) (25073715127/50000000000 : ℝ) (10029486051/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67089/524288 : ℝ))) 7 (25073715127/50000000000 : ℝ) (10029486051/20000000000 : ℝ) (25073715127/50000000000 : ℝ) (10029486051/20000000000 : ℝ) (25073715127/50000000000 : ℝ) (10029486051/20000000000 : ℝ) (25073715127/50000000000 : ℝ) (10029486051/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67089/524288 : ℝ)) hmem 8 (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ) (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67089/524288 : ℝ))) hcmem 8 (25073715127/50000000000 : ℝ) (10029486051/20000000000 : ℝ) (25073715127/50000000000 : ℝ) (10029486051/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67089/524288 : ℝ)) (496025063559/500000000000 : ℝ) (992050127121/1000000000000 : ℝ) (25073715127/50000000000 : ℝ) (10029486051/20000000000 : ℝ) (158805280273/200000000000 : ℝ) (99253300173/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1016_exp_lower
  have heNumeric : (410980402699/200000000000 : ℝ)/4 ≤ Real.exp (-5328529570447/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980402699/200000000000 : ℝ)/4 ≤ Real.exp ((4193/32768 : ℝ)-(99253300173/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4193/32768 : ℝ) (67089/524288 : ℝ) (99253300173/125000000000 : ℝ) (410980402699/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1017; no trusted numerical premise.
theorem cover8_leaf1017_exp_radius : (199600511947048383/200000000000000000 : ℝ) ≤ Real.exp ((-33545/2097152 : ℝ)/8) ∧ Real.exp ((-33545/2097152 : ℝ)/8) ≤ (249500639933810479/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33545/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1017_exp_lower : (920113474993916907/1000000000000000000 : ℝ) ≤ Real.exp ((-17051294548051/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051294548051/25600000000000 : ℝ)/8) ≤ (230028368748479227/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051294548051/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1017_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451009853/500000000000 : ℝ) ≤ 4*Real.exp (67089/524288 : ℝ)*Real.exp (-mu (radius 8 (33545/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451009853/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33545/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1017_exp_radius
  have hrNumeric : (196826349241/200000000000 : ℝ) ≤ Real.exp (-33545/2097152 : ℝ) ∧ Real.exp (-33545/2097152 : ℝ) ≤ (492065873103/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196826349241/200000000000 : ℝ) ≤ (radius 8 (33545/262144 : ℝ)) ∧ (radius 8 (33545/262144 : ℝ)) ≤ (492065873103/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33545/262144 : ℝ)) (196826349241/200000000000 : ℝ) (492065873103/500000000000 : ℝ) (88719651303/500000000000 : ℝ) (177439302613/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33545/262144 : ℝ)) (196826349241/200000000000 : ℝ) (492065873103/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33545/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196826349241/200000000000 : ℝ) (492065873103/500000000000 : ℝ) (496032936551/500000000000 : ℝ) (992065873103/1000000000000 : ℝ) (198406829137/200000000000 : ℝ) (496017072843/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33545/262144 : ℝ)) 1 (496032936551/500000000000 : ℝ) (992065873103/1000000000000 : ℝ) (198406829137/200000000000 : ℝ) (496017072843/500000000000 : ℝ) (992050009393/1000000000000 : ℝ) (198410001879/200000000000 : ℝ) (496025004633/500000000000 : ℝ) (248012502317/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33545/262144 : ℝ)) 2 (992050009393/1000000000000 : ℝ) (198410001879/200000000000 : ℝ) (496025004633/500000000000 : ℝ) (248012502317/250000000000 : ℝ) (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ) (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33545/262144 : ℝ)) 3 (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ) (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ) (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ) (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33545/262144 : ℝ)) 4 (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ) (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ) (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ) (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33545/262144 : ℝ)) 5 (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ) (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ) (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ) (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33545/262144 : ℝ)) 6 (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ) (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ) (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ) (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33545/262144 : ℝ)) 7 (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ) (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ) (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ) (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33545/262144 : ℝ))) (88719651303/500000000000 : ℝ) (177439302613/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33545/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88719651303/500000000000 : ℝ) (177439302613/1000000000000 : ℝ) (588719651303/1000000000000 : ℝ) (588719651307/1000000000000 : ℝ) (84247089589/200000000000 : ℝ) (210617723977/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33545/262144 : ℝ))) 1 (588719651303/1000000000000 : ℝ) (588719651307/1000000000000 : ℝ) (84247089589/200000000000 : ℝ) (210617723977/500000000000 : ℝ) (63122193703/125000000000 : ℝ) (504977549631/1000000000000 : ℝ) (124496381983/250000000000 : ℝ) (24899276397/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33545/262144 : ℝ))) 2 (63122193703/125000000000 : ℝ) (504977549631/1000000000000 : ℝ) (124496381983/250000000000 : ℝ) (24899276397/50000000000 : ℝ) (250740769389/500000000000 : ℝ) (250740769393/500000000000 : ℝ) (250734676323/500000000000 : ℝ) (250734676327/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33545/262144 : ℝ))) 3 (250740769389/500000000000 : ℝ) (250740769393/500000000000 : ℝ) (250734676323/500000000000 : ℝ) (250734676327/500000000000 : ℝ) (31342215357/62500000000 : ℝ) (12536886143/25000000000 : ℝ) (250737722837/500000000000 : ℝ) (501475445683/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33545/262144 : ℝ))) 4 (31342215357/62500000000 : ℝ) (12536886143/25000000000 : ℝ) (250737722837/500000000000 : ℝ) (501475445683/1000000000000 : ℝ) (501475445693/1000000000000 : ℝ) (250737722851/500000000000 : ℝ) (125368861423/250000000000 : ℝ) (250737722851/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33545/262144 : ℝ))) 5 (501475445693/1000000000000 : ℝ) (250737722851/500000000000 : ℝ) (125368861423/250000000000 : ℝ) (250737722851/500000000000 : ℝ) (125368861423/250000000000 : ℝ) (250737722851/500000000000 : ℝ) (125368861423/250000000000 : ℝ) (250737722851/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33545/262144 : ℝ))) 6 (125368861423/250000000000 : ℝ) (250737722851/500000000000 : ℝ) (125368861423/250000000000 : ℝ) (250737722851/500000000000 : ℝ) (125368861423/250000000000 : ℝ) (250737722851/500000000000 : ℝ) (125368861423/250000000000 : ℝ) (250737722851/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33545/262144 : ℝ))) 7 (125368861423/250000000000 : ℝ) (250737722851/500000000000 : ℝ) (125368861423/250000000000 : ℝ) (250737722851/500000000000 : ℝ) (125368861423/250000000000 : ℝ) (250737722851/500000000000 : ℝ) (125368861423/250000000000 : ℝ) (250737722851/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33545/262144 : ℝ)) hmem 8 (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ) (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33545/262144 : ℝ))) hcmem 8 (125368861423/250000000000 : ℝ) (250737722851/500000000000 : ℝ) (125368861423/250000000000 : ℝ) (250737722851/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33545/262144 : ℝ)) (992050009329/1000000000000 : ℝ) (248012502333/250000000000 : ℝ) (125368861423/250000000000 : ℝ) (250737722851/500000000000 : ℝ) (794028305691/1000000000000 : ℝ) (79402830571/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1017_exp_lower
  have heNumeric : (1027451009853/500000000000 : ℝ)/4 ≤ Real.exp (-17051294548051/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451009853/500000000000 : ℝ)/4 ≤ Real.exp ((67089/524288 : ℝ)-(79402830571/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67089/524288 : ℝ) (33545/262144 : ℝ) (79402830571/100000000000 : ℝ) (1027451009853/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1018; no trusted numerical premise.
theorem cover8_leaf1018_exp_radius : (998002529992448329/1000000000000000000 : ℝ) ≤ Real.exp ((-67091/4194304 : ℝ)/8) ∧ Real.exp ((-67091/4194304 : ℝ)/8) ≤ (99800252999244833/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67091/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1018_exp_lower : (460056737671931419/500000000000000000 : ℝ) ≤ Real.exp ((-42628236175399/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628236175399/64000000000000 : ℝ)/8) ≤ (920113475343862839/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628236175399/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1018_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451012979/500000000000 : ℝ) ≤ 4*Real.exp (33545/262144 : ℝ)*Real.exp (-mu (radius 8 (67091/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451012979/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67091/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1018_exp_radius
  have hrNumeric : (98413151157/100000000000 : ℝ) ≤ Real.exp (-67091/4194304 : ℝ) ∧ Real.exp (-67091/4194304 : ℝ) ≤ (984131511571/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98413151157/100000000000 : ℝ) ≤ (radius 8 (67091/524288 : ℝ)) ∧ (radius 8 (67091/524288 : ℝ)) ≤ (984131511571/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67091/524288 : ℝ)) (98413151157/100000000000 : ℝ) (984131511571/1000000000000 : ℝ) (177440603957/1000000000000 : ℝ) (44360150991/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67091/524288 : ℝ)) (98413151157/100000000000 : ℝ) (984131511571/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67091/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98413151157/100000000000 : ℝ) (984131511571/1000000000000 : ℝ) (198413151157/200000000000 : ℝ) (496032877893/500000000000 : ℝ) (39681361097/40000000000 : ℝ) (496017013713/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67091/524288 : ℝ)) 1 (198413151157/200000000000 : ℝ) (496032877893/500000000000 : ℝ) (39681361097/40000000000 : ℝ) (496017013713/500000000000 : ℝ) (198409978321/200000000000 : ℝ) (496024945803/500000000000 : ℝ) (496024945739/500000000000 : ℝ) (24801247287/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67091/524288 : ℝ)) 2 (198409978321/200000000000 : ℝ) (496024945803/500000000000 : ℝ) (496024945739/500000000000 : ℝ) (24801247287/25000000000 : ℝ) (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ) (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67091/524288 : ℝ)) 3 (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ) (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ) (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ) (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67091/524288 : ℝ)) 4 (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ) (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ) (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ) (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67091/524288 : ℝ)) 5 (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ) (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ) (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ) (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67091/524288 : ℝ)) 6 (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ) (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ) (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ) (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67091/524288 : ℝ)) 7 (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ) (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ) (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ) (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67091/524288 : ℝ))) (177440603957/1000000000000 : ℝ) (44360150991/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67091/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177440603957/1000000000000 : ℝ) (44360150991/250000000000 : ℝ) (294360150989/500000000000 : ℝ) (294360150991/500000000000 : ℝ) (210618496313/500000000000 : ℝ) (84247398527/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67091/524288 : ℝ))) 1 (294360150989/500000000000 : ℝ) (294360150991/500000000000 : ℝ) (210618496313/500000000000 : ℝ) (84247398527/200000000000 : ℝ) (252489323651/500000000000 : ℝ) (504978647309/1000000000000 : ℝ) (497986716191/1000000000000 : ℝ) (497986716199/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67091/524288 : ℝ))) 2 (252489323651/500000000000 : ℝ) (504978647309/1000000000000 : ℝ) (497986716191/1000000000000 : ℝ) (497986716199/1000000000000 : ℝ) (250741340873/500000000000 : ℝ) (250741340877/500000000000 : ℝ) (250735247979/500000000000 : ℝ) (250735247983/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67091/524288 : ℝ))) 3 (250741340873/500000000000 : ℝ) (250741340877/500000000000 : ℝ) (250735247979/500000000000 : ℝ) (250735247983/500000000000 : ℝ) (125369147213/250000000000 : ℝ) (25073829443/50000000000 : ℝ) (250738294407/500000000000 : ℝ) (501476588823/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67091/524288 : ℝ))) 4 (125369147213/250000000000 : ℝ) (25073829443/50000000000 : ℝ) (250738294407/500000000000 : ℝ) (501476588823/1000000000000 : ℝ) (501476588833/1000000000000 : ℝ) (250738294421/500000000000 : ℝ) (15671143401/31250000000 : ℝ) (250738294421/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67091/524288 : ℝ))) 5 (501476588833/1000000000000 : ℝ) (250738294421/500000000000 : ℝ) (15671143401/31250000000 : ℝ) (250738294421/500000000000 : ℝ) (15671143401/31250000000 : ℝ) (250738294421/500000000000 : ℝ) (15671143401/31250000000 : ℝ) (250738294421/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67091/524288 : ℝ))) 6 (15671143401/31250000000 : ℝ) (250738294421/500000000000 : ℝ) (15671143401/31250000000 : ℝ) (250738294421/500000000000 : ℝ) (15671143401/31250000000 : ℝ) (250738294421/500000000000 : ℝ) (15671143401/31250000000 : ℝ) (250738294421/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67091/524288 : ℝ))) 7 (15671143401/31250000000 : ℝ) (250738294421/500000000000 : ℝ) (15671143401/31250000000 : ℝ) (250738294421/500000000000 : ℝ) (15671143401/31250000000 : ℝ) (250738294421/500000000000 : ℝ) (15671143401/31250000000 : ℝ) (250738294421/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67091/524288 : ℝ)) hmem 8 (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ) (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67091/524288 : ℝ))) hcmem 8 (15671143401/31250000000 : ℝ) (250738294421/500000000000 : ℝ) (15671143401/31250000000 : ℝ) (250738294421/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67091/524288 : ℝ)) (992049891541/1000000000000 : ℝ) (992049891543/1000000000000 : ℝ) (15671143401/31250000000 : ℝ) (250738294421/500000000000 : ℝ) (397015104999/500000000000 : ℝ) (24813444063/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1018_exp_lower
  have heNumeric : (1027451012979/500000000000 : ℝ)/4 ≤ Real.exp (-42628236175399/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451012979/500000000000 : ℝ)/4 ≤ Real.exp ((33545/262144 : ℝ)-(24813444063/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33545/262144 : ℝ) (67091/524288 : ℝ) (24813444063/31250000000 : ℝ) (1027451012979/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1019; no trusted numerical premise.
theorem cover8_leaf1019_exp_radius : (99800250024965563/100000000000000000 : ℝ) ≤ Real.exp ((-16773/1048576 : ℝ)/8) ∧ Real.exp ((-16773/1048576 : ℝ)/8) ≤ (998002500249655631/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16773/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1019_exp_lower : (460056737847766991/500000000000000000 : ℝ) ≤ Real.exp ((-85256471959421/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256471959421/128000000000000 : ℝ)/8) ≤ (920113475695533983/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256471959421/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1019_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451016121/500000000000 : ℝ) ≤ 4*Real.exp (67091/524288 : ℝ)*Real.exp (-mu (radius 8 (16773/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451016121/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16773/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1019_exp_radius
  have hrNumeric : (196826255387/200000000000 : ℝ) ≤ Real.exp (-16773/1048576 : ℝ) ∧ Real.exp (-16773/1048576 : ℝ) ≤ (123016409617/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196826255387/200000000000 : ℝ) ≤ (radius 8 (16773/131072 : ℝ)) ∧ (radius 8 (16773/131072 : ℝ)) ≤ (123016409617/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16773/131072 : ℝ)) (196826255387/200000000000 : ℝ) (123016409617/125000000000 : ℝ) (177441905299/1000000000000 : ℝ) (88720952653/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16773/131072 : ℝ)) (196826255387/200000000000 : ℝ) (123016409617/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16773/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196826255387/200000000000 : ℝ) (123016409617/125000000000 : ℝ) (992065638467/1000000000000 : ℝ) (248016409617/250000000000 : ℝ) (198406781833/200000000000 : ℝ) (992033909167/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16773/131072 : ℝ)) 1 (992065638467/1000000000000 : ℝ) (248016409617/250000000000 : ℝ) (198406781833/200000000000 : ℝ) (992033909167/1000000000000 : ℝ) (124006221727/125000000000 : ℝ) (496024886909/500000000000 : ℝ) (992049773689/1000000000000 : ℝ) (992049773691/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16773/131072 : ℝ)) 2 (124006221727/125000000000 : ℝ) (496024886909/500000000000 : ℝ) (992049773689/1000000000000 : ℝ) (992049773691/1000000000000 : ℝ) (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ) (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16773/131072 : ℝ)) 3 (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ) (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ) (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ) (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16773/131072 : ℝ)) 4 (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ) (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ) (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ) (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16773/131072 : ℝ)) 5 (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ) (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ) (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ) (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16773/131072 : ℝ)) 6 (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ) (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ) (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ) (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16773/131072 : ℝ)) 7 (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ) (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ) (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ) (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16773/131072 : ℝ))) (177441905299/1000000000000 : ℝ) (88720952653/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16773/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177441905299/1000000000000 : ℝ) (88720952653/500000000000 : ℝ) (588720952649/1000000000000 : ℝ) (588720952653/1000000000000 : ℝ) (42123853729/100000000000 : ℝ) (4212385373/10000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16773/131072 : ℝ))) 1 (588720952649/1000000000000 : ℝ) (588720952653/1000000000000 : ℝ) (42123853729/100000000000 : ℝ) (4212385373/10000000000 : ℝ) (504979744969/1000000000000 : ℝ) (504979744977/1000000000000 : ℝ) (497987904437/1000000000000 : ℝ) (99597580889/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16773/131072 : ℝ))) 2 (504979744969/1000000000000 : ℝ) (504979744977/1000000000000 : ℝ) (497987904437/1000000000000 : ℝ) (99597580889/200000000000 : ℝ) (501483824703/1000000000000 : ℝ) (501483824711/1000000000000 : ℝ) (250735819629/500000000000 : ℝ) (501471639267/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16773/131072 : ℝ))) 3 (501483824703/1000000000000 : ℝ) (501483824711/1000000000000 : ℝ) (250735819629/500000000000 : ℝ) (501471639267/1000000000000 : ℝ) (25073886599/50000000000 : ℝ) (501477731989/1000000000000 : ℝ) (501477731943/1000000000000 : ℝ) (31342358247/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16773/131072 : ℝ))) 4 (25073886599/50000000000 : ℝ) (501477731989/1000000000000 : ℝ) (501477731943/1000000000000 : ℝ) (31342358247/62500000000 : ℝ) (501477731961/1000000000000 : ℝ) (501477731971/1000000000000 : ℝ) (501477731961/1000000000000 : ℝ) (501477731971/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16773/131072 : ℝ))) 5 (501477731961/1000000000000 : ℝ) (501477731971/1000000000000 : ℝ) (501477731961/1000000000000 : ℝ) (501477731971/1000000000000 : ℝ) (501477731961/1000000000000 : ℝ) (501477731971/1000000000000 : ℝ) (501477731961/1000000000000 : ℝ) (501477731971/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16773/131072 : ℝ))) 6 (501477731961/1000000000000 : ℝ) (501477731971/1000000000000 : ℝ) (501477731961/1000000000000 : ℝ) (501477731971/1000000000000 : ℝ) (501477731961/1000000000000 : ℝ) (501477731971/1000000000000 : ℝ) (501477731961/1000000000000 : ℝ) (501477731971/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16773/131072 : ℝ))) 7 (501477731961/1000000000000 : ℝ) (501477731971/1000000000000 : ℝ) (501477731961/1000000000000 : ℝ) (501477731971/1000000000000 : ℝ) (501477731961/1000000000000 : ℝ) (501477731971/1000000000000 : ℝ) (501477731961/1000000000000 : ℝ) (501477731971/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16773/131072 : ℝ)) hmem 8 (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ) (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16773/131072 : ℝ))) hcmem 8 (501477731961/1000000000000 : ℝ) (501477731971/1000000000000 : ℝ) (501477731961/1000000000000 : ℝ) (501477731971/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16773/131072 : ℝ)) (124006221719/125000000000 : ℝ) (198409954751/200000000000 : ℝ) (501477731961/1000000000000 : ℝ) (501477731971/1000000000000 : ℝ) (49627007143/62500000000 : ℝ) (794032114307/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1019_exp_lower
  have heNumeric : (1027451016121/500000000000 : ℝ)/4 ≤ Real.exp (-85256471959421/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451016121/500000000000 : ℝ)/4 ≤ Real.exp ((67091/524288 : ℝ)-(794032114307/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67091/524288 : ℝ) (16773/131072 : ℝ) (794032114307/1000000000000 : ℝ) (1027451016121/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1020; no trusted numerical premise.
theorem cover8_leaf1020_exp_radius : (998002470506863817/1000000000000000000 : ℝ) ≤ Real.exp ((-67093/4194304 : ℝ)/8) ∧ Real.exp ((-67093/4194304 : ℝ)/8) ≤ (499001235253431909/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67093/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1020_exp_lower : (920113476048470283/1000000000000000000 : ℝ) ≤ Real.exp ((-21314117891659/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314117891659/32000000000000 : ℝ)/8) ≤ (230028369012117571/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314117891659/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1020_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902038547/1000000000000 : ℝ) ≤ 4*Real.exp (16773/131072 : ℝ)*Real.exp (-mu (radius 8 (67093/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902038547/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67093/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1020_exp_radius
  have hrNumeric : (984131042299/1000000000000 : ℝ) ≤ Real.exp (-67093/4194304 : ℝ) ∧ Real.exp (-67093/4194304 : ℝ) ≤ (9841310423/10000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984131042299/1000000000000 : ℝ) ≤ (radius 8 (67093/524288 : ℝ)) ∧ (radius 8 (67093/524288 : ℝ)) ≤ (9841310423/10000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67093/524288 : ℝ)) (984131042299/1000000000000 : ℝ) (9841310423/10000000000 : ℝ) (44360801659/250000000000 : ℝ) (177443206643/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67093/524288 : ℝ)) (984131042299/1000000000000 : ℝ) (9841310423/10000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67093/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984131042299/1000000000000 : ℝ) (9841310423/10000000000 : ℝ) (992065521149/1000000000000 : ℝ) (19841310423/20000000000 : ℝ) (198406758181/200000000000 : ℝ) (992033790907/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67093/524288 : ℝ)) 1 (992065521149/1000000000000 : ℝ) (19841310423/20000000000 : ℝ) (198406758181/200000000000 : ℝ) (992033790907/1000000000000 : ℝ) (992049656027/1000000000000 : ℝ) (992049656029/1000000000000 : ℝ) (9920496559/10000000000 : ℝ) (496024827951/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67093/524288 : ℝ)) 2 (992049656027/1000000000000 : ℝ) (992049656029/1000000000000 : ℝ) (9920496559/10000000000 : ℝ) (496024827951/500000000000 : ℝ) (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ) (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67093/524288 : ℝ)) 3 (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ) (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ) (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ) (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67093/524288 : ℝ)) 4 (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ) (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ) (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ) (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67093/524288 : ℝ)) 5 (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ) (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ) (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ) (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67093/524288 : ℝ)) 6 (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ) (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ) (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ) (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67093/524288 : ℝ)) 7 (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ) (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ) (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ) (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67093/524288 : ℝ))) (44360801659/250000000000 : ℝ) (177443206643/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67093/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44360801659/250000000000 : ℝ) (177443206643/1000000000000 : ℝ) (294360801659/500000000000 : ℝ) (294360801661/500000000000 : ℝ) (421240081943/1000000000000 : ℝ) (421240081953/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67093/524288 : ℝ))) 1 (294360801659/500000000000 : ℝ) (294360801661/500000000000 : ℝ) (421240081943/1000000000000 : ℝ) (421240081953/1000000000000 : ℝ) (50498084263/100000000000 : ℝ) (252490421319/500000000000 : ℝ) (19919563707/40000000000 : ℝ) (497989092683/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67093/524288 : ℝ))) 2 (50498084263/100000000000 : ℝ) (252490421319/500000000000 : ℝ) (19919563707/40000000000 : ℝ) (497989092683/1000000000000 : ℝ) (125371241913/250000000000 : ℝ) (501484967661/1000000000000 : ℝ) (501472782551/1000000000000 : ℝ) (3134204891/6250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67093/524288 : ℝ))) 3 (125371241913/250000000000 : ℝ) (501484967661/1000000000000 : ℝ) (501472782551/1000000000000 : ℝ) (3134204891/6250000000 : ℝ) (501478875101/1000000000000 : ℝ) (501478875111/1000000000000 : ℝ) (62684859383/125000000000 : ℝ) (250739437537/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67093/524288 : ℝ))) 4 (501478875101/1000000000000 : ℝ) (501478875111/1000000000000 : ℝ) (62684859383/125000000000 : ℝ) (250739437537/500000000000 : ℝ) (250739437541/500000000000 : ℝ) (501478875093/1000000000000 : ℝ) (250739437541/500000000000 : ℝ) (501478875093/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67093/524288 : ℝ))) 5 (250739437541/500000000000 : ℝ) (501478875093/1000000000000 : ℝ) (250739437541/500000000000 : ℝ) (501478875093/1000000000000 : ℝ) (250739437541/500000000000 : ℝ) (501478875093/1000000000000 : ℝ) (250739437541/500000000000 : ℝ) (501478875093/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67093/524288 : ℝ))) 6 (250739437541/500000000000 : ℝ) (501478875093/1000000000000 : ℝ) (250739437541/500000000000 : ℝ) (501478875093/1000000000000 : ℝ) (250739437541/500000000000 : ℝ) (501478875093/1000000000000 : ℝ) (250739437541/500000000000 : ℝ) (501478875093/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67093/524288 : ℝ))) 7 (250739437541/500000000000 : ℝ) (501478875093/1000000000000 : ℝ) (250739437541/500000000000 : ℝ) (501478875093/1000000000000 : ℝ) (250739437541/500000000000 : ℝ) (501478875093/1000000000000 : ℝ) (250739437541/500000000000 : ℝ) (501478875093/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67093/524288 : ℝ)) hmem 8 (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ) (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67093/524288 : ℝ))) hcmem 8 (250739437541/500000000000 : ℝ) (501478875093/1000000000000 : ℝ) (250739437541/500000000000 : ℝ) (501478875093/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67093/524288 : ℝ)) (992049655963/1000000000000 : ℝ) (496024827983/500000000000 : ℝ) (250739437541/500000000000 : ℝ) (501478875093/1000000000000 : ℝ) (397017009283/500000000000 : ℝ) (794034018587/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1020_exp_lower
  have heNumeric : (2054902038547/1000000000000 : ℝ)/4 ≤ Real.exp (-21314117891659/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902038547/1000000000000 : ℝ)/4 ≤ Real.exp ((16773/131072 : ℝ)-(794034018587/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16773/131072 : ℝ) (67093/524288 : ℝ) (794034018587/1000000000000 : ℝ) (2054902038547/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1021; no trusted numerical premise.
theorem cover8_leaf1021_exp_radius : (99800244076407289/100000000000000000 : ℝ) ≤ Real.exp ((-33547/2097152 : ℝ)/8) ∧ Real.exp ((-33547/2097152 : ℝ)/8) ≤ (998002440764072891/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33547/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1021_exp_lower : (920113476404972023/1000000000000000000 : ℝ) ≤ Real.exp ((-85256471169883/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256471169883/128000000000000 : ℝ)/8) ≤ (115014184550621503/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256471169883/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1021_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902044917/1000000000000 : ℝ) ≤ 4*Real.exp (67093/524288 : ℝ)*Real.exp (-mu (radius 8 (33547/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902044917/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33547/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1021_exp_radius
  have hrNumeric : (61508175479/62500000000 : ℝ) ≤ Real.exp (-33547/2097152 : ℝ) ∧ Real.exp (-33547/2097152 : ℝ) ≤ (196826161533/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61508175479/62500000000 : ℝ) ≤ (radius 8 (33547/262144 : ℝ)) ∧ (radius 8 (33547/262144 : ℝ)) ≤ (196826161533/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33547/262144 : ℝ)) (61508175479/62500000000 : ℝ) (196826161533/200000000000 : ℝ) (88722253979/500000000000 : ℝ) (35488901593/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33547/262144 : ℝ)) (61508175479/62500000000 : ℝ) (196826161533/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33547/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61508175479/62500000000 : ℝ) (196826161533/200000000000 : ℝ) (124008175479/125000000000 : ℝ) (992065403833/1000000000000 : ℝ) (496016836323/500000000000 : ℝ) (992033672647/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33547/262144 : ℝ)) 1 (124008175479/125000000000 : ℝ) (992065403833/1000000000000 : ℝ) (496016836323/500000000000 : ℝ) (992033672647/1000000000000 : ℝ) (992049538239/1000000000000 : ℝ) (3100154807/3125000000 : ℝ) (15500774033/15625000000 : ℝ) (496024769057/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33547/262144 : ℝ)) 2 (992049538239/1000000000000 : ℝ) (3100154807/3125000000 : ℝ) (15500774033/15625000000 : ℝ) (496024769057/500000000000 : ℝ) (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ) (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33547/262144 : ℝ)) 3 (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ) (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ) (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ) (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33547/262144 : ℝ)) 4 (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ) (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ) (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ) (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33547/262144 : ℝ)) 5 (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ) (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ) (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ) (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33547/262144 : ℝ)) 6 (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ) (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ) (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ) (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33547/262144 : ℝ)) 7 (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ) (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ) (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ) (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33547/262144 : ℝ))) (88722253979/500000000000 : ℝ) (35488901593/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33547/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88722253979/500000000000 : ℝ) (35488901593/200000000000 : ℝ) (588722253979/1000000000000 : ℝ) (588722253983/1000000000000 : ℝ) (421241626573/1000000000000 : ℝ) (210620813291/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33547/262144 : ℝ))) 1 (588722253979/1000000000000 : ℝ) (588722253983/1000000000000 : ℝ) (421241626573/1000000000000 : ℝ) (210620813291/500000000000 : ℝ) (126245485069/250000000000 : ℝ) (504981940283/1000000000000 : ℝ) (248995140447/500000000000 : ℝ) (248995140451/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33547/262144 : ℝ))) 2 (126245485069/250000000000 : ℝ) (504981940283/1000000000000 : ℝ) (248995140447/500000000000 : ℝ) (248995140451/500000000000 : ℝ) (100297222117/200000000000 : ℝ) (501486110593/1000000000000 : ℝ) (501473925827/1000000000000 : ℝ) (100294785167/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33547/262144 : ℝ))) 3 (100297222117/200000000000 : ℝ) (501486110593/1000000000000 : ℝ) (501473925827/1000000000000 : ℝ) (100294785167/200000000000 : ℝ) (250740009103/500000000000 : ℝ) (250740009107/500000000000 : ℝ) (62685002271/125000000000 : ℝ) (501480018177/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33547/262144 : ℝ))) 4 (250740009103/500000000000 : ℝ) (250740009107/500000000000 : ℝ) (62685002271/125000000000 : ℝ) (501480018177/1000000000000 : ℝ) (501480018187/1000000000000 : ℝ) (125370004549/250000000000 : ℝ) (250740009093/500000000000 : ℝ) (125370004549/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33547/262144 : ℝ))) 5 (501480018187/1000000000000 : ℝ) (125370004549/250000000000 : ℝ) (250740009093/500000000000 : ℝ) (125370004549/250000000000 : ℝ) (250740009093/500000000000 : ℝ) (125370004549/250000000000 : ℝ) (250740009093/500000000000 : ℝ) (125370004549/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33547/262144 : ℝ))) 6 (250740009093/500000000000 : ℝ) (125370004549/250000000000 : ℝ) (250740009093/500000000000 : ℝ) (125370004549/250000000000 : ℝ) (250740009093/500000000000 : ℝ) (125370004549/250000000000 : ℝ) (250740009093/500000000000 : ℝ) (125370004549/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33547/262144 : ℝ))) 7 (250740009093/500000000000 : ℝ) (125370004549/250000000000 : ℝ) (250740009093/500000000000 : ℝ) (125370004549/250000000000 : ℝ) (250740009093/500000000000 : ℝ) (125370004549/250000000000 : ℝ) (250740009093/500000000000 : ℝ) (125370004549/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33547/262144 : ℝ)) hmem 8 (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ) (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33547/262144 : ℝ))) hcmem 8 (250740009093/500000000000 : ℝ) (125370004549/250000000000 : ℝ) (250740009093/500000000000 : ℝ) (125370004549/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33547/262144 : ℝ)) (39681981527/40000000000 : ℝ) (992049538177/1000000000000 : ℝ) (250740009093/500000000000 : ℝ) (125370004549/250000000000 : ℝ) (397017961409/500000000000 : ℝ) (198508980709/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1021_exp_lower
  have heNumeric : (2054902044917/1000000000000 : ℝ)/4 ≤ Real.exp (-85256471169883/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902044917/1000000000000 : ℝ)/4 ≤ Real.exp ((67093/524288 : ℝ)-(198508980709/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67093/524288 : ℝ) (33547/262144 : ℝ) (198508980709/250000000000 : ℝ) (2054902044917/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1022; no trusted numerical premise.
theorem cover8_leaf1022_exp_radius : (19960048220425657/20000000000000000 : ℝ) ≤ Real.exp ((-67095/4194304 : ℝ)/8) ∧ Real.exp ((-67095/4194304 : ℝ)/8) ≤ (998002411021282851/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67095/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1022_exp_lower : (230028369190857251/250000000000000000 : ℝ) ≤ Real.exp ((-42628235385477/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628235385477/64000000000000 : ℝ)/8) ≤ (184022695352685801/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628235385477/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1022_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902051321/1000000000000 : ℝ) ≤ 4*Real.exp (33547/262144 : ℝ)*Real.exp (-mu (radius 8 (67095/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902051321/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67095/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1022_exp_radius
  have hrNumeric : (984130573029/1000000000000 : ℝ) ≤ Real.exp (-67095/4194304 : ℝ) ∧ Real.exp (-67095/4194304 : ℝ) ≤ (98413057303/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984130573029/1000000000000 : ℝ) ≤ (radius 8 (67095/524288 : ℝ)) ∧ (radius 8 (67095/524288 : ℝ)) ≤ (98413057303/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67095/524288 : ℝ)) (984130573029/1000000000000 : ℝ) (98413057303/100000000000 : ℝ) (17744580927/100000000000 : ℝ) (44361452319/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67095/524288 : ℝ)) (984130573029/1000000000000 : ℝ) (98413057303/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67095/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984130573029/1000000000000 : ℝ) (98413057303/100000000000 : ℝ) (496032643257/500000000000 : ℝ) (198413057303/200000000000 : ℝ) (496016777193/500000000000 : ℝ) (248008388597/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67095/524288 : ℝ)) 1 (496032643257/500000000000 : ℝ) (198413057303/200000000000 : ℝ) (496016777193/500000000000 : ℝ) (248008388597/250000000000 : ℝ) (19840988409/20000000000 : ℝ) (248012355113/250000000000 : ℝ) (992049420323/1000000000000 : ℝ) (39681976813/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67095/524288 : ℝ)) 2 (19840988409/20000000000 : ℝ) (248012355113/250000000000 : ℝ) (992049420323/1000000000000 : ℝ) (39681976813/40000000000 : ℝ) (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ) (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67095/524288 : ℝ)) 3 (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ) (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ) (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ) (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67095/524288 : ℝ)) 4 (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ) (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ) (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ) (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67095/524288 : ℝ)) 5 (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ) (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ) (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ) (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67095/524288 : ℝ)) 6 (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ) (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ) (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ) (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67095/524288 : ℝ)) 7 (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ) (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ) (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ) (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67095/524288 : ℝ))) (17744580927/100000000000 : ℝ) (44361452319/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67095/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17744580927/100000000000 : ℝ) (44361452319/250000000000 : ℝ) (117744580927/200000000000 : ℝ) (294361452319/500000000000 : ℝ) (84248634237/200000000000 : ℝ) (421243171193/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67095/524288 : ℝ))) 1 (117744580927/200000000000 : ℝ) (294361452319/500000000000 : ℝ) (84248634237/200000000000 : ℝ) (421243171193/1000000000000 : ℝ) (50498303791/100000000000 : ℝ) (126245759479/250000000000 : ℝ) (497991469101/1000000000000 : ℝ) (124497867277/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67095/524288 : ℝ))) 2 (50498303791/100000000000 : ℝ) (126245759479/250000000000 : ℝ) (497991469101/1000000000000 : ℝ) (124497867277/250000000000 : ℝ) (100297450701/200000000000 : ℝ) (62685906689/125000000000 : ℝ) (501475069091/1000000000000 : ℝ) (250737534549/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67095/524288 : ℝ))) 3 (100297450701/200000000000 : ℝ) (62685906689/125000000000 : ℝ) (501475069091/1000000000000 : ℝ) (250737534549/500000000000 : ℝ) (250740580649/500000000000 : ℝ) (100296232261/200000000000 : ℝ) (25074058063/50000000000 : ℝ) (125370290317/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67095/524288 : ℝ))) 4 (250740580649/500000000000 : ℝ) (100296232261/200000000000 : ℝ) (25074058063/50000000000 : ℝ) (125370290317/250000000000 : ℝ) (501481161279/1000000000000 : ℝ) (501481161287/1000000000000 : ℝ) (250740580639/500000000000 : ℝ) (501481161287/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67095/524288 : ℝ))) 5 (501481161279/1000000000000 : ℝ) (501481161287/1000000000000 : ℝ) (250740580639/500000000000 : ℝ) (501481161287/1000000000000 : ℝ) (250740580639/500000000000 : ℝ) (501481161287/1000000000000 : ℝ) (250740580639/500000000000 : ℝ) (501481161287/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67095/524288 : ℝ))) 6 (250740580639/500000000000 : ℝ) (501481161287/1000000000000 : ℝ) (250740580639/500000000000 : ℝ) (501481161287/1000000000000 : ℝ) (250740580639/500000000000 : ℝ) (501481161287/1000000000000 : ℝ) (250740580639/500000000000 : ℝ) (501481161287/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67095/524288 : ℝ))) 7 (250740580639/500000000000 : ℝ) (501481161287/1000000000000 : ℝ) (250740580639/500000000000 : ℝ) (501481161287/1000000000000 : ℝ) (250740580639/500000000000 : ℝ) (501481161287/1000000000000 : ℝ) (250740580639/500000000000 : ℝ) (501481161287/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67095/524288 : ℝ)) hmem 8 (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ) (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67095/524288 : ℝ))) hcmem 8 (250740580639/500000000000 : ℝ) (501481161287/1000000000000 : ℝ) (250740580639/500000000000 : ℝ) (501481161287/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67095/524288 : ℝ)) (496024710193/500000000000 : ℝ) (992049420389/1000000000000 : ℝ) (250740580639/500000000000 : ℝ) (501481161287/1000000000000 : ℝ) (15880756541/20000000000 : ℝ) (198509456767/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1022_exp_lower
  have heNumeric : (2054902051321/1000000000000 : ℝ)/4 ≤ Real.exp (-42628235385477/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902051321/1000000000000 : ℝ)/4 ≤ Real.exp ((33547/262144 : ℝ)-(198509456767/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33547/262144 : ℝ) (67095/524288 : ℝ) (198509456767/250000000000 : ℝ) (2054902051321/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1023; no trusted numerical premise.
theorem cover8_leaf1023_exp_radius : (998002381278493697/1000000000000000000 : ℝ) ≤ Real.exp ((-8387/524288 : ℝ)/8) ∧ Real.exp ((-8387/524288 : ℝ)/8) ≤ (499001190639246849/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8387/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1023_exp_lower : (920113477123841227/1000000000000000000 : ℝ) ≤ Real.exp ((-85256470369849/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256470369849/128000000000000 : ℝ)/8) ≤ (230028369280960307/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256470369849/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1023_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (12843137861/6250000000 : ℝ) ≤ 4*Real.exp (67095/524288 : ℝ)*Real.exp (-mu (radius 8 (8387/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (12843137861/6250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8387/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1023_exp_radius
  have hrNumeric : (492065169197/500000000000 : ℝ) ≤ Real.exp (-8387/524288 : ℝ) ∧ Real.exp (-8387/524288 : ℝ) ≤ (196826067679/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492065169197/500000000000 : ℝ) ≤ (radius 8 (8387/65536 : ℝ)) ∧ (radius 8 (8387/65536 : ℝ)) ≤ (196826067679/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8387/65536 : ℝ)) (492065169197/500000000000 : ℝ) (196826067679/200000000000 : ℝ) (44361777643/250000000000 : ℝ) (177447110579/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8387/65536 : ℝ)) (492065169197/500000000000 : ℝ) (196826067679/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8387/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492065169197/500000000000 : ℝ) (196826067679/200000000000 : ℝ) (992065169197/1000000000000 : ℝ) (496032584599/500000000000 : ℝ) (992033436127/1000000000000 : ℝ) (31001044879/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8387/65536 : ℝ)) 1 (992065169197/1000000000000 : ℝ) (496032584599/500000000000 : ℝ) (992033436127/1000000000000 : ℝ) (31001044879/31250000000 : ℝ) (496024651331/500000000000 : ℝ) (992049302663/1000000000000 : ℝ) (198409860507/200000000000 : ℝ) (992049302537/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8387/65536 : ℝ)) 2 (496024651331/500000000000 : ℝ) (992049302663/1000000000000 : ℝ) (198409860507/200000000000 : ℝ) (992049302537/1000000000000 : ℝ) (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ) (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8387/65536 : ℝ)) 3 (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ) (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ) (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ) (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8387/65536 : ℝ)) 4 (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ) (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ) (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ) (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8387/65536 : ℝ)) 5 (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ) (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ) (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ) (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8387/65536 : ℝ)) 6 (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ) (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ) (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ) (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8387/65536 : ℝ)) 7 (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ) (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ) (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ) (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8387/65536 : ℝ))) (44361777643/250000000000 : ℝ) (177447110579/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8387/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44361777643/250000000000 : ℝ) (177447110579/1000000000000 : ℝ) (294361777643/500000000000 : ℝ) (58872355529/100000000000 : ℝ) (421244715779/1000000000000 : ℝ) (105311178947/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8387/65536 : ℝ))) 1 (294361777643/500000000000 : ℝ) (58872355529/100000000000 : ℝ) (421244715779/1000000000000 : ℝ) (105311178947/250000000000 : ℝ) (126246033883/250000000000 : ℝ) (504984135539/1000000000000 : ℝ) (248996328647/500000000000 : ℝ) (248996328651/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8387/65536 : ℝ))) 2 (126246033883/250000000000 : ℝ) (504984135539/1000000000000 : ℝ) (248996328647/500000000000 : ℝ) (248996328651/500000000000 : ℝ) (501488396413/1000000000000 : ℝ) (501488396421/1000000000000 : ℝ) (250738106171/500000000000 : ℝ) (10029524247/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8387/65536 : ℝ))) 3 (501488396413/1000000000000 : ℝ) (501488396421/1000000000000 : ℝ) (250738106171/500000000000 : ℝ) (10029524247/20000000000 : ℝ) (501482304377/1000000000000 : ℝ) (250741152193/500000000000 : ℝ) (25074115217/50000000000 : ℝ) (501482304349/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8387/65536 : ℝ))) 4 (501482304377/1000000000000 : ℝ) (250741152193/500000000000 : ℝ) (25074115217/50000000000 : ℝ) (501482304349/1000000000000 : ℝ) (250741152179/500000000000 : ℝ) (31342644023/62500000000 : ℝ) (250741152179/500000000000 : ℝ) (31342644023/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8387/65536 : ℝ))) 5 (250741152179/500000000000 : ℝ) (31342644023/62500000000 : ℝ) (250741152179/500000000000 : ℝ) (31342644023/62500000000 : ℝ) (250741152179/500000000000 : ℝ) (31342644023/62500000000 : ℝ) (250741152179/500000000000 : ℝ) (31342644023/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8387/65536 : ℝ))) 6 (250741152179/500000000000 : ℝ) (31342644023/62500000000 : ℝ) (250741152179/500000000000 : ℝ) (31342644023/62500000000 : ℝ) (250741152179/500000000000 : ℝ) (31342644023/62500000000 : ℝ) (250741152179/500000000000 : ℝ) (31342644023/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8387/65536 : ℝ))) 7 (250741152179/500000000000 : ℝ) (31342644023/62500000000 : ℝ) (250741152179/500000000000 : ℝ) (31342644023/62500000000 : ℝ) (250741152179/500000000000 : ℝ) (31342644023/62500000000 : ℝ) (250741152179/500000000000 : ℝ) (31342644023/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8387/65536 : ℝ)) hmem 8 (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ) (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8387/65536 : ℝ))) hcmem 8 (250741152179/500000000000 : ℝ) (31342644023/62500000000 : ℝ) (250741152179/500000000000 : ℝ) (31342644023/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8387/65536 : ℝ)) (496024651299/500000000000 : ℝ) (4960246513/5000000000 : ℝ) (250741152179/500000000000 : ℝ) (31342644023/62500000000 : ℝ) (158807946253/200000000000 : ℝ) (794039731283/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1023_exp_lower
  have heNumeric : (12843137861/6250000000 : ℝ)/4 ≤ Real.exp (-85256470369849/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (12843137861/6250000000 : ℝ)/4 ≤ Real.exp ((67095/524288 : ℝ)-(794039731283/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67095/524288 : ℝ) (8387/65536 : ℝ) (794039731283/1000000000000 : ℝ) (12843137861/6250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1024; no trusted numerical premise.
theorem cover8_leaf1024_exp_radius : (998002351535705429/1000000000000000000 : ℝ) ≤ Real.exp ((-67097/4194304 : ℝ)/8) ∧ Real.exp ((-67097/4194304 : ℝ)/8) ≤ (99800235153570543/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67097/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1024_exp_lower : (230028369371667187/250000000000000000 : ℝ) ≤ Real.exp ((-10657058745757/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657058745757/16000000000000 : ℝ)/8) ≤ (920113477486668749/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657058745757/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1024_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902064243/1000000000000 : ℝ) ≤ 4*Real.exp (8387/65536 : ℝ)*Real.exp (-mu (radius 8 (67097/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902064243/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67097/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1024_exp_radius
  have hrNumeric : (984130103759/1000000000000 : ℝ) ≤ Real.exp (-67097/4194304 : ℝ) ∧ Real.exp (-67097/4194304 : ℝ) ≤ (12301626297/12500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984130103759/1000000000000 : ℝ) ≤ (radius 8 (67097/524288 : ℝ)) ∧ (radius 8 (67097/524288 : ℝ)) ≤ (12301626297/12500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67097/524288 : ℝ)) (984130103759/1000000000000 : ℝ) (12301626297/12500000000 : ℝ) (22181051483/125000000000 : ℝ) (177448411871/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67097/524288 : ℝ)) (984130103759/1000000000000 : ℝ) (12301626297/12500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67097/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984130103759/1000000000000 : ℝ) (12301626297/12500000000 : ℝ) (992065051879/1000000000000 : ℝ) (24801626297/25000000000 : ℝ) (992033317867/1000000000000 : ℝ) (248008329467/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67097/524288 : ℝ)) 1 (992065051879/1000000000000 : ℝ) (24801626297/25000000000 : ℝ) (992033317867/1000000000000 : ℝ) (248008329467/250000000000 : ℝ) (992049184873/1000000000000 : ℝ) (496024592437/500000000000 : ℝ) (496024592373/500000000000 : ℝ) (248012296187/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67097/524288 : ℝ)) 2 (992049184873/1000000000000 : ℝ) (496024592437/500000000000 : ℝ) (496024592373/500000000000 : ℝ) (248012296187/250000000000 : ℝ) (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ) (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67097/524288 : ℝ)) 3 (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ) (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ) (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ) (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67097/524288 : ℝ)) 4 (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ) (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ) (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ) (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67097/524288 : ℝ)) 5 (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ) (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ) (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ) (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67097/524288 : ℝ)) 6 (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ) (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ) (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ) (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67097/524288 : ℝ)) 7 (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ) (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ) (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ) (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67097/524288 : ℝ))) (22181051483/125000000000 : ℝ) (177448411871/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67097/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22181051483/125000000000 : ℝ) (177448411871/1000000000000 : ℝ) (147181051483/250000000000 : ℝ) (36795262871/62500000000 : ℝ) (105311565089/250000000000 : ℝ) (84249252073/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67097/524288 : ℝ))) 1 (147181051483/250000000000 : ℝ) (36795262871/62500000000 : ℝ) (105311565089/250000000000 : ℝ) (84249252073/200000000000 : ℝ) (63123154143/125000000000 : ℝ) (504985233151/1000000000000 : ℝ) (497993845473/1000000000000 : ℝ) (497993845481/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67097/524288 : ℝ))) 2 (63123154143/125000000000 : ℝ) (504985233151/1000000000000 : ℝ) (497993845473/1000000000000 : ℝ) (497993845481/1000000000000 : ℝ) (125372384827/250000000000 : ℝ) (125372384829/250000000000 : ℝ) (25073867779/50000000000 : ℝ) (501477355589/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67097/524288 : ℝ))) 3 (125372384827/250000000000 : ℝ) (125372384829/250000000000 : ℝ) (25073867779/50000000000 : ℝ) (501477355589/1000000000000 : ℝ) (125370861861/250000000000 : ℝ) (501483447453/1000000000000 : ℝ) (250741723703/500000000000 : ℝ) (62685430927/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67097/524288 : ℝ))) 4 (125370861861/250000000000 : ℝ) (501483447453/1000000000000 : ℝ) (250741723703/500000000000 : ℝ) (62685430927/125000000000 : ℝ) (20059337897/40000000000 : ℝ) (100296689487/200000000000 : ℝ) (3917839433/7812500000 : ℝ) (100296689487/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67097/524288 : ℝ))) 5 (20059337897/40000000000 : ℝ) (100296689487/200000000000 : ℝ) (3917839433/7812500000 : ℝ) (100296689487/200000000000 : ℝ) (3917839433/7812500000 : ℝ) (100296689487/200000000000 : ℝ) (3917839433/7812500000 : ℝ) (100296689487/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67097/524288 : ℝ))) 6 (3917839433/7812500000 : ℝ) (100296689487/200000000000 : ℝ) (3917839433/7812500000 : ℝ) (100296689487/200000000000 : ℝ) (3917839433/7812500000 : ℝ) (100296689487/200000000000 : ℝ) (3917839433/7812500000 : ℝ) (100296689487/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67097/524288 : ℝ))) 7 (3917839433/7812500000 : ℝ) (100296689487/200000000000 : ℝ) (3917839433/7812500000 : ℝ) (100296689487/200000000000 : ℝ) (3917839433/7812500000 : ℝ) (100296689487/200000000000 : ℝ) (3917839433/7812500000 : ℝ) (100296689487/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67097/524288 : ℝ)) hmem 8 (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ) (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67097/524288 : ℝ))) hcmem 8 (3917839433/7812500000 : ℝ) (100296689487/200000000000 : ℝ) (3917839433/7812500000 : ℝ) (100296689487/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67097/524288 : ℝ)) (992049184809/1000000000000 : ℝ) (992049184811/1000000000000 : ℝ) (3917839433/7812500000 : ℝ) (100296689487/200000000000 : ℝ) (794041635457/1000000000000 : ℝ) (794041635477/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1024_exp_lower
  have heNumeric : (2054902064243/1000000000000 : ℝ)/4 ≤ Real.exp (-10657058745757/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902064243/1000000000000 : ℝ)/4 ≤ Real.exp ((8387/65536 : ℝ)-(794041635477/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8387/65536 : ℝ) (67097/524288 : ℝ) (794041635477/1000000000000 : ℝ) (2054902064243/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1000_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1000_certificate
#check SmaleRate.Proofs.cover8_leaf1001_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1001_certificate
#check SmaleRate.Proofs.cover8_leaf1002_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1002_certificate
#check SmaleRate.Proofs.cover8_leaf1003_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1003_certificate
#check SmaleRate.Proofs.cover8_leaf1004_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1004_certificate
#check SmaleRate.Proofs.cover8_leaf1005_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1005_certificate
#check SmaleRate.Proofs.cover8_leaf1006_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1006_certificate
#check SmaleRate.Proofs.cover8_leaf1007_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1007_certificate
#check SmaleRate.Proofs.cover8_leaf1008_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1008_certificate
#check SmaleRate.Proofs.cover8_leaf1009_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1009_certificate
#check SmaleRate.Proofs.cover8_leaf1010_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1010_certificate
#check SmaleRate.Proofs.cover8_leaf1011_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1011_certificate
#check SmaleRate.Proofs.cover8_leaf1012_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1012_certificate
#check SmaleRate.Proofs.cover8_leaf1013_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1013_certificate
#check SmaleRate.Proofs.cover8_leaf1014_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1014_certificate
#check SmaleRate.Proofs.cover8_leaf1015_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1015_certificate
#check SmaleRate.Proofs.cover8_leaf1016_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1016_certificate
#check SmaleRate.Proofs.cover8_leaf1017_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1017_certificate
#check SmaleRate.Proofs.cover8_leaf1018_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1018_certificate
#check SmaleRate.Proofs.cover8_leaf1019_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1019_certificate
#check SmaleRate.Proofs.cover8_leaf1020_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1020_certificate
#check SmaleRate.Proofs.cover8_leaf1021_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1021_certificate
#check SmaleRate.Proofs.cover8_leaf1022_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1022_certificate
#check SmaleRate.Proofs.cover8_leaf1023_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1023_certificate
#check SmaleRate.Proofs.cover8_leaf1024_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1024_certificate
