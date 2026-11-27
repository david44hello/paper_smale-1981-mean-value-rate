/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0825; no trusted numerical premise.
theorem cover8_leaf0825_exp_radius : (499004135184016857/500000000000000000 : ℝ) ≤ Real.exp ((-33449/2097152 : ℝ)/8) ∧ Real.exp ((-33449/2097152 : ℝ)/8) ≤ (199601654073606743/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33449/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0825_exp_lower : (920113448979491489/1000000000000000000 : ℝ) ≤ Real.exp ((-85256501691871/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256501691871/128000000000000 : ℝ)/8) ≤ (92011344897949149/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256501691871/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0825_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901554919/1000000000000 : ℝ) ≤ 4*Real.exp (66897/524288 : ℝ)*Real.exp (-mu (radius 8 (33449/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901554919/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33449/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0825_exp_radius
  have hrNumeric : (246044199303/250000000000 : ℝ) ≤ Real.exp (-33449/2097152 : ℝ) ∧ Real.exp (-33449/2097152 : ℝ) ≤ (984176797213/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246044199303/250000000000 : ℝ) ≤ (radius 8 (33449/262144 : ℝ)) ∧ (radius 8 (33449/262144 : ℝ)) ≤ (984176797213/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33449/262144 : ℝ)) (246044199303/250000000000 : ℝ) (984176797213/1000000000000 : ℝ) (88594627133/500000000000 : ℝ) (177189254273/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33449/262144 : ℝ)) (246044199303/250000000000 : ℝ) (984176797213/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33449/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246044199303/250000000000 : ℝ) (984176797213/1000000000000 : ℝ) (496044199303/500000000000 : ℝ) (992088398607/1000000000000 : ℝ) (248014212951/250000000000 : ℝ) (198411370361/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33449/262144 : ℝ)) 1 (496044199303/500000000000 : ℝ) (992088398607/1000000000000 : ℝ) (248014212951/250000000000 : ℝ) (198411370361/200000000000 : ℝ) (198414525041/200000000000 : ℝ) (496036312603/500000000000 : ℝ) (992072625079/1000000000000 : ℝ) (992072625081/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33449/262144 : ℝ)) 2 (198414525041/200000000000 : ℝ) (496036312603/500000000000 : ℝ) (992072625079/1000000000000 : ℝ) (992072625081/1000000000000 : ℝ) (496036312571/500000000000 : ℝ) (124009078143/125000000000 : ℝ) (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33449/262144 : ℝ)) 3 (496036312571/500000000000 : ℝ) (124009078143/125000000000 : ℝ) (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ) (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ) (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33449/262144 : ℝ)) 4 (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ) (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ) (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ) (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33449/262144 : ℝ)) 5 (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ) (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ) (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ) (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33449/262144 : ℝ)) 6 (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ) (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ) (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ) (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33449/262144 : ℝ)) 7 (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ) (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ) (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ) (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33449/262144 : ℝ))) (88594627133/500000000000 : ℝ) (177189254273/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33449/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88594627133/500000000000 : ℝ) (177189254273/1000000000000 : ℝ) (588594627133/1000000000000 : ℝ) (588594627137/1000000000000 : ℝ) (105234634943/250000000000 : ℝ) (210469269891/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33449/262144 : ℝ))) 1 (588594627133/1000000000000 : ℝ) (588594627137/1000000000000 : ℝ) (105234634943/250000000000 : ℝ) (210469269891/500000000000 : ℝ) (126191645863/250000000000 : ℝ) (25238329173/50000000000 : ℝ) (497757132407/1000000000000 : ℝ) (3888727597/7812500000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33449/262144 : ℝ))) 2 (126191645863/250000000000 : ℝ) (25238329173/50000000000 : ℝ) (497757132407/1000000000000 : ℝ) (3888727597/7812500000 : ℝ) (501261857929/1000000000000 : ℝ) (250630928969/500000000000 : ℝ) (501249605599/1000000000000 : ℝ) (501249605609/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33449/262144 : ℝ))) 3 (501261857929/1000000000000 : ℝ) (250630928969/500000000000 : ℝ) (501249605599/1000000000000 : ℝ) (501249605609/1000000000000 : ℝ) (125313932941/250000000000 : ℝ) (250627865887/500000000000 : ℝ) (250627865863/500000000000 : ℝ) (501255731737/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33449/262144 : ℝ))) 4 (125313932941/250000000000 : ℝ) (250627865887/500000000000 : ℝ) (250627865863/500000000000 : ℝ) (501255731737/1000000000000 : ℝ) (100251146349/200000000000 : ℝ) (125313932939/250000000000 : ℝ) (15664241617/31250000000 : ℝ) (125313932939/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33449/262144 : ℝ))) 5 (100251146349/200000000000 : ℝ) (125313932939/250000000000 : ℝ) (15664241617/31250000000 : ℝ) (125313932939/250000000000 : ℝ) (15664241617/31250000000 : ℝ) (125313932939/250000000000 : ℝ) (15664241617/31250000000 : ℝ) (125313932939/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33449/262144 : ℝ))) 6 (15664241617/31250000000 : ℝ) (125313932939/250000000000 : ℝ) (15664241617/31250000000 : ℝ) (125313932939/250000000000 : ℝ) (15664241617/31250000000 : ℝ) (125313932939/250000000000 : ℝ) (15664241617/31250000000 : ℝ) (125313932939/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33449/262144 : ℝ))) 7 (15664241617/31250000000 : ℝ) (125313932939/250000000000 : ℝ) (15664241617/31250000000 : ℝ) (125313932939/250000000000 : ℝ) (15664241617/31250000000 : ℝ) (125313932939/250000000000 : ℝ) (15664241617/31250000000 : ℝ) (125313932939/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33449/262144 : ℝ)) hmem 8 (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ) (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33449/262144 : ℝ))) hcmem 8 (15664241617/31250000000 : ℝ) (125313932939/250000000000 : ℝ) (15664241617/31250000000 : ℝ) (125313932939/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33449/262144 : ℝ)) (992072625141/1000000000000 : ℝ) (124009078143/125000000000 : ℝ) (15664241617/31250000000 : ℝ) (125313932939/250000000000 : ℝ) (158732464187/200000000000 : ℝ) (793662320957/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0825_exp_lower
  have heNumeric : (2054901554919/1000000000000 : ℝ)/4 ≤ Real.exp (-85256501691871/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901554919/1000000000000 : ℝ)/4 ≤ Real.exp ((66897/524288 : ℝ)-(793662320957/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66897/524288 : ℝ) (33449/262144 : ℝ) (793662320957/1000000000000 : ℝ) (2054901554919/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0826; no trusted numerical premise.
theorem cover8_leaf0826_exp_radius : (499004120312534969/500000000000000000 : ℝ) ≤ Real.exp ((-66899/4194304 : ℝ)/8) ∧ Real.exp ((-66899/4194304 : ℝ)/8) ≤ (998008240625069939/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66899/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0826_exp_lower : (230028362225712453/250000000000000000 : ℝ) ≤ Real.exp ((-42628250888583/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628250888583/64000000000000 : ℝ)/8) ≤ (920113448902849813/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628250888583/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0826_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (41098031071/20000000000 : ℝ) ≤ 4*Real.exp (33449/262144 : ℝ)*Real.exp (-mu (radius 8 (66899/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (41098031071/20000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66899/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0826_exp_radius
  have hrNumeric : (492088281283/500000000000 : ℝ) ≤ Real.exp (-66899/4194304 : ℝ) ∧ Real.exp (-66899/4194304 : ℝ) ≤ (984176562567/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492088281283/500000000000 : ℝ) ≤ (radius 8 (66899/524288 : ℝ)) ∧ (radius 8 (66899/524288 : ℝ)) ≤ (984176562567/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66899/524288 : ℝ)) (492088281283/500000000000 : ℝ) (984176562567/1000000000000 : ℝ) (7087622303/40000000000 : ℝ) (177190557581/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66899/524288 : ℝ)) (492088281283/500000000000 : ℝ) (984176562567/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66899/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492088281283/500000000000 : ℝ) (984176562567/1000000000000 : ℝ) (992088281283/1000000000000 : ℝ) (248022070321/250000000000 : ℝ) (992056733541/1000000000000 : ℝ) (992056733543/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66899/524288 : ℝ)) 1 (992088281283/1000000000000 : ℝ) (248022070321/250000000000 : ℝ) (992056733541/1000000000000 : ℝ) (992056733543/1000000000000 : ℝ) (248018126853/250000000000 : ℝ) (496036253707/500000000000 : ℝ) (496036253643/500000000000 : ℝ) (992072507289/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66899/524288 : ℝ)) 2 (248018126853/250000000000 : ℝ) (496036253707/500000000000 : ℝ) (496036253643/500000000000 : ℝ) (992072507289/1000000000000 : ℝ) (992072507349/1000000000000 : ℝ) (124009063419/125000000000 : ℝ) (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66899/524288 : ℝ)) 3 (992072507349/1000000000000 : ℝ) (124009063419/125000000000 : ℝ) (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ) (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ) (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66899/524288 : ℝ)) 4 (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ) (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ) (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ) (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66899/524288 : ℝ)) 5 (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ) (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ) (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ) (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66899/524288 : ℝ)) 6 (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ) (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ) (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ) (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66899/524288 : ℝ)) 7 (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ) (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ) (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ) (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66899/524288 : ℝ))) (7087622303/40000000000 : ℝ) (177190557581/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66899/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7087622303/40000000000 : ℝ) (177190557581/1000000000000 : ℝ) (588595278787/1000000000000 : ℝ) (588595278791/1000000000000 : ℝ) (105235021967/250000000000 : ℝ) (105235021969/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66899/524288 : ℝ))) 1 (588595278787/1000000000000 : ℝ) (588595278791/1000000000000 : ℝ) (105235021967/250000000000 : ℝ) (105235021969/250000000000 : ℝ) (504767683327/1000000000000 : ℝ) (252383841667/500000000000 : ℝ) (62219790407/125000000000 : ℝ) (7777473801/15625000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66899/524288 : ℝ))) 2 (504767683327/1000000000000 : ℝ) (252383841667/500000000000 : ℝ) (62219790407/125000000000 : ℝ) (7777473801/15625000000 : ℝ) (501263003291/1000000000000 : ℝ) (501263003299/1000000000000 : ℝ) (501250751307/1000000000000 : ℝ) (125312687829/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66899/524288 : ℝ))) 3 (501263003291/1000000000000 : ℝ) (501263003299/1000000000000 : ℝ) (501250751307/1000000000000 : ℝ) (125312687829/250000000000 : ℝ) (501256877299/1000000000000 : ℝ) (125314219327/250000000000 : ℝ) (501256877261/1000000000000 : ℝ) (501256877271/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66899/524288 : ℝ))) 4 (501256877299/1000000000000 : ℝ) (125314219327/250000000000 : ℝ) (501256877261/1000000000000 : ℝ) (501256877271/1000000000000 : ℝ) (3132855483/6250000000 : ℝ) (50125687729/100000000000 : ℝ) (501256877279/1000000000000 : ℝ) (50125687729/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66899/524288 : ℝ))) 5 (3132855483/6250000000 : ℝ) (50125687729/100000000000 : ℝ) (501256877279/1000000000000 : ℝ) (50125687729/100000000000 : ℝ) (501256877279/1000000000000 : ℝ) (50125687729/100000000000 : ℝ) (501256877279/1000000000000 : ℝ) (50125687729/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66899/524288 : ℝ))) 6 (501256877279/1000000000000 : ℝ) (50125687729/100000000000 : ℝ) (501256877279/1000000000000 : ℝ) (50125687729/100000000000 : ℝ) (501256877279/1000000000000 : ℝ) (50125687729/100000000000 : ℝ) (501256877279/1000000000000 : ℝ) (50125687729/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66899/524288 : ℝ))) 7 (501256877279/1000000000000 : ℝ) (50125687729/100000000000 : ℝ) (501256877279/1000000000000 : ℝ) (50125687729/100000000000 : ℝ) (501256877279/1000000000000 : ℝ) (50125687729/100000000000 : ℝ) (501256877279/1000000000000 : ℝ) (50125687729/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66899/524288 : ℝ)) hmem 8 (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ) (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66899/524288 : ℝ))) hcmem 8 (501256877279/1000000000000 : ℝ) (50125687729/100000000000 : ℝ) (501256877279/1000000000000 : ℝ) (50125687729/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66899/524288 : ℝ)) (248018126837/250000000000 : ℝ) (124009063419/125000000000 : ℝ) (501256877279/1000000000000 : ℝ) (50125687729/100000000000 : ℝ) (15873284579/20000000000 : ℝ) (198416057243/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0826_exp_lower
  have heNumeric : (41098031071/20000000000 : ℝ)/4 ≤ Real.exp (-42628250888583/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (41098031071/20000000000 : ℝ)/4 ≤ Real.exp ((33449/262144 : ℝ)-(198416057243/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33449/262144 : ℝ) (66899/524288 : ℝ) (198416057243/250000000000 : ℝ) (41098031071/20000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0827; no trusted numerical premise.
theorem cover8_leaf0827_exp_radius : (998008210882107049/1000000000000000000 : ℝ) ≤ Real.exp ((-16725/1048576 : ℝ)/8) ∧ Real.exp ((-16725/1048576 : ℝ)/8) ≤ (19960164217642141/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16725/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0827_exp_lower : (46005672441425421/50000000000000000 : ℝ) ≤ Real.exp ((-85256501859901/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256501859901/128000000000000 : ℝ)/8) ≤ (920113448828508421/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256501859901/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0827_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450776111/500000000000 : ℝ) ≤ 4*Real.exp (66899/524288 : ℝ)*Real.exp (-mu (radius 8 (16725/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450776111/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16725/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0827_exp_radius
  have hrNumeric : (12302204099/12500000000 : ℝ) ≤ Real.exp (-16725/1048576 : ℝ) ∧ Real.exp (-16725/1048576 : ℝ) ≤ (984176327921/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (12302204099/12500000000 : ℝ) ≤ (radius 8 (16725/131072 : ℝ)) ∧ (radius 8 (16725/131072 : ℝ)) ≤ (984176327921/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16725/131072 : ℝ)) (12302204099/12500000000 : ℝ) (984176327921/1000000000000 : ℝ) (177191860873/1000000000000 : ℝ) (2214898261/12500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16725/131072 : ℝ)) (12302204099/12500000000 : ℝ) (984176327921/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16725/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (12302204099/12500000000 : ℝ) (984176327921/1000000000000 : ℝ) (24802204099/25000000000 : ℝ) (992088163961/1000000000000 : ℝ) (992056615279/1000000000000 : ℝ) (992056615281/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16725/131072 : ℝ)) 1 (24802204099/25000000000 : ℝ) (992088163961/1000000000000 : ℝ) (992056615279/1000000000000 : ℝ) (992056615281/1000000000000 : ℝ) (992072389619/1000000000000 : ℝ) (992072389621/1000000000000 : ℝ) (496036194747/500000000000 : ℝ) (124009048687/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16725/131072 : ℝ)) 2 (992072389619/1000000000000 : ℝ) (992072389621/1000000000000 : ℝ) (496036194747/500000000000 : ℝ) (124009048687/125000000000 : ℝ) (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ) (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16725/131072 : ℝ)) 3 (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ) (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ) (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ) (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16725/131072 : ℝ)) 4 (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ) (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ) (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ) (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16725/131072 : ℝ)) 5 (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ) (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ) (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ) (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16725/131072 : ℝ)) 6 (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ) (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ) (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ) (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16725/131072 : ℝ)) 7 (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ) (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ) (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ) (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16725/131072 : ℝ))) (177191860873/1000000000000 : ℝ) (2214898261/12500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16725/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177191860873/1000000000000 : ℝ) (2214898261/12500000000 : ℝ) (147148982609/250000000000 : ℝ) (14714898261/25000000000 : ℝ) (210470817973/500000000000 : ℝ) (84188327191/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16725/131072 : ℝ))) 1 (147148982609/250000000000 : ℝ) (14714898261/25000000000 : ℝ) (210470817973/500000000000 : ℝ) (84188327191/200000000000 : ℝ) (504768783191/1000000000000 : ℝ) (252384391599/500000000000 : ℝ) (497759514091/1000000000000 : ℝ) (497759514099/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16725/131072 : ℝ))) 2 (504768783191/1000000000000 : ℝ) (252384391599/500000000000 : ℝ) (497759514091/1000000000000 : ℝ) (497759514099/1000000000000 : ℝ) (501264148641/1000000000000 : ℝ) (501264148649/1000000000000 : ℝ) (501251897003/1000000000000 : ℝ) (501251897011/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16725/131072 : ℝ))) 3 (501264148641/1000000000000 : ℝ) (501264148649/1000000000000 : ℝ) (501251897003/1000000000000 : ℝ) (501251897011/1000000000000 : ℝ) (250629011411/500000000000 : ℝ) (50125802283/100000000000 : ℝ) (3916078303/7812500000 : ℝ) (501258022793/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16725/131072 : ℝ))) 4 (250629011411/500000000000 : ℝ) (50125802283/100000000000 : ℝ) (3916078303/7812500000 : ℝ) (501258022793/1000000000000 : ℝ) (501258022803/1000000000000 : ℝ) (125314505703/250000000000 : ℝ) (250629011401/500000000000 : ℝ) (125314505703/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16725/131072 : ℝ))) 5 (501258022803/1000000000000 : ℝ) (125314505703/250000000000 : ℝ) (250629011401/500000000000 : ℝ) (125314505703/250000000000 : ℝ) (250629011401/500000000000 : ℝ) (125314505703/250000000000 : ℝ) (250629011401/500000000000 : ℝ) (125314505703/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16725/131072 : ℝ))) 6 (250629011401/500000000000 : ℝ) (125314505703/250000000000 : ℝ) (250629011401/500000000000 : ℝ) (125314505703/250000000000 : ℝ) (250629011401/500000000000 : ℝ) (125314505703/250000000000 : ℝ) (250629011401/500000000000 : ℝ) (125314505703/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16725/131072 : ℝ))) 7 (250629011401/500000000000 : ℝ) (125314505703/250000000000 : ℝ) (250629011401/500000000000 : ℝ) (125314505703/250000000000 : ℝ) (250629011401/500000000000 : ℝ) (125314505703/250000000000 : ℝ) (250629011401/500000000000 : ℝ) (125314505703/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16725/131072 : ℝ)) hmem 8 (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ) (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16725/131072 : ℝ))) hcmem 8 (250629011401/500000000000 : ℝ) (125314505703/250000000000 : ℝ) (250629011401/500000000000 : ℝ) (125314505703/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16725/131072 : ℝ)) (248018097389/250000000000 : ℝ) (992072389559/1000000000000 : ℝ) (250629011401/500000000000 : ℝ) (125314505703/250000000000 : ℝ) (793666136947/1000000000000 : ℝ) (793666136967/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0827_exp_lower
  have heNumeric : (1027450776111/500000000000 : ℝ)/4 ≤ Real.exp (-85256501859901/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450776111/500000000000 : ℝ)/4 ≤ Real.exp ((66899/524288 : ℝ)-(793666136967/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66899/524288 : ℝ) (16725/131072 : ℝ) (793666136967/1000000000000 : ℝ) (1027450776111/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0828; no trusted numerical premise.
theorem cover8_leaf0828_exp_radius : (499004090569572523/500000000000000000 : ℝ) ≤ Real.exp ((-66901/4194304 : ℝ)/8) ∧ Real.exp ((-66901/4194304 : ℝ)/8) ≤ (998008181139145047/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66901/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0828_exp_lower : (230028362189030567/250000000000000000 : ℝ) ≤ Real.exp ((-4262825097023/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262825097023/6400000000000 : ℝ)/8) ≤ (920113448756122269/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262825097023/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0828_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431346933/62500000000 : ℝ) ≤ 4*Real.exp (16725/131072 : ℝ)*Real.exp (-mu (radius 8 (66901/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (128431346933/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66901/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0828_exp_radius
  have hrNumeric : (492088046637/500000000000 : ℝ) ≤ Real.exp (-66901/4194304 : ℝ) ∧ Real.exp (-66901/4194304 : ℝ) ≤ (39367043731/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492088046637/500000000000 : ℝ) ≤ (radius 8 (66901/524288 : ℝ)) ∧ (radius 8 (66901/524288 : ℝ)) ≤ (39367043731/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66901/524288 : ℝ)) (492088046637/500000000000 : ℝ) (39367043731/40000000000 : ℝ) (88596582081/500000000000 : ℝ) (177193164169/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66901/524288 : ℝ)) (492088046637/500000000000 : ℝ) (39367043731/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66901/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492088046637/500000000000 : ℝ) (39367043731/40000000000 : ℝ) (992088046637/1000000000000 : ℝ) (496044023319/500000000000 : ℝ) (992056497017/1000000000000 : ℝ) (496028248509/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66901/524288 : ℝ)) 1 (992088046637/1000000000000 : ℝ) (496044023319/500000000000 : ℝ) (992056497017/1000000000000 : ℝ) (496028248509/500000000000 : ℝ) (992072271827/1000000000000 : ℝ) (248018067957/250000000000 : ℝ) (992072271701/1000000000000 : ℝ) (992072271703/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66901/524288 : ℝ)) 2 (992072271827/1000000000000 : ℝ) (248018067957/250000000000 : ℝ) (992072271701/1000000000000 : ℝ) (992072271703/1000000000000 : ℝ) (248018067941/250000000000 : ℝ) (496036135883/500000000000 : ℝ) (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66901/524288 : ℝ)) 3 (248018067941/250000000000 : ℝ) (496036135883/500000000000 : ℝ) (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ) (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ) (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66901/524288 : ℝ)) 4 (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ) (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ) (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ) (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66901/524288 : ℝ)) 5 (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ) (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ) (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ) (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66901/524288 : ℝ)) 6 (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ) (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ) (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ) (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66901/524288 : ℝ)) 7 (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ) (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ) (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ) (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66901/524288 : ℝ))) (88596582081/500000000000 : ℝ) (177193164169/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66901/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88596582081/500000000000 : ℝ) (177193164169/1000000000000 : ℝ) (588596582081/1000000000000 : ℝ) (117719316417/200000000000 : ℝ) (420943184007/1000000000000 : ℝ) (26308949001/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66901/524288 : ℝ))) 1 (588596582081/1000000000000 : ℝ) (117719316417/200000000000 : ℝ) (420943184007/1000000000000 : ℝ) (26308949001/62500000000 : ℝ) (126192470761/250000000000 : ℝ) (504769883051/1000000000000 : ℝ) (248880352457/500000000000 : ℝ) (248880352461/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66901/524288 : ℝ))) 2 (126192470761/250000000000 : ℝ) (504769883051/1000000000000 : ℝ) (248880352457/500000000000 : ℝ) (248880352461/500000000000 : ℝ) (501265293979/1000000000000 : ℝ) (501265293987/1000000000000 : ℝ) (501253042687/1000000000000 : ℝ) (100250608539/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66901/524288 : ℝ))) 3 (501265293979/1000000000000 : ℝ) (501265293987/1000000000000 : ℝ) (501253042687/1000000000000 : ℝ) (100250608539/200000000000 : ℝ) (501259168333/1000000000000 : ℝ) (501259168341/1000000000000 : ℝ) (100251833659/200000000000 : ℝ) (31328698019/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66901/524288 : ℝ))) 4 (501259168333/1000000000000 : ℝ) (501259168341/1000000000000 : ℝ) (100251833659/200000000000 : ℝ) (31328698019/62500000000 : ℝ) (250629584157/500000000000 : ℝ) (501259168323/1000000000000 : ℝ) (501259168313/1000000000000 : ℝ) (501259168323/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66901/524288 : ℝ))) 5 (250629584157/500000000000 : ℝ) (501259168323/1000000000000 : ℝ) (501259168313/1000000000000 : ℝ) (501259168323/1000000000000 : ℝ) (501259168313/1000000000000 : ℝ) (501259168323/1000000000000 : ℝ) (501259168313/1000000000000 : ℝ) (501259168323/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66901/524288 : ℝ))) 6 (501259168313/1000000000000 : ℝ) (501259168323/1000000000000 : ℝ) (501259168313/1000000000000 : ℝ) (501259168323/1000000000000 : ℝ) (501259168313/1000000000000 : ℝ) (501259168323/1000000000000 : ℝ) (501259168313/1000000000000 : ℝ) (501259168323/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66901/524288 : ℝ))) 7 (501259168313/1000000000000 : ℝ) (501259168323/1000000000000 : ℝ) (501259168313/1000000000000 : ℝ) (501259168323/1000000000000 : ℝ) (501259168313/1000000000000 : ℝ) (501259168323/1000000000000 : ℝ) (501259168313/1000000000000 : ℝ) (501259168323/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66901/524288 : ℝ)) hmem 8 (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ) (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66901/524288 : ℝ))) hcmem 8 (501259168313/1000000000000 : ℝ) (501259168323/1000000000000 : ℝ) (501259168313/1000000000000 : ℝ) (501259168323/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66901/524288 : ℝ)) (992072271763/1000000000000 : ℝ) (496036135883/500000000000 : ℝ) (501259168313/1000000000000 : ℝ) (501259168323/1000000000000 : ℝ) (396834022463/500000000000 : ℝ) (158733608989/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0828_exp_lower
  have heNumeric : (128431346933/62500000000 : ℝ)/4 ≤ Real.exp (-4262825097023/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431346933/62500000000 : ℝ)/4 ≤ Real.exp ((16725/131072 : ℝ)-(158733608989/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16725/131072 : ℝ) (66901/524288 : ℝ) (158733608989/200000000000 : ℝ) (128431346933/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0829; no trusted numerical premise.
theorem cover8_leaf0829_exp_radius : (998008151396183929/1000000000000000000 : ℝ) ≤ Real.exp ((-33451/2097152 : ℝ)/8) ∧ Real.exp ((-33451/2097152 : ℝ)/8) ≤ (99800815139618393/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33451/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0829_exp_lower : (920113448686956513/1000000000000000000 : ℝ) ≤ Real.exp ((-17051300403487/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051300403487/25600000000000 : ℝ)/8) ≤ (460056724343478257/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051300403487/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0829_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901549693/1000000000000 : ℝ) ≤ 4*Real.exp (66901/524288 : ℝ)*Real.exp (-mu (radius 8 (33451/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901549693/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33451/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0829_exp_radius
  have hrNumeric : (984175858629/1000000000000 : ℝ) ≤ Real.exp (-33451/2097152 : ℝ) ∧ Real.exp (-33451/2097152 : ℝ) ≤ (98417585863/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984175858629/1000000000000 : ℝ) ≤ (radius 8 (33451/262144 : ℝ)) ∧ (radius 8 (33451/262144 : ℝ)) ≤ (98417585863/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33451/262144 : ℝ)) (984175858629/1000000000000 : ℝ) (98417585863/100000000000 : ℝ) (35438893487/200000000000 : ℝ) (88597233721/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33451/262144 : ℝ)) (984175858629/1000000000000 : ℝ) (98417585863/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33451/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984175858629/1000000000000 : ℝ) (98417585863/100000000000 : ℝ) (496043964657/500000000000 : ℝ) (198417585863/200000000000 : ℝ) (198411275751/200000000000 : ℝ) (248014094689/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33451/262144 : ℝ)) 1 (496043964657/500000000000 : ℝ) (198417585863/200000000000 : ℝ) (198411275751/200000000000 : ℝ) (248014094689/250000000000 : ℝ) (496036077017/500000000000 : ℝ) (248018038509/250000000000 : ℝ) (992072153909/1000000000000 : ℝ) (992072153911/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33451/262144 : ℝ)) 2 (496036077017/500000000000 : ℝ) (248018038509/250000000000 : ℝ) (992072153909/1000000000000 : ℝ) (992072153911/1000000000000 : ℝ) (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ) (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33451/262144 : ℝ)) 3 (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ) (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ) (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ) (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33451/262144 : ℝ)) 4 (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ) (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ) (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ) (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33451/262144 : ℝ)) 5 (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ) (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ) (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ) (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33451/262144 : ℝ)) 6 (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ) (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ) (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ) (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33451/262144 : ℝ)) 7 (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ) (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ) (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ) (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33451/262144 : ℝ))) (35438893487/200000000000 : ℝ) (88597233721/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33451/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35438893487/200000000000 : ℝ) (88597233721/500000000000 : ℝ) (588597233717/1000000000000 : ℝ) (588597233721/1000000000000 : ℝ) (420944732043/1000000000000 : ℝ) (105236183013/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33451/262144 : ℝ))) 1 (588597233717/1000000000000 : ℝ) (588597233721/1000000000000 : ℝ) (420944732043/1000000000000 : ℝ) (105236183013/250000000000 : ℝ) (3154818643/6250000000 : ℝ) (504770982887/1000000000000 : ℝ) (497761895717/1000000000000 : ℝ) (19910475829/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33451/262144 : ℝ))) 2 (3154818643/6250000000 : ℝ) (504770982887/1000000000000 : ℝ) (497761895717/1000000000000 : ℝ) (19910475829/40000000000 : ℝ) (250633219649/500000000000 : ℝ) (250633219653/500000000000 : ℝ) (7832096693/15625000000 : ℝ) (501254188361/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33451/262144 : ℝ))) 3 (250633219649/500000000000 : ℝ) (250633219653/500000000000 : ℝ) (7832096693/15625000000 : ℝ) (501254188361/1000000000000 : ℝ) (20050412553/40000000000 : ℝ) (250630156917/500000000000 : ℝ) (501260313787/1000000000000 : ℝ) (501260313797/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33451/262144 : ℝ))) 4 (20050412553/40000000000 : ℝ) (250630156917/500000000000 : ℝ) (501260313787/1000000000000 : ℝ) (501260313797/1000000000000 : ℝ) (250630156903/500000000000 : ℝ) (62657539227/125000000000 : ℝ) (100252062761/200000000000 : ℝ) (62657539227/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33451/262144 : ℝ))) 5 (250630156903/500000000000 : ℝ) (62657539227/125000000000 : ℝ) (100252062761/200000000000 : ℝ) (62657539227/125000000000 : ℝ) (100252062761/200000000000 : ℝ) (62657539227/125000000000 : ℝ) (100252062761/200000000000 : ℝ) (62657539227/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33451/262144 : ℝ))) 6 (100252062761/200000000000 : ℝ) (62657539227/125000000000 : ℝ) (100252062761/200000000000 : ℝ) (62657539227/125000000000 : ℝ) (100252062761/200000000000 : ℝ) (62657539227/125000000000 : ℝ) (100252062761/200000000000 : ℝ) (62657539227/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33451/262144 : ℝ))) 7 (100252062761/200000000000 : ℝ) (62657539227/125000000000 : ℝ) (100252062761/200000000000 : ℝ) (62657539227/125000000000 : ℝ) (100252062761/200000000000 : ℝ) (62657539227/125000000000 : ℝ) (100252062761/200000000000 : ℝ) (62657539227/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33451/262144 : ℝ)) hmem 8 (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ) (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33451/262144 : ℝ))) hcmem 8 (100252062761/200000000000 : ℝ) (62657539227/125000000000 : ℝ) (100252062761/200000000000 : ℝ) (62657539227/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33451/262144 : ℝ)) (992072153971/1000000000000 : ℝ) (496036076987/500000000000 : ℝ) (100252062761/200000000000 : ℝ) (62657539227/125000000000 : ℝ) (396834976437/500000000000 : ℝ) (158733990579/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0829_exp_lower
  have heNumeric : (2054901549693/1000000000000 : ℝ)/4 ≤ Real.exp (-17051300403487/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901549693/1000000000000 : ℝ)/4 ≤ Real.exp ((66901/524288 : ℝ)-(158733990579/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66901/524288 : ℝ) (33451/262144 : ℝ) (158733990579/200000000000 : ℝ) (2054901549693/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0830; no trusted numerical premise.
theorem cover8_leaf0830_exp_radius : (998008121653223699/1000000000000000000 : ℝ) ≤ Real.exp ((-66903/4194304 : ℝ)/8) ∧ Real.exp ((-66903/4194304 : ℝ)/8) ≤ (9980081216532237/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66903/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0830_exp_lower : (9201134486189409/10000000000000000 : ℝ) ≤ Real.exp ((-8525650209313/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525650209313/12800000000000 : ℝ)/8) ≤ (920113448618940901/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525650209313/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0830_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901548477/1000000000000 : ℝ) ≤ 4*Real.exp (33451/262144 : ℝ)*Real.exp (-mu (radius 8 (66903/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901548477/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66903/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0830_exp_radius
  have hrNumeric : (984175623983/1000000000000 : ℝ) ≤ Real.exp (-66903/4194304 : ℝ) ∧ Real.exp (-66903/4194304 : ℝ) ≤ (61510976499/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984175623983/1000000000000 : ℝ) ≤ (radius 8 (66903/524288 : ℝ)) ∧ (radius 8 (66903/524288 : ℝ)) ≤ (61510976499/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66903/524288 : ℝ)) (984175623983/1000000000000 : ℝ) (61510976499/62500000000 : ℝ) (11074735669/62500000000 : ℝ) (177195770711/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66903/524288 : ℝ)) (984175623983/1000000000000 : ℝ) (61510976499/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66903/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984175623983/1000000000000 : ℝ) (61510976499/62500000000 : ℝ) (992087811991/1000000000000 : ℝ) (124010976499/125000000000 : ℝ) (248014065123/250000000000 : ℝ) (496028130247/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66903/524288 : ℝ)) 1 (992087811991/1000000000000 : ℝ) (124010976499/125000000000 : ℝ) (248014065123/250000000000 : ℝ) (496028130247/500000000000 : ℝ) (992072036241/1000000000000 : ℝ) (992072036243/1000000000000 : ℝ) (248018009029/250000000000 : ℝ) (496036018059/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66903/524288 : ℝ)) 2 (992072036241/1000000000000 : ℝ) (992072036243/1000000000000 : ℝ) (248018009029/250000000000 : ℝ) (496036018059/500000000000 : ℝ) (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ) (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66903/524288 : ℝ)) 3 (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ) (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ) (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ) (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66903/524288 : ℝ)) 4 (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ) (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ) (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ) (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66903/524288 : ℝ)) 5 (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ) (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ) (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ) (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66903/524288 : ℝ)) 6 (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ) (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ) (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ) (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66903/524288 : ℝ)) 7 (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ) (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ) (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ) (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66903/524288 : ℝ))) (11074735669/62500000000 : ℝ) (177195770711/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66903/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11074735669/62500000000 : ℝ) (177195770711/1000000000000 : ℝ) (73574735669/125000000000 : ℝ) (147149471339/250000000000 : ℝ) (420946280069/1000000000000 : ℝ) (210473140039/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66903/524288 : ℝ))) 1 (73574735669/125000000000 : ℝ) (147149471339/250000000000 : ℝ) (420946280069/1000000000000 : ℝ) (210473140039/500000000000 : ℝ) (50477208271/100000000000 : ℝ) (504772082717/1000000000000 : ℝ) (497763086513/1000000000000 : ℝ) (497763086521/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66903/524288 : ℝ))) 2 (50477208271/100000000000 : ℝ) (504772082717/1000000000000 : ℝ) (497763086513/1000000000000 : ℝ) (497763086521/1000000000000 : ℝ) (501267584611/1000000000000 : ℝ) (501267584619/1000000000000 : ℝ) (501255334011/1000000000000 : ℝ) (25062766701/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66903/524288 : ℝ))) 3 (501267584611/1000000000000 : ℝ) (501267584619/1000000000000 : ℝ) (501255334011/1000000000000 : ℝ) (25062766701/50000000000 : ℝ) (501261459311/1000000000000 : ℝ) (12531536483/25000000000 : ℝ) (501261459273/1000000000000 : ℝ) (501261459283/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66903/524288 : ℝ))) 4 (501261459311/1000000000000 : ℝ) (12531536483/25000000000 : ℝ) (501261459273/1000000000000 : ℝ) (501261459283/1000000000000 : ℝ) (125315364823/250000000000 : ℝ) (250630729651/500000000000 : ℝ) (501261459291/1000000000000 : ℝ) (250630729651/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66903/524288 : ℝ))) 5 (125315364823/250000000000 : ℝ) (250630729651/500000000000 : ℝ) (501261459291/1000000000000 : ℝ) (250630729651/500000000000 : ℝ) (501261459291/1000000000000 : ℝ) (250630729651/500000000000 : ℝ) (501261459291/1000000000000 : ℝ) (250630729651/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66903/524288 : ℝ))) 6 (501261459291/1000000000000 : ℝ) (250630729651/500000000000 : ℝ) (501261459291/1000000000000 : ℝ) (250630729651/500000000000 : ℝ) (501261459291/1000000000000 : ℝ) (250630729651/500000000000 : ℝ) (501261459291/1000000000000 : ℝ) (250630729651/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66903/524288 : ℝ))) 7 (501261459291/1000000000000 : ℝ) (250630729651/500000000000 : ℝ) (501261459291/1000000000000 : ℝ) (250630729651/500000000000 : ℝ) (501261459291/1000000000000 : ℝ) (250630729651/500000000000 : ℝ) (501261459291/1000000000000 : ℝ) (250630729651/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66903/524288 : ℝ)) hmem 8 (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ) (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66903/524288 : ℝ))) hcmem 8 (501261459291/1000000000000 : ℝ) (250630729651/500000000000 : ℝ) (501261459291/1000000000000 : ℝ) (250630729651/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66903/524288 : ℝ)) (496036018089/500000000000 : ℝ) (992072036181/1000000000000 : ℝ) (501261459291/1000000000000 : ℝ) (250630729651/500000000000 : ℝ) (396835930407/500000000000 : ℝ) (158734372167/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0830_exp_lower
  have heNumeric : (2054901548477/1000000000000 : ℝ)/4 ≤ Real.exp (-8525650209313/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901548477/1000000000000 : ℝ)/4 ≤ Real.exp ((33451/262144 : ℝ)-(158734372167/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33451/262144 : ℝ) (66903/524288 : ℝ) (158734372167/200000000000 : ℝ) (2054901548477/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0831; no trusted numerical premise.
theorem cover8_leaf0831_exp_radius : (199601618382052871/200000000000000000 : ℝ) ≤ Real.exp ((-8363/524288 : ℝ)/8) ∧ Real.exp ((-8363/524288 : ℝ)/8) ≤ (249502022977566089/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8363/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0831_exp_lower : (920113448553225571/1000000000000000000 : ℝ) ≤ Real.exp ((-17051300433253/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051300433253/25600000000000 : ℝ)/8) ≤ (230028362138306393/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051300433253/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0831_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901547303/1000000000000 : ℝ) ≤ 4*Real.exp (66903/524288 : ℝ)*Real.exp (-mu (radius 8 (8363/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901547303/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8363/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0831_exp_radius
  have hrNumeric : (984175389337/1000000000000 : ℝ) ≤ Real.exp (-8363/524288 : ℝ) ∧ Real.exp (-8363/524288 : ℝ) ≤ (492087694669/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984175389337/1000000000000 : ℝ) ≤ (radius 8 (8363/65536 : ℝ)) ∧ (radius 8 (8363/65536 : ℝ)) ≤ (492087694669/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8363/65536 : ℝ)) (984175389337/1000000000000 : ℝ) (492087694669/500000000000 : ℝ) (177197073963/1000000000000 : ℝ) (17719707397/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8363/65536 : ℝ)) (984175389337/1000000000000 : ℝ) (492087694669/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8363/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984175389337/1000000000000 : ℝ) (492087694669/500000000000 : ℝ) (248021923667/250000000000 : ℝ) (992087694669/1000000000000 : ℝ) (99205614223/100000000000 : ℝ) (992056142231/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8363/65536 : ℝ)) 1 (248021923667/250000000000 : ℝ) (992087694669/1000000000000 : ℝ) (99205614223/100000000000 : ℝ) (992056142231/1000000000000 : ℝ) (992071918449/1000000000000 : ℝ) (19841438369/20000000000 : ℝ) (992071918323/1000000000000 : ℝ) (39682876733/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8363/65536 : ℝ)) 2 (992071918449/1000000000000 : ℝ) (19841438369/20000000000 : ℝ) (992071918323/1000000000000 : ℝ) (39682876733/40000000000 : ℝ) (496035959193/500000000000 : ℝ) (248017979597/250000000000 : ℝ) (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8363/65536 : ℝ)) 3 (496035959193/500000000000 : ℝ) (248017979597/250000000000 : ℝ) (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ) (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ) (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8363/65536 : ℝ)) 4 (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ) (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ) (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ) (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8363/65536 : ℝ)) 5 (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ) (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ) (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ) (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8363/65536 : ℝ)) 6 (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ) (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ) (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ) (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8363/65536 : ℝ)) 7 (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ) (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ) (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ) (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8363/65536 : ℝ))) (177197073963/1000000000000 : ℝ) (17719707397/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8363/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177197073963/1000000000000 : ℝ) (17719707397/100000000000 : ℝ) (588598536981/1000000000000 : ℝ) (117719707397/200000000000 : ℝ) (420947828077/1000000000000 : ℝ) (210473914043/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8363/65536 : ℝ))) 1 (588598536981/1000000000000 : ℝ) (117719707397/200000000000 : ℝ) (420947828077/1000000000000 : ℝ) (210473914043/500000000000 : ℝ) (504773182529/1000000000000 : ℝ) (63096647817/125000000000 : ℝ) (99552855459/200000000000 : ℝ) (497764277303/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8363/65536 : ℝ))) 2 (504773182529/1000000000000 : ℝ) (63096647817/125000000000 : ℝ) (99552855459/200000000000 : ℝ) (497764277303/1000000000000 : ℝ) (62658591239/125000000000 : ℝ) (1566464781/3125000000 : ℝ) (250628239829/500000000000 : ℝ) (250628239833/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8363/65536 : ℝ))) 3 (62658591239/125000000000 : ℝ) (1566464781/3125000000 : ℝ) (250628239829/500000000000 : ℝ) (250628239833/500000000000 : ℝ) (100252520957/200000000000 : ℝ) (501262604793/1000000000000 : ℝ) (501262604747/1000000000000 : ℝ) (125315651189/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8363/65536 : ℝ))) 4 (100252520957/200000000000 : ℝ) (501262604793/1000000000000 : ℝ) (501262604747/1000000000000 : ℝ) (125315651189/250000000000 : ℝ) (250631302383/500000000000 : ℝ) (20050504191/40000000000 : ℝ) (100252520953/200000000000 : ℝ) (20050504191/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8363/65536 : ℝ))) 5 (250631302383/500000000000 : ℝ) (20050504191/40000000000 : ℝ) (100252520953/200000000000 : ℝ) (20050504191/40000000000 : ℝ) (100252520953/200000000000 : ℝ) (20050504191/40000000000 : ℝ) (100252520953/200000000000 : ℝ) (20050504191/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8363/65536 : ℝ))) 6 (100252520953/200000000000 : ℝ) (20050504191/40000000000 : ℝ) (100252520953/200000000000 : ℝ) (20050504191/40000000000 : ℝ) (100252520953/200000000000 : ℝ) (20050504191/40000000000 : ℝ) (100252520953/200000000000 : ℝ) (20050504191/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8363/65536 : ℝ))) 7 (100252520953/200000000000 : ℝ) (20050504191/40000000000 : ℝ) (100252520953/200000000000 : ℝ) (20050504191/40000000000 : ℝ) (100252520953/200000000000 : ℝ) (20050504191/40000000000 : ℝ) (100252520953/200000000000 : ℝ) (20050504191/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8363/65536 : ℝ)) hmem 8 (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ) (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8363/65536 : ℝ))) hcmem 8 (100252520953/200000000000 : ℝ) (20050504191/40000000000 : ℝ) (100252520953/200000000000 : ℝ) (20050504191/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8363/65536 : ℝ)) (198414383677/200000000000 : ℝ) (248017979597/250000000000 : ℝ) (100252520953/200000000000 : ℝ) (20050504191/40000000000 : ℝ) (24802305273/31250000000 : ℝ) (158734753751/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0831_exp_lower
  have heNumeric : (2054901547303/1000000000000 : ℝ)/4 ≤ Real.exp (-17051300433253/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901547303/1000000000000 : ℝ)/4 ≤ Real.exp ((66903/524288 : ℝ)-(158734753751/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66903/524288 : ℝ) (8363/65536 : ℝ) (158734753751/200000000000 : ℝ) (2054901547303/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0832; no trusted numerical premise.
theorem cover8_leaf0832_exp_radius : (499004031083652949/500000000000000000 : ℝ) ≤ Real.exp ((-66905/4194304 : ℝ)/8) ∧ Real.exp ((-66905/4194304 : ℝ)/8) ≤ (998008062167305899/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66905/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0832_exp_lower : (920113448489465483/1000000000000000000 : ℝ) ≤ Real.exp ((-10657062779653/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657062779653/16000000000000 : ℝ)/8) ≤ (230028362122366371/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657062779653/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0832_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725386541/250000000000 : ℝ) ≤ 4*Real.exp (8363/65536 : ℝ)*Real.exp (-mu (radius 8 (66905/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725386541/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66905/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0832_exp_radius
  have hrNumeric : (984175154691/1000000000000 : ℝ) ≤ Real.exp (-66905/4194304 : ℝ) ∧ Real.exp (-66905/4194304 : ℝ) ≤ (246043788673/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984175154691/1000000000000 : ℝ) ≤ (radius 8 (66905/524288 : ℝ)) ∧ (radius 8 (66905/524288 : ℝ)) ≤ (246043788673/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66905/524288 : ℝ)) (984175154691/1000000000000 : ℝ) (246043788673/250000000000 : ℝ) (177198377213/1000000000000 : ℝ) (177198377219/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66905/524288 : ℝ)) (984175154691/1000000000000 : ℝ) (246043788673/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66905/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984175154691/1000000000000 : ℝ) (246043788673/250000000000 : ℝ) (198417515469/200000000000 : ℝ) (496043788673/500000000000 : ℝ) (992056023967/1000000000000 : ℝ) (992056023969/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66905/524288 : ℝ)) 1 (198417515469/200000000000 : ℝ) (496043788673/500000000000 : ℝ) (992056023967/1000000000000 : ℝ) (992056023969/1000000000000 : ℝ) (62004487541/62500000000 : ℝ) (496035900329/500000000000 : ℝ) (99207180053/100000000000 : ℝ) (992071800533/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66905/524288 : ℝ)) 2 (62004487541/62500000000 : ℝ) (496035900329/500000000000 : ℝ) (99207180053/100000000000 : ℝ) (992071800533/1000000000000 : ℝ) (992071800593/1000000000000 : ℝ) (248017950149/250000000000 : ℝ) (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66905/524288 : ℝ)) 3 (992071800593/1000000000000 : ℝ) (248017950149/250000000000 : ℝ) (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ) (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ) (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66905/524288 : ℝ)) 4 (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ) (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ) (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ) (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66905/524288 : ℝ)) 5 (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ) (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ) (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ) (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66905/524288 : ℝ)) 6 (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ) (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ) (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ) (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66905/524288 : ℝ)) 7 (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ) (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ) (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ) (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66905/524288 : ℝ))) (177198377213/1000000000000 : ℝ) (177198377219/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66905/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177198377213/1000000000000 : ℝ) (177198377219/1000000000000 : ℝ) (294299594303/500000000000 : ℝ) (58859918861/100000000000 : ℝ) (420949376069/1000000000000 : ℝ) (420949376077/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66905/524288 : ℝ))) 1 (294299594303/500000000000 : ℝ) (58859918861/100000000000 : ℝ) (420949376069/1000000000000 : ℝ) (420949376077/1000000000000 : ℝ) (504774282337/1000000000000 : ℝ) (63096785293/125000000000 : ℝ) (99553093613/200000000000 : ℝ) (62220683509/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66905/524288 : ℝ))) 2 (504774282337/1000000000000 : ℝ) (63096785293/125000000000 : ℝ) (99553093613/200000000000 : ℝ) (62220683509/125000000000 : ℝ) (501269875201/1000000000000 : ℝ) (62658734401/125000000000 : ℝ) (501257625293/1000000000000 : ℝ) (501257625301/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66905/524288 : ℝ))) 3 (501269875201/1000000000000 : ℝ) (62658734401/125000000000 : ℝ) (501257625293/1000000000000 : ℝ) (501257625301/1000000000000 : ℝ) (501263750247/1000000000000 : ℝ) (100252750051/200000000000 : ℝ) (501263750209/1000000000000 : ℝ) (250631875109/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66905/524288 : ℝ))) 4 (501263750247/1000000000000 : ℝ) (100252750051/200000000000 : ℝ) (501263750209/1000000000000 : ℝ) (250631875109/500000000000 : ℝ) (125315937557/250000000000 : ℝ) (501263750237/1000000000000 : ℝ) (501263750227/1000000000000 : ℝ) (501263750237/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66905/524288 : ℝ))) 5 (125315937557/250000000000 : ℝ) (501263750237/1000000000000 : ℝ) (501263750227/1000000000000 : ℝ) (501263750237/1000000000000 : ℝ) (501263750227/1000000000000 : ℝ) (501263750237/1000000000000 : ℝ) (501263750227/1000000000000 : ℝ) (501263750237/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66905/524288 : ℝ))) 6 (501263750227/1000000000000 : ℝ) (501263750237/1000000000000 : ℝ) (501263750227/1000000000000 : ℝ) (501263750237/1000000000000 : ℝ) (501263750227/1000000000000 : ℝ) (501263750237/1000000000000 : ℝ) (501263750227/1000000000000 : ℝ) (501263750237/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66905/524288 : ℝ))) 7 (501263750227/1000000000000 : ℝ) (501263750237/1000000000000 : ℝ) (501263750227/1000000000000 : ℝ) (501263750237/1000000000000 : ℝ) (501263750227/1000000000000 : ℝ) (501263750237/1000000000000 : ℝ) (501263750227/1000000000000 : ℝ) (501263750237/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66905/524288 : ℝ)) hmem 8 (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ) (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66905/524288 : ℝ))) hcmem 8 (501263750227/1000000000000 : ℝ) (501263750237/1000000000000 : ℝ) (501263750227/1000000000000 : ℝ) (501263750237/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66905/524288 : ℝ)) (62004487537/62500000000 : ℝ) (248017950149/250000000000 : ℝ) (501263750227/1000000000000 : ℝ) (501263750237/1000000000000 : ℝ) (396837838319/500000000000 : ℝ) (396837838329/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0832_exp_lower
  have heNumeric : (513725386541/250000000000 : ℝ)/4 ≤ Real.exp (-10657062779653/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725386541/250000000000 : ℝ)/4 ≤ Real.exp ((8363/65536 : ℝ)-(396837838329/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8363/65536 : ℝ) (66905/524288 : ℝ) (396837838329/500000000000 : ℝ) (513725386541/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0833; no trusted numerical premise.
theorem cover8_leaf0833_exp_radius : (998008032424348327/1000000000000000000 : ℝ) ≤ Real.exp ((-33453/2097152 : ℝ)/8) ∧ Real.exp ((-33453/2097152 : ℝ)/8) ≤ (124751004053043541/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33453/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0833_exp_lower : (460056724214520403/500000000000000000 : ℝ) ≤ Real.exp ((-85256502304471/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256502304471/128000000000000 : ℝ)/8) ≤ (920113448429040807/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256502304471/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0833_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980309017/200000000000 : ℝ) ≤ 4*Real.exp (66905/524288 : ℝ)*Real.exp (-mu (radius 8 (33453/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980309017/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33453/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0833_exp_radius
  have hrNumeric : (492087460023/500000000000 : ℝ) ≤ Real.exp (-33453/2097152 : ℝ) ∧ Real.exp (-33453/2097152 : ℝ) ≤ (984174920047/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492087460023/500000000000 : ℝ) ≤ (radius 8 (33453/262144 : ℝ)) ∧ (radius 8 (33453/262144 : ℝ)) ≤ (984174920047/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33453/262144 : ℝ)) (492087460023/500000000000 : ℝ) (984174920047/1000000000000 : ℝ) (88599840223/500000000000 : ℝ) (177199680453/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33453/262144 : ℝ)) (492087460023/500000000000 : ℝ) (984174920047/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33453/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492087460023/500000000000 : ℝ) (984174920047/1000000000000 : ℝ) (992087460023/1000000000000 : ℝ) (124010932503/125000000000 : ℝ) (198411181141/200000000000 : ℝ) (992055905707/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33453/262144 : ℝ)) 1 (992087460023/1000000000000 : ℝ) (124010932503/125000000000 : ℝ) (198411181141/200000000000 : ℝ) (992055905707/1000000000000 : ℝ) (62004480179/62500000000 : ℝ) (496035841433/500000000000 : ℝ) (496035841369/500000000000 : ℝ) (992071682741/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33453/262144 : ℝ)) 2 (62004480179/62500000000 : ℝ) (496035841433/500000000000 : ℝ) (496035841369/500000000000 : ℝ) (992071682741/1000000000000 : ℝ) (992071682801/1000000000000 : ℝ) (248017920701/250000000000 : ℝ) (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33453/262144 : ℝ)) 3 (992071682801/1000000000000 : ℝ) (248017920701/250000000000 : ℝ) (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ) (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ) (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33453/262144 : ℝ)) 4 (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ) (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ) (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ) (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33453/262144 : ℝ)) 5 (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ) (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ) (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ) (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33453/262144 : ℝ)) 6 (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ) (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ) (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ) (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33453/262144 : ℝ)) 7 (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ) (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ) (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ) (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33453/262144 : ℝ))) (88599840223/500000000000 : ℝ) (177199680453/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33453/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88599840223/500000000000 : ℝ) (177199680453/1000000000000 : ℝ) (588599840223/1000000000000 : ℝ) (588599840227/1000000000000 : ℝ) (84190184807/200000000000 : ℝ) (105237731011/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33453/262144 : ℝ))) 1 (588599840223/1000000000000 : ℝ) (588599840227/1000000000000 : ℝ) (84190184807/200000000000 : ℝ) (105237731011/250000000000 : ℝ) (504775382129/1000000000000 : ℝ) (63096922767/125000000000 : ℝ) (99553331763/200000000000 : ℝ) (497766658823/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33453/262144 : ℝ))) 2 (504775382129/1000000000000 : ℝ) (63096922767/125000000000 : ℝ) (99553331763/200000000000 : ℝ) (497766658823/1000000000000 : ℝ) (62658877559/125000000000 : ℝ) (1566471939/3125000000 : ℝ) (50125877091/100000000000 : ℝ) (250629385459/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33453/262144 : ℝ))) 3 (62658877559/125000000000 : ℝ) (1566471939/3125000000 : ℝ) (50125877091/100000000000 : ℝ) (250629385459/500000000000 : ℝ) (501264895691/1000000000000 : ℝ) (501264895699/1000000000000 : ℝ) (501264895653/1000000000000 : ℝ) (250632447831/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33453/262144 : ℝ))) 4 (501264895691/1000000000000 : ℝ) (501264895699/1000000000000 : ℝ) (501264895653/1000000000000 : ℝ) (250632447831/500000000000 : ℝ) (62658111959/125000000000 : ℝ) (501264895681/1000000000000 : ℝ) (501264895671/1000000000000 : ℝ) (501264895681/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33453/262144 : ℝ))) 5 (62658111959/125000000000 : ℝ) (501264895681/1000000000000 : ℝ) (501264895671/1000000000000 : ℝ) (501264895681/1000000000000 : ℝ) (501264895671/1000000000000 : ℝ) (501264895681/1000000000000 : ℝ) (501264895671/1000000000000 : ℝ) (501264895681/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33453/262144 : ℝ))) 6 (501264895671/1000000000000 : ℝ) (501264895681/1000000000000 : ℝ) (501264895671/1000000000000 : ℝ) (501264895681/1000000000000 : ℝ) (501264895671/1000000000000 : ℝ) (501264895681/1000000000000 : ℝ) (501264895671/1000000000000 : ℝ) (501264895681/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33453/262144 : ℝ))) 7 (501264895671/1000000000000 : ℝ) (501264895681/1000000000000 : ℝ) (501264895671/1000000000000 : ℝ) (501264895681/1000000000000 : ℝ) (501264895671/1000000000000 : ℝ) (501264895681/1000000000000 : ℝ) (501264895671/1000000000000 : ℝ) (501264895681/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33453/262144 : ℝ)) hmem 8 (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ) (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33453/262144 : ℝ))) hcmem 8 (501264895671/1000000000000 : ℝ) (501264895681/1000000000000 : ℝ) (501264895671/1000000000000 : ℝ) (501264895681/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33453/262144 : ℝ)) (2480179207/2500000000 : ℝ) (248017920701/250000000000 : ℝ) (501264895671/1000000000000 : ℝ) (501264895681/1000000000000 : ℝ) (6200606129/7812500000 : ℝ) (198419396133/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0833_exp_lower
  have heNumeric : (410980309017/200000000000 : ℝ)/4 ≤ Real.exp (-85256502304471/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980309017/200000000000 : ℝ)/4 ≤ Real.exp ((66905/524288 : ℝ)-(198419396133/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66905/524288 : ℝ) (33453/262144 : ℝ) (198419396133/250000000000 : ℝ) (410980309017/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0834; no trusted numerical premise.
theorem cover8_leaf0834_exp_radius : (499004001340695821/500000000000000000 : ℝ) ≤ Real.exp ((-66907/4194304 : ℝ)/8) ∧ Real.exp ((-66907/4194304 : ℝ)/8) ≤ (998008002681391643/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66907/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0834_exp_lower : (9201134483699963/10000000000000000 : ℝ) ≤ Real.exp ((-42628251185091/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628251185091/64000000000000 : ℝ)/8) ≤ (920113448369996301/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628251185091/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0834_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490154403/100000000000 : ℝ) ≤ 4*Real.exp (33453/262144 : ℝ)*Real.exp (-mu (radius 8 (66907/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (205490154403/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66907/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0834_exp_radius
  have hrNumeric : (4920873427/5000000000 : ℝ) ≤ Real.exp (-66907/4194304 : ℝ) ∧ Real.exp (-66907/4194304 : ℝ) ≤ (984174685401/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (4920873427/5000000000 : ℝ) ≤ (radius 8 (66907/524288 : ℝ)) ∧ (radius 8 (66907/524288 : ℝ)) ≤ (984174685401/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66907/524288 : ℝ)) (4920873427/5000000000 : ℝ) (984174685401/1000000000000 : ℝ) (44300245919/250000000000 : ℝ) (88600491841/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66907/524288 : ℝ)) (4920873427/5000000000 : ℝ) (984174685401/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66907/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (4920873427/5000000000 : ℝ) (984174685401/1000000000000 : ℝ) (9920873427/10000000000 : ℝ) (992087342701/1000000000000 : ℝ) (992055787443/1000000000000 : ℝ) (248013946861/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66907/524288 : ℝ)) 1 (9920873427/10000000000 : ℝ) (992087342701/1000000000000 : ℝ) (992055787443/1000000000000 : ℝ) (248013946861/250000000000 : ℝ) (992071565071/1000000000000 : ℝ) (992071565073/1000000000000 : ℝ) (496035782473/500000000000 : ℝ) (248017891237/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66907/524288 : ℝ)) 2 (992071565071/1000000000000 : ℝ) (992071565073/1000000000000 : ℝ) (496035782473/500000000000 : ℝ) (248017891237/250000000000 : ℝ) (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ) (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66907/524288 : ℝ)) 3 (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ) (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ) (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ) (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66907/524288 : ℝ)) 4 (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ) (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ) (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ) (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66907/524288 : ℝ)) 5 (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ) (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ) (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ) (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66907/524288 : ℝ)) 6 (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ) (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ) (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ) (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66907/524288 : ℝ)) 7 (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ) (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ) (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ) (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66907/524288 : ℝ))) (44300245919/250000000000 : ℝ) (88600491841/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66907/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44300245919/250000000000 : ℝ) (88600491841/500000000000 : ℝ) (294300245919/500000000000 : ℝ) (588600491841/1000000000000 : ℝ) (420952471991/1000000000000 : ℝ) (420952471999/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66907/524288 : ℝ))) 1 (294300245919/500000000000 : ℝ) (588600491841/1000000000000 : ℝ) (420952471991/1000000000000 : ℝ) (420952471999/1000000000000 : ℝ) (252388240957/500000000000 : ℝ) (788713253/1562500000 : ℝ) (248883924779/500000000000 : ℝ) (99553569913/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66907/524288 : ℝ))) 2 (252388240957/500000000000 : ℝ) (788713253/1562500000 : ℝ) (248883924779/500000000000 : ℝ) (99553569913/200000000000 : ℝ) (62659020717/125000000000 : ℝ) (501272165743/1000000000000 : ℝ) (12531497913/25000000000 : ℝ) (501259916527/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66907/524288 : ℝ))) 3 (62659020717/125000000000 : ℝ) (501272165743/1000000000000 : ℝ) (12531497913/25000000000 : ℝ) (501259916527/1000000000000 : ℝ) (62658255141/125000000000 : ℝ) (100253208227/200000000000 : ℝ) (50126604109/100000000000 : ℝ) (250633020549/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66907/524288 : ℝ))) 4 (62658255141/125000000000 : ℝ) (100253208227/200000000000 : ℝ) (50126604109/100000000000 : ℝ) (250633020549/500000000000 : ℝ) (501266041109/1000000000000 : ℝ) (501266041117/1000000000000 : ℝ) (125316510277/250000000000 : ℝ) (501266041117/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66907/524288 : ℝ))) 5 (501266041109/1000000000000 : ℝ) (501266041117/1000000000000 : ℝ) (125316510277/250000000000 : ℝ) (501266041117/1000000000000 : ℝ) (125316510277/250000000000 : ℝ) (501266041117/1000000000000 : ℝ) (125316510277/250000000000 : ℝ) (501266041117/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66907/524288 : ℝ))) 6 (125316510277/250000000000 : ℝ) (501266041117/1000000000000 : ℝ) (125316510277/250000000000 : ℝ) (501266041117/1000000000000 : ℝ) (125316510277/250000000000 : ℝ) (501266041117/1000000000000 : ℝ) (125316510277/250000000000 : ℝ) (501266041117/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66907/524288 : ℝ))) 7 (125316510277/250000000000 : ℝ) (501266041117/1000000000000 : ℝ) (125316510277/250000000000 : ℝ) (501266041117/1000000000000 : ℝ) (125316510277/250000000000 : ℝ) (501266041117/1000000000000 : ℝ) (125316510277/250000000000 : ℝ) (501266041117/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66907/524288 : ℝ)) hmem 8 (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ) (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66907/524288 : ℝ))) hcmem 8 (125316510277/250000000000 : ℝ) (501266041117/1000000000000 : ℝ) (125316510277/250000000000 : ℝ) (501266041117/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66907/524288 : ℝ)) (62004472813/62500000000 : ℝ) (992071565011/1000000000000 : ℝ) (125316510277/250000000000 : ℝ) (501266041117/1000000000000 : ℝ) (99209936547/125000000000 : ℝ) (396839746197/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0834_exp_lower
  have heNumeric : (205490154403/100000000000 : ℝ)/4 ≤ Real.exp (-42628251185091/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490154403/100000000000 : ℝ)/4 ≤ Real.exp ((33453/262144 : ℝ)-(396839746197/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33453/262144 : ℝ) (66907/524288 : ℝ) (396839746197/500000000000 : ℝ) (205490154403/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0835; no trusted numerical premise.
theorem cover8_leaf0835_exp_radius : (249501993234608961/250000000000000000 : ℝ) ≤ Real.exp ((-16727/1048576 : ℝ)/8) ∧ Real.exp ((-16727/1048576 : ℝ)/8) ≤ (199601594587687169/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16727/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0835_exp_lower : (920113448313597119/1000000000000000000 : ℝ) ≤ Real.exp ((-85256502432949/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256502432949/128000000000000 : ℝ)/8) ≤ (2875354525979991/3125000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256502432949/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0835_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450771511/500000000000 : ℝ) ≤ 4*Real.exp (66907/524288 : ℝ)*Real.exp (-mu (radius 8 (16727/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450771511/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16727/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0835_exp_radius
  have hrNumeric : (196834890151/200000000000 : ℝ) ≤ Real.exp (-16727/1048576 : ℝ) ∧ Real.exp (-16727/1048576 : ℝ) ≤ (246043612689/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196834890151/200000000000 : ℝ) ≤ (radius 8 (16727/131072 : ℝ)) ∧ (radius 8 (16727/131072 : ℝ)) ≤ (246043612689/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16727/131072 : ℝ)) (196834890151/200000000000 : ℝ) (246043612689/250000000000 : ℝ) (17720228689/100000000000 : ℝ) (11075142931/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16727/131072 : ℝ)) (196834890151/200000000000 : ℝ) (246043612689/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16727/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196834890151/200000000000 : ℝ) (246043612689/250000000000 : ℝ) (992087225377/1000000000000 : ℝ) (496043612689/500000000000 : ℝ) (992055669181/1000000000000 : ℝ) (496027834591/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16727/131072 : ℝ)) 1 (992087225377/1000000000000 : ℝ) (496043612689/500000000000 : ℝ) (992055669181/1000000000000 : ℝ) (496027834591/500000000000 : ℝ) (992071447279/1000000000000 : ℝ) (12400893091/12500000000 : ℝ) (992071447153/1000000000000 : ℝ) (198414289431/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16727/131072 : ℝ)) 2 (992071447279/1000000000000 : ℝ) (12400893091/12500000000 : ℝ) (992071447153/1000000000000 : ℝ) (198414289431/200000000000 : ℝ) (62004465451/62500000000 : ℝ) (496035723609/500000000000 : ℝ) (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16727/131072 : ℝ)) 3 (62004465451/62500000000 : ℝ) (496035723609/500000000000 : ℝ) (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ) (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ) (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16727/131072 : ℝ)) 4 (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ) (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ) (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ) (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16727/131072 : ℝ)) 5 (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ) (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ) (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ) (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16727/131072 : ℝ)) 6 (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ) (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ) (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ) (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16727/131072 : ℝ)) 7 (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ) (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ) (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ) (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16727/131072 : ℝ))) (17720228689/100000000000 : ℝ) (11075142931/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16727/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17720228689/100000000000 : ℝ) (11075142931/62500000000 : ℝ) (117720228689/200000000000 : ℝ) (73575142931/125000000000 : ℝ) (420954019923/1000000000000 : ℝ) (420954019931/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16727/131072 : ℝ))) 1 (117720228689/200000000000 : ℝ) (73575142931/125000000000 : ℝ) (420954019923/1000000000000 : ℝ) (420954019931/1000000000000 : ℝ) (126194395421/250000000000 : ℝ) (50477758169/100000000000 : ℝ) (497769040283/1000000000000 : ℝ) (49776904029/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16727/131072 : ℝ))) 2 (126194395421/250000000000 : ℝ) (50477758169/100000000000 : ℝ) (497769040283/1000000000000 : ℝ) (49776904029/100000000000 : ℝ) (501273310983/1000000000000 : ℝ) (50127331099/100000000000 : ℝ) (501261062113/1000000000000 : ℝ) (501261062121/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16727/131072 : ℝ))) 3 (501273310983/1000000000000 : ℝ) (50127331099/100000000000 : ℝ) (501261062113/1000000000000 : ℝ) (501261062121/1000000000000 : ℝ) (125316796637/250000000000 : ℝ) (125316796639/250000000000 : ℝ) (50126718651/100000000000 : ℝ) (501267186519/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16727/131072 : ℝ))) 4 (125316796637/250000000000 : ℝ) (125316796639/250000000000 : ℝ) (50126718651/100000000000 : ℝ) (501267186519/1000000000000 : ℝ) (501267186529/1000000000000 : ℝ) (250633593269/500000000000 : ℝ) (15664599579/31250000000 : ℝ) (250633593269/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16727/131072 : ℝ))) 5 (501267186529/1000000000000 : ℝ) (250633593269/500000000000 : ℝ) (15664599579/31250000000 : ℝ) (250633593269/500000000000 : ℝ) (15664599579/31250000000 : ℝ) (250633593269/500000000000 : ℝ) (15664599579/31250000000 : ℝ) (250633593269/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16727/131072 : ℝ))) 6 (15664599579/31250000000 : ℝ) (250633593269/500000000000 : ℝ) (15664599579/31250000000 : ℝ) (250633593269/500000000000 : ℝ) (15664599579/31250000000 : ℝ) (250633593269/500000000000 : ℝ) (15664599579/31250000000 : ℝ) (250633593269/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16727/131072 : ℝ))) 7 (15664599579/31250000000 : ℝ) (250633593269/500000000000 : ℝ) (15664599579/31250000000 : ℝ) (250633593269/500000000000 : ℝ) (15664599579/31250000000 : ℝ) (250633593269/500000000000 : ℝ) (15664599579/31250000000 : ℝ) (250633593269/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16727/131072 : ℝ)) hmem 8 (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ) (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16727/131072 : ℝ))) hcmem 8 (15664599579/31250000000 : ℝ) (250633593269/500000000000 : ℝ) (15664599579/31250000000 : ℝ) (250633593269/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16727/131072 : ℝ)) (198414289443/200000000000 : ℝ) (496035723609/500000000000 : ℝ) (15664599579/31250000000 : ℝ) (250633593269/500000000000 : ℝ) (396840700107/500000000000 : ℝ) (793681400233/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0835_exp_lower
  have heNumeric : (1027450771511/500000000000 : ℝ)/4 ≤ Real.exp (-85256502432949/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450771511/500000000000 : ℝ)/4 ≤ Real.exp ((66907/524288 : ℝ)-(793681400233/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66907/524288 : ℝ) (16727/131072 : ℝ) (793681400233/1000000000000 : ℝ) (1027450771511/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0836; no trusted numerical premise.
theorem cover8_leaf0836_exp_radius : (249501985798870233/250000000000000000 : ℝ) ≤ Real.exp ((-66909/4194304 : ℝ)/8) ∧ Real.exp ((-66909/4194304 : ℝ)/8) ≤ (998007943195480933/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66909/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0836_exp_lower : (920113448258693123/1000000000000000000 : ℝ) ≤ Real.exp ((-21314125623513/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314125623513/32000000000000 : ℝ)/8) ≤ (230028362064673281/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314125623513/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0836_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901542041/1000000000000 : ℝ) ≤ 4*Real.exp (16727/131072 : ℝ)*Real.exp (-mu (radius 8 (66909/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901542041/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66909/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0836_exp_radius
  have hrNumeric : (984174216109/1000000000000 : ℝ) ≤ Real.exp (-66909/4194304 : ℝ) ∧ Real.exp (-66909/4194304 : ℝ) ≤ (98417421611/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984174216109/1000000000000 : ℝ) ≤ (radius 8 (66909/524288 : ℝ)) ∧ (radius 8 (66909/524288 : ℝ)) ≤ (98417421611/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66909/524288 : ℝ)) (984174216109/1000000000000 : ℝ) (98417421611/100000000000 : ℝ) (177203590099/1000000000000 : ℝ) (88601795053/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66909/524288 : ℝ)) (984174216109/1000000000000 : ℝ) (98417421611/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66909/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984174216109/1000000000000 : ℝ) (98417421611/100000000000 : ℝ) (496043554027/500000000000 : ℝ) (198417421611/200000000000 : ℝ) (496027775459/500000000000 : ℝ) (24801388773/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66909/524288 : ℝ)) 1 (496043554027/500000000000 : ℝ) (198417421611/200000000000 : ℝ) (496027775459/500000000000 : ℝ) (24801388773/25000000000 : ℝ) (496035664743/500000000000 : ℝ) (62004458093/62500000000 : ℝ) (12400891617/12500000000 : ℝ) (992071329363/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66909/524288 : ℝ)) 2 (496035664743/500000000000 : ℝ) (62004458093/62500000000 : ℝ) (12400891617/12500000000 : ℝ) (992071329363/1000000000000 : ℝ) (992071329423/1000000000000 : ℝ) (496035664713/500000000000 : ℝ) (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66909/524288 : ℝ)) 3 (992071329423/1000000000000 : ℝ) (496035664713/500000000000 : ℝ) (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ) (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ) (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66909/524288 : ℝ)) 4 (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ) (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ) (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ) (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66909/524288 : ℝ)) 5 (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ) (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ) (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ) (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66909/524288 : ℝ)) 6 (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ) (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ) (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ) (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66909/524288 : ℝ)) 7 (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ) (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ) (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ) (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66909/524288 : ℝ))) (177203590099/1000000000000 : ℝ) (88601795053/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66909/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177203590099/1000000000000 : ℝ) (88601795053/500000000000 : ℝ) (588601795049/1000000000000 : ℝ) (588601795053/1000000000000 : ℝ) (105238891961/250000000000 : ℝ) (420955567853/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66909/524288 : ℝ))) 1 (588601795049/1000000000000 : ℝ) (588601795053/1000000000000 : ℝ) (105238891961/250000000000 : ℝ) (420955567853/1000000000000 : ℝ) (252389340723/500000000000 : ℝ) (504778681453/1000000000000 : ℝ) (497770230999/1000000000000 : ℝ) (497770231007/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66909/524288 : ℝ))) 2 (252389340723/500000000000 : ℝ) (504778681453/1000000000000 : ℝ) (497770230999/1000000000000 : ℝ) (497770231007/1000000000000 : ℝ) (250637228111/500000000000 : ℝ) (50127445623/100000000000 : ℝ) (250631103849/500000000000 : ℝ) (250631103853/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66909/524288 : ℝ))) 3 (250637228111/500000000000 : ℝ) (50127445623/100000000000 : ℝ) (250631103849/500000000000 : ℝ) (250631103853/500000000000 : ℝ) (12531708299/25000000000 : ℝ) (7832317687/15625000000 : ℝ) (250634165961/500000000000 : ℝ) (501268331931/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66909/524288 : ℝ))) 4 (12531708299/25000000000 : ℝ) (7832317687/15625000000 : ℝ) (250634165961/500000000000 : ℝ) (501268331931/1000000000000 : ℝ) (501268331941/1000000000000 : ℝ) (10025366639/20000000000 : ℝ) (25063416597/50000000000 : ℝ) (10025366639/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66909/524288 : ℝ))) 5 (501268331941/1000000000000 : ℝ) (10025366639/20000000000 : ℝ) (25063416597/50000000000 : ℝ) (10025366639/20000000000 : ℝ) (25063416597/50000000000 : ℝ) (10025366639/20000000000 : ℝ) (25063416597/50000000000 : ℝ) (10025366639/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66909/524288 : ℝ))) 6 (25063416597/50000000000 : ℝ) (10025366639/20000000000 : ℝ) (25063416597/50000000000 : ℝ) (10025366639/20000000000 : ℝ) (25063416597/50000000000 : ℝ) (10025366639/20000000000 : ℝ) (25063416597/50000000000 : ℝ) (10025366639/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66909/524288 : ℝ))) 7 (25063416597/50000000000 : ℝ) (10025366639/20000000000 : ℝ) (25063416597/50000000000 : ℝ) (10025366639/20000000000 : ℝ) (25063416597/50000000000 : ℝ) (10025366639/20000000000 : ℝ) (25063416597/50000000000 : ℝ) (10025366639/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66909/524288 : ℝ)) hmem 8 (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ) (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66909/524288 : ℝ))) hcmem 8 (25063416597/50000000000 : ℝ) (10025366639/20000000000 : ℝ) (25063416597/50000000000 : ℝ) (10025366639/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66909/524288 : ℝ)) (496035664711/500000000000 : ℝ) (496035664713/500000000000 : ℝ) (25063416597/50000000000 : ℝ) (10025366639/20000000000 : ℝ) (793683308039/1000000000000 : ℝ) (793683308059/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0836_exp_lower
  have heNumeric : (2054901542041/1000000000000 : ℝ)/4 ≤ Real.exp (-21314125623513/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901542041/1000000000000 : ℝ)/4 ≤ Real.exp ((16727/131072 : ℝ)-(793683308059/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16727/131072 : ℝ) (66909/524288 : ℝ) (793683308059/1000000000000 : ℝ) (2054901542041/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0837; no trusted numerical premise.
theorem cover8_leaf0837_exp_radius : (998007913452526907/1000000000000000000 : ℝ) ≤ Real.exp ((-33455/2097152 : ℝ)/8) ∧ Real.exp ((-33455/2097152 : ℝ)/8) ≤ (249501978363131727/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33455/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0837_exp_lower : (230028362051752381/250000000000000000 : ℝ) ≤ Real.exp ((-85256502551571/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256502551571/128000000000000 : ℝ)/8) ≤ (36804537928280381/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256502551571/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0837_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450770559/500000000000 : ℝ) ≤ 4*Real.exp (66909/524288 : ℝ)*Real.exp (-mu (radius 8 (33455/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450770559/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33455/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0837_exp_radius
  have hrNumeric : (123021747683/125000000000 : ℝ) ≤ Real.exp (-33455/2097152 : ℝ) ∧ Real.exp (-33455/2097152 : ℝ) ≤ (196834796293/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123021747683/125000000000 : ℝ) ≤ (radius 8 (33455/262144 : ℝ)) ∧ (radius 8 (33455/262144 : ℝ)) ≤ (196834796293/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33455/262144 : ℝ)) (123021747683/125000000000 : ℝ) (196834796293/200000000000 : ℝ) (177204893293/1000000000000 : ℝ) (1772048933/10000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33455/262144 : ℝ)) (123021747683/125000000000 : ℝ) (196834796293/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33455/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123021747683/125000000000 : ℝ) (196834796293/200000000000 : ℝ) (248021747683/250000000000 : ℝ) (992086990733/1000000000000 : ℝ) (62003464541/62500000000 : ℝ) (496027716329/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33455/262144 : ℝ)) 1 (248021747683/250000000000 : ℝ) (992086990733/1000000000000 : ℝ) (62003464541/62500000000 : ℝ) (496027716329/500000000000 : ℝ) (496035605847/500000000000 : ℝ) (62004450731/62500000000 : ℝ) (62004450723/62500000000 : ℝ) (992071211571/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33455/262144 : ℝ)) 2 (496035605847/500000000000 : ℝ) (62004450731/62500000000 : ℝ) (62004450723/62500000000 : ℝ) (992071211571/1000000000000 : ℝ) (992071211631/1000000000000 : ℝ) (496035605817/500000000000 : ℝ) (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33455/262144 : ℝ)) 3 (992071211631/1000000000000 : ℝ) (496035605817/500000000000 : ℝ) (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ) (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ) (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33455/262144 : ℝ)) 4 (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ) (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ) (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ) (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33455/262144 : ℝ)) 5 (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ) (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ) (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ) (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33455/262144 : ℝ)) 6 (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ) (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ) (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ) (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33455/262144 : ℝ)) 7 (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ) (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ) (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ) (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33455/262144 : ℝ))) (177204893293/1000000000000 : ℝ) (1772048933/10000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33455/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177204893293/1000000000000 : ℝ) (1772048933/10000000000 : ℝ) (294301223323/500000000000 : ℝ) (11772048933/20000000000 : ℝ) (420957115741/1000000000000 : ℝ) (1683828463/4000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33455/262144 : ℝ))) 1 (294301223323/500000000000 : ℝ) (11772048933/20000000000 : ℝ) (420957115741/1000000000000 : ℝ) (1683828463/4000000000 : ℝ) (504779781193/1000000000000 : ℝ) (1261949453/2500000000 : ℝ) (121526226/244140625 : ℝ) (62221427713/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33455/262144 : ℝ))) 2 (504779781193/1000000000000 : ℝ) (1261949453/2500000000 : ℝ) (121526226/244140625 : ℝ) (62221427713/125000000000 : ℝ) (125318900361/250000000000 : ℝ) (125318900363/250000000000 : ℝ) (250631676633/500000000000 : ℝ) (250631676637/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33455/262144 : ℝ))) 3 (125318900361/250000000000 : ℝ) (125318900363/250000000000 : ℝ) (250631676633/500000000000 : ℝ) (250631676637/500000000000 : ℝ) (100253895471/200000000000 : ℝ) (501269477363/1000000000000 : ℝ) (501269477317/1000000000000 : ℝ) (250634738663/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33455/262144 : ℝ))) 4 (100253895471/200000000000 : ℝ) (501269477363/1000000000000 : ℝ) (501269477317/1000000000000 : ℝ) (250634738663/500000000000 : ℝ) (62658684667/125000000000 : ℝ) (100253895469/200000000000 : ℝ) (100253895467/200000000000 : ℝ) (100253895469/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33455/262144 : ℝ))) 5 (62658684667/125000000000 : ℝ) (100253895469/200000000000 : ℝ) (100253895467/200000000000 : ℝ) (100253895469/200000000000 : ℝ) (100253895467/200000000000 : ℝ) (100253895469/200000000000 : ℝ) (100253895467/200000000000 : ℝ) (100253895469/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33455/262144 : ℝ))) 6 (100253895467/200000000000 : ℝ) (100253895469/200000000000 : ℝ) (100253895467/200000000000 : ℝ) (100253895469/200000000000 : ℝ) (100253895467/200000000000 : ℝ) (100253895469/200000000000 : ℝ) (100253895467/200000000000 : ℝ) (100253895469/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33455/262144 : ℝ))) 7 (100253895467/200000000000 : ℝ) (100253895469/200000000000 : ℝ) (100253895467/200000000000 : ℝ) (100253895469/200000000000 : ℝ) (100253895467/200000000000 : ℝ) (100253895469/200000000000 : ℝ) (100253895467/200000000000 : ℝ) (100253895469/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33455/262144 : ℝ)) hmem 8 (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ) (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33455/262144 : ℝ))) hcmem 8 (100253895467/200000000000 : ℝ) (100253895469/200000000000 : ℝ) (100253895467/200000000000 : ℝ) (100253895469/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33455/262144 : ℝ)) (99207121163/100000000000 : ℝ) (496035605817/500000000000 : ℝ) (100253895467/200000000000 : ℝ) (100253895469/200000000000 : ℝ) (793685215837/1000000000000 : ℝ) (793685215857/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0837_exp_lower
  have heNumeric : (1027450770559/500000000000 : ℝ)/4 ≤ Real.exp (-85256502551571/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450770559/500000000000 : ℝ)/4 ≤ Real.exp ((66909/524288 : ℝ)-(793685215857/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66909/524288 : ℝ) (33455/262144 : ℝ) (793685215857/1000000000000 : ℝ) (1027450770559/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0838; no trusted numerical premise.
theorem cover8_leaf0838_exp_radius : (124750985463696721/125000000000000000 : ℝ) ≤ Real.exp ((-66911/4194304 : ℝ)/8) ∧ Real.exp ((-66911/4194304 : ℝ)/8) ≤ (998007883709573769/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66911/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0838_exp_lower : (115014181019645769/125000000000000000 : ℝ) ≤ Real.exp ((-42628251303521/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628251303521/64000000000000 : ℝ)/8) ≤ (920113448157166153/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628251303521/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0838_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901540227/1000000000000 : ℝ) ≤ 4*Real.exp (33455/262144 : ℝ)*Real.exp (-mu (radius 8 (66911/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901540227/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66911/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0838_exp_radius
  have hrNumeric : (984173746819/1000000000000 : ℝ) ≤ Real.exp (-66911/4194304 : ℝ) ∧ Real.exp (-66911/4194304 : ℝ) ≤ (49208687341/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984173746819/1000000000000 : ℝ) ≤ (radius 8 (66911/524288 : ℝ)) ∧ (radius 8 (66911/524288 : ℝ)) ≤ (49208687341/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66911/524288 : ℝ)) (984173746819/1000000000000 : ℝ) (49208687341/50000000000 : ℝ) (88603098239/500000000000 : ℝ) (44301549121/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66911/524288 : ℝ)) (984173746819/1000000000000 : ℝ) (49208687341/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66911/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984173746819/1000000000000 : ℝ) (49208687341/50000000000 : ℝ) (992086873409/1000000000000 : ℝ) (99208687341/100000000000 : ℝ) (496027657197/500000000000 : ℝ) (248013828599/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66911/524288 : ℝ)) 1 (992086873409/1000000000000 : ℝ) (99208687341/100000000000 : ℝ) (496027657197/500000000000 : ℝ) (248013828599/250000000000 : ℝ) (992071093901/1000000000000 : ℝ) (992071093903/1000000000000 : ℝ) (62004443361/62500000000 : ℝ) (496035546889/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66911/524288 : ℝ)) 2 (992071093901/1000000000000 : ℝ) (992071093903/1000000000000 : ℝ) (62004443361/62500000000 : ℝ) (496035546889/500000000000 : ℝ) (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ) (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66911/524288 : ℝ)) 3 (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ) (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ) (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ) (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66911/524288 : ℝ)) 4 (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ) (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ) (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ) (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66911/524288 : ℝ)) 5 (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ) (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ) (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ) (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66911/524288 : ℝ)) 6 (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ) (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ) (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ) (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66911/524288 : ℝ)) 7 (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ) (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ) (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ) (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66911/524288 : ℝ))) (88603098239/500000000000 : ℝ) (44301549121/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66911/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88603098239/500000000000 : ℝ) (44301549121/250000000000 : ℝ) (588603098239/1000000000000 : ℝ) (294301549121/500000000000 : ℝ) (420958663621/1000000000000 : ℝ) (420958663629/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66911/524288 : ℝ))) 1 (588603098239/1000000000000 : ℝ) (294301549121/500000000000 : ℝ) (420958663621/1000000000000 : ℝ) (420958663629/1000000000000 : ℝ) (50478088093/100000000000 : ℝ) (63097610117/125000000000 : ℝ) (248886306191/500000000000 : ℝ) (497772612389/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66911/524288 : ℝ))) 2 (50478088093/100000000000 : ℝ) (63097610117/125000000000 : ℝ) (248886306191/500000000000 : ℝ) (497772612389/1000000000000 : ℝ) (15664898333/31250000000 : ℝ) (501276746663/1000000000000 : ℝ) (501264498823/1000000000000 : ℝ) (501264498831/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66911/524288 : ℝ))) 3 (15664898333/31250000000 : ℝ) (501276746663/1000000000000 : ℝ) (501264498823/1000000000000 : ℝ) (501264498831/1000000000000 : ℝ) (501270622739/1000000000000 : ℝ) (501270622747/1000000000000 : ℝ) (250635311351/500000000000 : ℝ) (50127062271/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66911/524288 : ℝ))) 4 (501270622739/1000000000000 : ℝ) (501270622747/1000000000000 : ℝ) (250635311351/500000000000 : ℝ) (50127062271/100000000000 : ℝ) (195808837/390625000 : ℝ) (501270622729/1000000000000 : ℝ) (195808837/390625000 : ℝ) (501270622729/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66911/524288 : ℝ))) 5 (195808837/390625000 : ℝ) (501270622729/1000000000000 : ℝ) (195808837/390625000 : ℝ) (501270622729/1000000000000 : ℝ) (195808837/390625000 : ℝ) (501270622729/1000000000000 : ℝ) (195808837/390625000 : ℝ) (501270622729/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66911/524288 : ℝ))) 6 (195808837/390625000 : ℝ) (501270622729/1000000000000 : ℝ) (195808837/390625000 : ℝ) (501270622729/1000000000000 : ℝ) (195808837/390625000 : ℝ) (501270622729/1000000000000 : ℝ) (195808837/390625000 : ℝ) (501270622729/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66911/524288 : ℝ))) 7 (195808837/390625000 : ℝ) (501270622729/1000000000000 : ℝ) (195808837/390625000 : ℝ) (501270622729/1000000000000 : ℝ) (195808837/390625000 : ℝ) (501270622729/1000000000000 : ℝ) (195808837/390625000 : ℝ) (501270622729/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66911/524288 : ℝ)) hmem 8 (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ) (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66911/524288 : ℝ))) hcmem 8 (195808837/390625000 : ℝ) (501270622729/1000000000000 : ℝ) (195808837/390625000 : ℝ) (501270622729/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66911/524288 : ℝ)) (496035546919/500000000000 : ℝ) (992071093841/1000000000000 : ℝ) (195808837/390625000 : ℝ) (501270622729/1000000000000 : ℝ) (793687123621/1000000000000 : ℝ) (793687123639/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0838_exp_lower
  have heNumeric : (2054901540227/1000000000000 : ℝ)/4 ≤ Real.exp (-42628251303521/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901540227/1000000000000 : ℝ)/4 ≤ Real.exp ((33455/262144 : ℝ)-(793687123639/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33455/262144 : ℝ) (66911/524288 : ℝ) (793687123639/1000000000000 : ℝ) (2054901540227/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0839; no trusted numerical premise.
theorem cover8_leaf0839_exp_radius : (199601570793324303/200000000000000000 : ℝ) ≤ Real.exp ((-2091/131072 : ℝ)/8) ∧ Real.exp ((-2091/131072 : ℝ)/8) ≤ (249501963491655379/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2091/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0839_exp_lower : (18402268962174059/20000000000000000 : ℝ) ≤ Real.exp ((-85256502660977/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256502660977/128000000000000 : ℝ)/8) ≤ (920113448108702951/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256502660977/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0839_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901539361/1000000000000 : ℝ) ≤ 4*Real.exp (66911/524288 : ℝ)*Real.exp (-mu (radius 8 (2091/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901539361/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2091/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0839_exp_radius
  have hrNumeric : (984173512173/1000000000000 : ℝ) ≤ Real.exp (-2091/131072 : ℝ) ∧ Real.exp (-2091/131072 : ℝ) ≤ (492086756087/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984173512173/1000000000000 : ℝ) ≤ (radius 8 (2091/16384 : ℝ)) ∧ (radius 8 (2091/16384 : ℝ)) ≤ (492086756087/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2091/16384 : ℝ)) (984173512173/1000000000000 : ℝ) (492086756087/500000000000 : ℝ) (88603749829/500000000000 : ℝ) (11075468729/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2091/16384 : ℝ)) (984173512173/1000000000000 : ℝ) (492086756087/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2091/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984173512173/1000000000000 : ℝ) (492086756087/500000000000 : ℝ) (496043378043/500000000000 : ℝ) (992086756087/1000000000000 : ℝ) (248013799033/250000000000 : ℝ) (992055196133/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2091/16384 : ℝ)) 1 (496043378043/500000000000 : ℝ) (992086756087/1000000000000 : ℝ) (248013799033/250000000000 : ℝ) (992055196133/1000000000000 : ℝ) (992070976109/1000000000000 : ℝ) (99207097611/100000000000 : ℝ) (992070975983/1000000000000 : ℝ) (198414195197/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2091/16384 : ℝ)) 2 (992070976109/1000000000000 : ℝ) (99207097611/100000000000 : ℝ) (992070975983/1000000000000 : ℝ) (198414195197/200000000000 : ℝ) (496035488023/500000000000 : ℝ) (62004436003/62500000000 : ℝ) (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2091/16384 : ℝ)) 3 (496035488023/500000000000 : ℝ) (62004436003/62500000000 : ℝ) (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ) (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ) (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2091/16384 : ℝ)) 4 (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ) (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ) (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ) (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2091/16384 : ℝ)) 5 (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ) (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ) (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ) (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2091/16384 : ℝ)) 6 (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ) (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ) (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ) (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2091/16384 : ℝ)) 7 (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ) (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ) (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ) (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2091/16384 : ℝ))) (88603749829/500000000000 : ℝ) (11075468729/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2091/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88603749829/500000000000 : ℝ) (11075468729/62500000000 : ℝ) (588603749829/1000000000000 : ℝ) (73575468729/125000000000 : ℝ) (42096021149/100000000000 : ℝ) (210480105749/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2091/16384 : ℝ))) 1 (588603749829/1000000000000 : ℝ) (73575468729/125000000000 : ℝ) (42096021149/100000000000 : ℝ) (210480105749/500000000000 : ℝ) (504781980659/1000000000000 : ℝ) (100956396133/200000000000 : ℝ) (497773803059/1000000000000 : ℝ) (248886901533/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2091/16384 : ℝ))) 2 (504781980659/1000000000000 : ℝ) (100956396133/200000000000 : ℝ) (497773803059/1000000000000 : ℝ) (248886901533/500000000000 : ℝ) (501277891859/1000000000000 : ℝ) (250638945933/500000000000 : ℝ) (125316411093/250000000000 : ℝ) (25063282219/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2091/16384 : ℝ))) 3 (501277891859/1000000000000 : ℝ) (250638945933/500000000000 : ℝ) (125316411093/250000000000 : ℝ) (25063282219/50000000000 : ℝ) (100254353623/200000000000 : ℝ) (501271768123/1000000000000 : ℝ) (250635884039/500000000000 : ℝ) (250635884043/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2091/16384 : ℝ))) 4 (100254353623/200000000000 : ℝ) (501271768123/1000000000000 : ℝ) (250635884039/500000000000 : ℝ) (250635884043/500000000000 : ℝ) (15664742753/31250000000 : ℝ) (100254353621/200000000000 : ℝ) (15664742753/31250000000 : ℝ) (100254353621/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2091/16384 : ℝ))) 5 (15664742753/31250000000 : ℝ) (100254353621/200000000000 : ℝ) (15664742753/31250000000 : ℝ) (100254353621/200000000000 : ℝ) (15664742753/31250000000 : ℝ) (100254353621/200000000000 : ℝ) (15664742753/31250000000 : ℝ) (100254353621/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2091/16384 : ℝ))) 6 (15664742753/31250000000 : ℝ) (100254353621/200000000000 : ℝ) (15664742753/31250000000 : ℝ) (100254353621/200000000000 : ℝ) (15664742753/31250000000 : ℝ) (100254353621/200000000000 : ℝ) (15664742753/31250000000 : ℝ) (100254353621/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2091/16384 : ℝ))) 7 (15664742753/31250000000 : ℝ) (100254353621/200000000000 : ℝ) (15664742753/31250000000 : ℝ) (100254353621/200000000000 : ℝ) (15664742753/31250000000 : ℝ) (100254353621/200000000000 : ℝ) (15664742753/31250000000 : ℝ) (100254353621/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2091/16384 : ℝ)) hmem 8 (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ) (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2091/16384 : ℝ))) hcmem 8 (15664742753/31250000000 : ℝ) (100254353621/200000000000 : ℝ) (15664742753/31250000000 : ℝ) (100254353621/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2091/16384 : ℝ)) (198414195209/200000000000 : ℝ) (62004436003/62500000000 : ℝ) (15664742753/31250000000 : ℝ) (100254353621/200000000000 : ℝ) (793689031391/1000000000000 : ℝ) (793689031409/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0839_exp_lower
  have heNumeric : (2054901539361/1000000000000 : ℝ)/4 ≤ Real.exp (-85256502660977/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901539361/1000000000000 : ℝ)/4 ≤ Real.exp ((66911/524288 : ℝ)-(793689031409/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66911/524288 : ℝ) (2091/16384 : ℝ) (793689031409/1000000000000 : ℝ) (2054901539361/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0840; no trusted numerical premise.
theorem cover8_leaf0840_exp_radius : (998007824223670149/1000000000000000000 : ℝ) ≤ Real.exp ((-66913/4194304 : ℝ)/8) ∧ Real.exp ((-66913/4194304 : ℝ)/8) ≤ (19960156484473403/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66913/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0840_exp_lower : (184022689612692029/200000000000000000 : ℝ) ≤ Real.exp ((-2664265709729/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664265709729/4000000000000 : ℝ)/8) ≤ (460056724031730073/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664265709729/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0840_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901538553/1000000000000 : ℝ) ≤ 4*Real.exp (2091/16384 : ℝ)*Real.exp (-mu (radius 8 (66913/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901538553/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66913/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0840_exp_radius
  have hrNumeric : (123021659691/125000000000 : ℝ) ≤ Real.exp (-66913/4194304 : ℝ) ∧ Real.exp (-66913/4194304 : ℝ) ≤ (984173277529/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123021659691/125000000000 : ℝ) ≤ (radius 8 (66913/524288 : ℝ)) ∧ (radius 8 (66913/524288 : ℝ)) ≤ (984173277529/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66913/524288 : ℝ)) (123021659691/125000000000 : ℝ) (984173277529/1000000000000 : ℝ) (88604401411/500000000000 : ℝ) (177208802829/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66913/524288 : ℝ)) (123021659691/125000000000 : ℝ) (984173277529/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66913/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123021659691/125000000000 : ℝ) (984173277529/1000000000000 : ℝ) (248021659691/250000000000 : ℝ) (198417327753/200000000000 : ℝ) (99205507787/100000000000 : ℝ) (992055077871/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66913/524288 : ℝ)) 1 (248021659691/250000000000 : ℝ) (198417327753/200000000000 : ℝ) (99205507787/100000000000 : ℝ) (992055077871/1000000000000 : ℝ) (992070858317/1000000000000 : ℝ) (496035429159/500000000000 : ℝ) (992070858191/1000000000000 : ℝ) (992070858193/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66913/524288 : ℝ)) 2 (992070858317/1000000000000 : ℝ) (496035429159/500000000000 : ℝ) (992070858191/1000000000000 : ℝ) (992070858193/1000000000000 : ℝ) (496035429127/500000000000 : ℝ) (62004428641/62500000000 : ℝ) (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66913/524288 : ℝ)) 3 (496035429127/500000000000 : ℝ) (62004428641/62500000000 : ℝ) (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ) (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ) (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66913/524288 : ℝ)) 4 (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ) (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ) (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ) (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66913/524288 : ℝ)) 5 (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ) (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ) (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ) (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66913/524288 : ℝ)) 6 (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ) (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ) (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ) (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66913/524288 : ℝ)) 7 (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ) (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ) (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ) (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66913/524288 : ℝ))) (88604401411/500000000000 : ℝ) (177208802829/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66913/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88604401411/500000000000 : ℝ) (177208802829/1000000000000 : ℝ) (588604401411/1000000000000 : ℝ) (117720880283/200000000000 : ℝ) (210480879667/500000000000 : ℝ) (420961759343/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66913/524288 : ℝ))) 1 (588604401411/1000000000000 : ℝ) (117720880283/200000000000 : ℝ) (210480879667/500000000000 : ℝ) (420961759343/1000000000000 : ℝ) (126195770093/250000000000 : ℝ) (504783080379/1000000000000 : ℝ) (124443748429/250000000000 : ℝ) (124443748431/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66913/524288 : ℝ))) 2 (126195770093/250000000000 : ℝ) (504783080379/1000000000000 : ℝ) (124443748429/250000000000 : ℝ) (124443748431/250000000000 : ℝ) (125319759261/250000000000 : ℝ) (125319759263/250000000000 : ℝ) (501266789903/1000000000000 : ℝ) (501266789911/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66913/524288 : ℝ))) 3 (125319759261/250000000000 : ℝ) (125319759263/250000000000 : ℝ) (501266789903/1000000000000 : ℝ) (501266789911/1000000000000 : ℝ) (501272913473/1000000000000 : ℝ) (250636456741/500000000000 : ℝ) (125318228359/250000000000 : ℝ) (100254582689/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66913/524288 : ℝ))) 4 (501272913473/1000000000000 : ℝ) (250636456741/500000000000 : ℝ) (125318228359/250000000000 : ℝ) (100254582689/200000000000 : ℝ) (250636456727/500000000000 : ℝ) (62659114183/125000000000 : ℝ) (250636456727/500000000000 : ℝ) (62659114183/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66913/524288 : ℝ))) 5 (250636456727/500000000000 : ℝ) (62659114183/125000000000 : ℝ) (250636456727/500000000000 : ℝ) (62659114183/125000000000 : ℝ) (250636456727/500000000000 : ℝ) (62659114183/125000000000 : ℝ) (250636456727/500000000000 : ℝ) (62659114183/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66913/524288 : ℝ))) 6 (250636456727/500000000000 : ℝ) (62659114183/125000000000 : ℝ) (250636456727/500000000000 : ℝ) (62659114183/125000000000 : ℝ) (250636456727/500000000000 : ℝ) (62659114183/125000000000 : ℝ) (250636456727/500000000000 : ℝ) (62659114183/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66913/524288 : ℝ))) 7 (250636456727/500000000000 : ℝ) (62659114183/125000000000 : ℝ) (250636456727/500000000000 : ℝ) (62659114183/125000000000 : ℝ) (250636456727/500000000000 : ℝ) (62659114183/125000000000 : ℝ) (250636456727/500000000000 : ℝ) (62659114183/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66913/524288 : ℝ)) hmem 8 (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ) (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66913/524288 : ℝ))) hcmem 8 (250636456727/500000000000 : ℝ) (62659114183/125000000000 : ℝ) (250636456727/500000000000 : ℝ) (62659114183/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66913/524288 : ℝ)) (992070858253/1000000000000 : ℝ) (62004428641/62500000000 : ℝ) (250636456727/500000000000 : ℝ) (62659114183/125000000000 : ℝ) (198422734783/250000000000 : ℝ) (793690939151/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0840_exp_lower
  have heNumeric : (2054901538553/1000000000000 : ℝ)/4 ≤ Real.exp (-2664265709729/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901538553/1000000000000 : ℝ)/4 ≤ Real.exp ((2091/16384 : ℝ)-(793690939151/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2091/16384 : ℝ) (66913/524288 : ℝ) (793690939151/1000000000000 : ℝ) (2054901538553/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0841; no trusted numerical premise.
theorem cover8_leaf0841_exp_radius : (998007794480719669/1000000000000000000 : ℝ) ≤ Real.exp ((-33457/2097152 : ℝ)/8) ∧ Real.exp ((-33457/2097152 : ℝ)/8) ≤ (99800779448071967/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33457/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0841_exp_lower : (184022689604057519/200000000000000000 : ℝ) ≤ Real.exp ((-27282080883/40960000000 : ℝ)/8) ∧ Real.exp ((-27282080883/40960000000 : ℝ)/8) ≤ (230028362005071899/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-27282080883/40960000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0841_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450768891/500000000000 : ℝ) ≤ 4*Real.exp (66913/524288 : ℝ)*Real.exp (-mu (radius 8 (33457/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450768891/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33457/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0841_exp_radius
  have hrNumeric : (984173042883/1000000000000 : ℝ) ≤ Real.exp (-33457/2097152 : ℝ) ∧ Real.exp (-33457/2097152 : ℝ) ≤ (246043260721/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984173042883/1000000000000 : ℝ) ≤ (radius 8 (33457/262144 : ℝ)) ∧ (radius 8 (33457/262144 : ℝ)) ≤ (246043260721/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33457/262144 : ℝ)) (984173042883/1000000000000 : ℝ) (246043260721/250000000000 : ℝ) (177210105977/1000000000000 : ℝ) (177210105983/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33457/262144 : ℝ)) (984173042883/1000000000000 : ℝ) (246043260721/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33457/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984173042883/1000000000000 : ℝ) (246043260721/250000000000 : ℝ) (992086521441/1000000000000 : ℝ) (496043260721/500000000000 : ℝ) (124006869951/125000000000 : ℝ) (992054959609/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33457/262144 : ℝ)) 1 (992086521441/1000000000000 : ℝ) (496043260721/500000000000 : ℝ) (124006869951/125000000000 : ℝ) (992054959609/1000000000000 : ℝ) (248017685131/250000000000 : ℝ) (496035370263/500000000000 : ℝ) (496035370199/500000000000 : ℝ) (2480176851/2500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33457/262144 : ℝ)) 2 (248017685131/250000000000 : ℝ) (496035370263/500000000000 : ℝ) (496035370199/500000000000 : ℝ) (2480176851/2500000000 : ℝ) (992070740461/1000000000000 : ℝ) (992070740463/1000000000000 : ℝ) (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33457/262144 : ℝ)) 3 (992070740461/1000000000000 : ℝ) (992070740463/1000000000000 : ℝ) (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ) (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ) (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33457/262144 : ℝ)) 4 (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ) (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ) (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ) (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33457/262144 : ℝ)) 5 (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ) (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ) (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ) (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33457/262144 : ℝ)) 6 (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ) (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ) (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ) (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33457/262144 : ℝ)) 7 (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ) (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ) (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ) (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33457/262144 : ℝ))) (177210105977/1000000000000 : ℝ) (177210105983/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33457/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177210105977/1000000000000 : ℝ) (177210105983/1000000000000 : ℝ) (147151263247/250000000000 : ℝ) (9196953953/15625000000 : ℝ) (210481653581/500000000000 : ℝ) (42096330717/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33457/262144 : ℝ))) 1 (147151263247/250000000000 : ℝ) (9196953953/15625000000 : ℝ) (210481653581/500000000000 : ℝ) (42096330717/100000000000 : ℝ) (20191367203/40000000000 : ℝ) (504784180081/1000000000000 : ℝ) (248888092181/500000000000 : ℝ) (497776184369/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33457/262144 : ℝ))) 2 (20191367203/40000000000 : ℝ) (504784180081/1000000000000 : ℝ) (248888092181/500000000000 : ℝ) (497776184369/1000000000000 : ℝ) (250640091109/500000000000 : ℝ) (20051207289/40000000000 : ℝ) (501267935423/1000000000000 : ℝ) (501267935431/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33457/262144 : ℝ))) 3 (250640091109/500000000000 : ℝ) (20051207289/40000000000 : ℝ) (501267935423/1000000000000 : ℝ) (501267935431/1000000000000 : ℝ) (25063702941/50000000000 : ℝ) (125318514707/250000000000 : ℝ) (501274058783/1000000000000 : ℝ) (501274058791/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33457/262144 : ℝ))) 4 (25063702941/50000000000 : ℝ) (125318514707/250000000000 : ℝ) (501274058783/1000000000000 : ℝ) (501274058791/1000000000000 : ℝ) (501274058801/1000000000000 : ℝ) (50127405881/100000000000 : ℝ) (501274058801/1000000000000 : ℝ) (50127405881/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33457/262144 : ℝ))) 5 (501274058801/1000000000000 : ℝ) (50127405881/100000000000 : ℝ) (501274058801/1000000000000 : ℝ) (50127405881/100000000000 : ℝ) (501274058801/1000000000000 : ℝ) (50127405881/100000000000 : ℝ) (501274058801/1000000000000 : ℝ) (50127405881/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33457/262144 : ℝ))) 6 (501274058801/1000000000000 : ℝ) (50127405881/100000000000 : ℝ) (501274058801/1000000000000 : ℝ) (50127405881/100000000000 : ℝ) (501274058801/1000000000000 : ℝ) (50127405881/100000000000 : ℝ) (501274058801/1000000000000 : ℝ) (50127405881/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33457/262144 : ℝ))) 7 (501274058801/1000000000000 : ℝ) (50127405881/100000000000 : ℝ) (501274058801/1000000000000 : ℝ) (50127405881/100000000000 : ℝ) (501274058801/1000000000000 : ℝ) (50127405881/100000000000 : ℝ) (501274058801/1000000000000 : ℝ) (50127405881/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33457/262144 : ℝ)) hmem 8 (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ) (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33457/262144 : ℝ))) hcmem 8 (501274058801/1000000000000 : ℝ) (50127405881/100000000000 : ℝ) (501274058801/1000000000000 : ℝ) (50127405881/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33457/262144 : ℝ)) (49603537023/50000000000 : ℝ) (992070740463/1000000000000 : ℝ) (501274058801/1000000000000 : ℝ) (50127405881/100000000000 : ℝ) (793692846857/1000000000000 : ℝ) (253981711/320000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0841_exp_lower
  have heNumeric : (1027450768891/500000000000 : ℝ)/4 ≤ Real.exp (-27282080883/40960000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450768891/500000000000 : ℝ)/4 ≤ Real.exp ((66913/524288 : ℝ)-(253981711/320000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66913/524288 : ℝ) (33457/262144 : ℝ) (253981711/320000000 : ℝ) (1027450768891/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0842; no trusted numerical premise.
theorem cover8_leaf0842_exp_radius : (249501941184442519/250000000000000000 : ℝ) ≤ Real.exp ((-66915/4194304 : ℝ)/8) ∧ Real.exp ((-66915/4194304 : ℝ)/8) ≤ (998007764737770077/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66915/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0842_exp_lower : (184022689595860063/200000000000000000 : ℝ) ≤ Real.exp ((-8525650280499/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525650280499/12800000000000 : ℝ)/8) ≤ (230028361994825079/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525650280499/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0842_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901537049/1000000000000 : ℝ) ≤ 4*Real.exp (33457/262144 : ℝ)*Real.exp (-mu (radius 8 (66915/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901537049/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66915/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0842_exp_radius
  have hrNumeric : (492086404119/500000000000 : ℝ) ≤ Real.exp (-66915/4194304 : ℝ) ∧ Real.exp (-66915/4194304 : ℝ) ≤ (984172808239/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492086404119/500000000000 : ℝ) ≤ (radius 8 (66915/524288 : ℝ)) ∧ (radius 8 (66915/524288 : ℝ)) ≤ (984172808239/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66915/524288 : ℝ)) (492086404119/500000000000 : ℝ) (984172808239/1000000000000 : ℝ) (177211409121/1000000000000 : ℝ) (22151426141/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66915/524288 : ℝ)) (492086404119/500000000000 : ℝ) (984172808239/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66915/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492086404119/500000000000 : ℝ) (984172808239/1000000000000 : ℝ) (992086404119/1000000000000 : ℝ) (24802160103/25000000000 : ℝ) (198410968269/200000000000 : ℝ) (992054841347/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66915/524288 : ℝ)) 1 (992086404119/1000000000000 : ℝ) (24802160103/25000000000 : ℝ) (198410968269/200000000000 : ℝ) (992054841347/1000000000000 : ℝ) (248017655683/250000000000 : ℝ) (496035311367/500000000000 : ℝ) (496035311303/500000000000 : ℝ) (62004413913/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66915/524288 : ℝ)) 2 (248017655683/250000000000 : ℝ) (496035311367/500000000000 : ℝ) (496035311303/500000000000 : ℝ) (62004413913/62500000000 : ℝ) (992070622669/1000000000000 : ℝ) (992070622671/1000000000000 : ℝ) (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66915/524288 : ℝ)) 3 (992070622669/1000000000000 : ℝ) (992070622671/1000000000000 : ℝ) (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ) (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ) (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66915/524288 : ℝ)) 4 (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ) (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ) (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ) (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66915/524288 : ℝ)) 5 (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ) (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ) (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ) (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66915/524288 : ℝ)) 6 (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ) (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ) (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ) (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66915/524288 : ℝ)) 7 (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ) (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ) (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ) (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66915/524288 : ℝ))) (177211409121/1000000000000 : ℝ) (22151426141/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66915/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177211409121/1000000000000 : ℝ) (22151426141/125000000000 : ℝ) (7357571307/12500000000 : ℝ) (147151426141/250000000000 : ℝ) (420964854971/1000000000000 : ℝ) (21048242749/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66915/524288 : ℝ))) 1 (7357571307/12500000000 : ℝ) (147151426141/250000000000 : ℝ) (420964854971/1000000000000 : ℝ) (21048242749/50000000000 : ℝ) (100957055953/200000000000 : ℝ) (126196319943/250000000000 : ℝ) (497777374993/1000000000000 : ℝ) (497777375001/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66915/524288 : ℝ))) 2 (100957055953/200000000000 : ℝ) (126196319943/250000000000 : ℝ) (497777374993/1000000000000 : ℝ) (497777375001/1000000000000 : ℝ) (501281327379/1000000000000 : ℝ) (501281327387/1000000000000 : ℝ) (50126908093/100000000000 : ℝ) (250634540469/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66915/524288 : ℝ))) 3 (501281327379/1000000000000 : ℝ) (501281327387/1000000000000 : ℝ) (50126908093/100000000000 : ℝ) (250634540469/500000000000 : ℝ) (250637602077/500000000000 : ℝ) (501275204163/1000000000000 : ℝ) (501275204117/1000000000000 : ℝ) (250637602063/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66915/524288 : ℝ))) 4 (250637602077/500000000000 : ℝ) (501275204163/1000000000000 : ℝ) (501275204117/1000000000000 : ℝ) (250637602063/500000000000 : ℝ) (100255040827/200000000000 : ℝ) (100255040829/200000000000 : ℝ) (100255040827/200000000000 : ℝ) (100255040829/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66915/524288 : ℝ))) 5 (100255040827/200000000000 : ℝ) (100255040829/200000000000 : ℝ) (100255040827/200000000000 : ℝ) (100255040829/200000000000 : ℝ) (100255040827/200000000000 : ℝ) (100255040829/200000000000 : ℝ) (100255040827/200000000000 : ℝ) (100255040829/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66915/524288 : ℝ))) 6 (100255040827/200000000000 : ℝ) (100255040829/200000000000 : ℝ) (100255040827/200000000000 : ℝ) (100255040829/200000000000 : ℝ) (100255040827/200000000000 : ℝ) (100255040829/200000000000 : ℝ) (100255040827/200000000000 : ℝ) (100255040829/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66915/524288 : ℝ))) 7 (100255040827/200000000000 : ℝ) (100255040829/200000000000 : ℝ) (100255040827/200000000000 : ℝ) (100255040829/200000000000 : ℝ) (100255040827/200000000000 : ℝ) (100255040829/200000000000 : ℝ) (100255040827/200000000000 : ℝ) (100255040829/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66915/524288 : ℝ)) hmem 8 (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ) (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66915/524288 : ℝ))) hcmem 8 (100255040827/200000000000 : ℝ) (100255040829/200000000000 : ℝ) (100255040827/200000000000 : ℝ) (100255040829/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66915/524288 : ℝ)) (248017655667/250000000000 : ℝ) (992070622671/1000000000000 : ℝ) (100255040827/200000000000 : ℝ) (100255040829/200000000000 : ℝ) (793694754561/1000000000000 : ℝ) (39684737729/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0842_exp_lower
  have heNumeric : (2054901537049/1000000000000 : ℝ)/4 ≤ Real.exp (-8525650280499/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901537049/1000000000000 : ℝ)/4 ≤ Real.exp ((33457/262144 : ℝ)-(39684737729/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33457/262144 : ℝ) (66915/524288 : ℝ) (39684737729/50000000000 : ℝ) (2054901537049/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0843; no trusted numerical premise.
theorem cover8_leaf0843_exp_radius : (998007734994821369/1000000000000000000 : ℝ) ≤ Real.exp ((-16729/1048576 : ℝ)/8) ∧ Real.exp ((-16729/1048576 : ℝ)/8) ≤ (99800773499482137/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16729/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0843_exp_lower : (230028361985067069/250000000000000000 : ℝ) ≤ Real.exp ((-85256502848429/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256502848429/128000000000000 : ℝ)/8) ≤ (920113447940268277/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256502848429/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0843_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (64215673011/31250000000 : ℝ) ≤ 4*Real.exp (66915/524288 : ℝ)*Real.exp (-mu (radius 8 (16729/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (64215673011/31250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16729/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0843_exp_radius
  have hrNumeric : (984172573593/1000000000000 : ℝ) ≤ Real.exp (-16729/1048576 : ℝ) ∧ Real.exp (-16729/1048576 : ℝ) ≤ (492086286797/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984172573593/1000000000000 : ℝ) ≤ (radius 8 (16729/131072 : ℝ)) ∧ (radius 8 (16729/131072 : ℝ)) ≤ (492086286797/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16729/131072 : ℝ)) (984172573593/1000000000000 : ℝ) (492086286797/500000000000 : ℝ) (2768948629/15625000000 : ℝ) (177212712263/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16729/131072 : ℝ)) (984172573593/1000000000000 : ℝ) (492086286797/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16729/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984172573593/1000000000000 : ℝ) (492086286797/500000000000 : ℝ) (248021571699/250000000000 : ℝ) (992086286797/1000000000000 : ℝ) (992054723083/1000000000000 : ℝ) (198410944617/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16729/131072 : ℝ)) 1 (248021571699/250000000000 : ℝ) (992086286797/1000000000000 : ℝ) (992054723083/1000000000000 : ℝ) (198410944617/200000000000 : ℝ) (992070504939/1000000000000 : ℝ) (992070504941/1000000000000 : ℝ) (992070504813/1000000000000 : ℝ) (62004406551/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16729/131072 : ℝ)) 2 (992070504939/1000000000000 : ℝ) (992070504941/1000000000000 : ℝ) (992070504813/1000000000000 : ℝ) (62004406551/62500000000 : ℝ) (248017626219/250000000000 : ℝ) (992070504879/1000000000000 : ℝ) (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16729/131072 : ℝ)) 3 (248017626219/250000000000 : ℝ) (992070504879/1000000000000 : ℝ) (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ) (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ) (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16729/131072 : ℝ)) 4 (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ) (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ) (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ) (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16729/131072 : ℝ)) 5 (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ) (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ) (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ) (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16729/131072 : ℝ)) 6 (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ) (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ) (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ) (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16729/131072 : ℝ)) 7 (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ) (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ) (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ) (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16729/131072 : ℝ))) (2768948629/15625000000 : ℝ) (177212712263/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16729/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2768948629/15625000000 : ℝ) (177212712263/1000000000000 : ℝ) (18393948629/31250000000 : ℝ) (147151589033/250000000000 : ℝ) (420966402763/1000000000000 : ℝ) (420966402773/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16729/131072 : ℝ))) 1 (18393948629/31250000000 : ℝ) (147151589033/250000000000 : ℝ) (420966402763/1000000000000 : ℝ) (420966402773/1000000000000 : ℝ) (100957275889/200000000000 : ℝ) (504786379453/1000000000000 : ℝ) (497778565611/1000000000000 : ℝ) (24888928281/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16729/131072 : ℝ))) 2 (100957275889/200000000000 : ℝ) (504786379453/1000000000000 : ℝ) (497778565611/1000000000000 : ℝ) (24888928281/50000000000 : ℝ) (31330154533/62500000000 : ℝ) (501282472537/1000000000000 : ℝ) (62658778303/125000000000 : ℝ) (250635113217/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16729/131072 : ℝ))) 3 (31330154533/62500000000 : ℝ) (501282472537/1000000000000 : ℝ) (62658778303/125000000000 : ℝ) (250635113217/500000000000 : ℝ) (125319087369/250000000000 : ℝ) (250638174743/500000000000 : ℝ) (250638174719/500000000000 : ℝ) (501276349449/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16729/131072 : ℝ))) 4 (125319087369/250000000000 : ℝ) (250638174743/500000000000 : ℝ) (250638174719/500000000000 : ℝ) (501276349449/1000000000000 : ℝ) (501276349457/1000000000000 : ℝ) (125319087367/250000000000 : ℝ) (31329771841/62500000000 : ℝ) (125319087367/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16729/131072 : ℝ))) 5 (501276349457/1000000000000 : ℝ) (125319087367/250000000000 : ℝ) (31329771841/62500000000 : ℝ) (125319087367/250000000000 : ℝ) (31329771841/62500000000 : ℝ) (125319087367/250000000000 : ℝ) (31329771841/62500000000 : ℝ) (125319087367/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16729/131072 : ℝ))) 6 (31329771841/62500000000 : ℝ) (125319087367/250000000000 : ℝ) (31329771841/62500000000 : ℝ) (125319087367/250000000000 : ℝ) (31329771841/62500000000 : ℝ) (125319087367/250000000000 : ℝ) (31329771841/62500000000 : ℝ) (125319087367/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16729/131072 : ℝ))) 7 (31329771841/62500000000 : ℝ) (125319087367/250000000000 : ℝ) (31329771841/62500000000 : ℝ) (125319087367/250000000000 : ℝ) (31329771841/62500000000 : ℝ) (125319087367/250000000000 : ℝ) (31329771841/62500000000 : ℝ) (125319087367/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16729/131072 : ℝ)) hmem 8 (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ) (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16729/131072 : ℝ))) hcmem 8 (31329771841/62500000000 : ℝ) (125319087367/250000000000 : ℝ) (31329771841/62500000000 : ℝ) (125319087367/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16729/131072 : ℝ)) (7936564039/8000000000 : ℝ) (992070504879/1000000000000 : ℝ) (31329771841/62500000000 : ℝ) (125319087367/250000000000 : ℝ) (158739332449/200000000000 : ℝ) (198424165567/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0843_exp_lower
  have heNumeric : (64215673011/31250000000 : ℝ)/4 ≤ Real.exp (-85256502848429/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (64215673011/31250000000 : ℝ)/4 ≤ Real.exp ((66915/524288 : ℝ)-(198424165567/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66915/524288 : ℝ) (16729/131072 : ℝ) (198424165567/250000000000 : ℝ) (64215673011/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0844; no trusted numerical premise.
theorem cover8_leaf0844_exp_radius : (249501926312968387/250000000000000000 : ℝ) ≤ Real.exp ((-66917/4194304 : ℝ)/8) ∧ Real.exp ((-66917/4194304 : ℝ)/8) ≤ (998007705251873549/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66917/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0844_exp_lower : (920113447903766549/1000000000000000000 : ℝ) ≤ Real.exp ((-21314125722263/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314125722263/32000000000000 : ℝ)/8) ≤ (18402268958075331/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314125722263/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0844_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (20549015357/10000000000 : ℝ) ≤ 4*Real.exp (16729/131072 : ℝ)*Real.exp (-mu (radius 8 (66917/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (20549015357/10000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66917/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0844_exp_radius
  have hrNumeric : (246043084737/250000000000 : ℝ) ≤ Real.exp (-66917/4194304 : ℝ) ∧ Real.exp (-66917/4194304 : ℝ) ≤ (984172338949/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246043084737/250000000000 : ℝ) ≤ (radius 8 (66917/524288 : ℝ)) ∧ (radius 8 (66917/524288 : ℝ)) ≤ (984172338949/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66917/524288 : ℝ)) (246043084737/250000000000 : ℝ) (984172338949/1000000000000 : ℝ) (177214015381/1000000000000 : ℝ) (44303503847/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66917/524288 : ℝ)) (246043084737/250000000000 : ℝ) (984172338949/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66917/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246043084737/250000000000 : ℝ) (984172338949/1000000000000 : ℝ) (496043084737/500000000000 : ℝ) (39683446779/40000000000 : ℝ) (992054604821/1000000000000 : ℝ) (992054604823/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66917/524288 : ℝ)) 1 (496043084737/500000000000 : ℝ) (39683446779/40000000000 : ℝ) (992054604821/1000000000000 : ℝ) (992054604823/1000000000000 : ℝ) (992070387147/1000000000000 : ℝ) (992070387149/1000000000000 : ℝ) (992070387021/1000000000000 : ℝ) (62004399189/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66917/524288 : ℝ)) 2 (992070387147/1000000000000 : ℝ) (992070387149/1000000000000 : ℝ) (992070387021/1000000000000 : ℝ) (62004399189/62500000000 : ℝ) (248017596771/250000000000 : ℝ) (992070387087/1000000000000 : ℝ) (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66917/524288 : ℝ)) 3 (248017596771/250000000000 : ℝ) (992070387087/1000000000000 : ℝ) (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ) (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ) (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66917/524288 : ℝ)) 4 (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ) (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ) (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ) (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66917/524288 : ℝ)) 5 (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ) (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ) (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ) (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66917/524288 : ℝ)) 6 (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ) (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ) (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ) (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66917/524288 : ℝ)) 7 (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ) (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ) (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ) (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66917/524288 : ℝ))) (177214015381/1000000000000 : ℝ) (44303503847/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66917/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177214015381/1000000000000 : ℝ) (44303503847/250000000000 : ℝ) (58860700769/100000000000 : ℝ) (294303503847/500000000000 : ℝ) (210483975269/500000000000 : ℝ) (105241987637/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66917/524288 : ℝ))) 1 (58860700769/100000000000 : ℝ) (294303503847/500000000000 : ℝ) (210483975269/500000000000 : ℝ) (105241987637/250000000000 : ℝ) (252393739557/500000000000 : ℝ) (504787479121/1000000000000 : ℝ) (497779756217/1000000000000 : ℝ) (19911190249/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66917/524288 : ℝ))) 2 (252393739557/500000000000 : ℝ) (504787479121/1000000000000 : ℝ) (497779756217/1000000000000 : ℝ) (19911190249/40000000000 : ℝ) (100256723533/200000000000 : ℝ) (501283617673/1000000000000 : ℝ) (125317842977/250000000000 : ℝ) (125317842979/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66917/524288 : ℝ))) 3 (100256723533/200000000000 : ℝ) (501283617673/1000000000000 : ℝ) (125317842977/250000000000 : ℝ) (125317842979/250000000000 : ℝ) (250638747393/500000000000 : ℝ) (100255498959/200000000000 : ℝ) (501277494749/1000000000000 : ℝ) (250638747379/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66917/524288 : ℝ))) 4 (250638747393/500000000000 : ℝ) (100255498959/200000000000 : ℝ) (501277494749/1000000000000 : ℝ) (250638747379/500000000000 : ℝ) (501277494767/1000000000000 : ℝ) (501277494777/1000000000000 : ℝ) (501277494767/1000000000000 : ℝ) (501277494777/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66917/524288 : ℝ))) 5 (501277494767/1000000000000 : ℝ) (501277494777/1000000000000 : ℝ) (501277494767/1000000000000 : ℝ) (501277494777/1000000000000 : ℝ) (501277494767/1000000000000 : ℝ) (501277494777/1000000000000 : ℝ) (501277494767/1000000000000 : ℝ) (501277494777/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66917/524288 : ℝ))) 6 (501277494767/1000000000000 : ℝ) (501277494777/1000000000000 : ℝ) (501277494767/1000000000000 : ℝ) (501277494777/1000000000000 : ℝ) (501277494767/1000000000000 : ℝ) (501277494777/1000000000000 : ℝ) (501277494767/1000000000000 : ℝ) (501277494777/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66917/524288 : ℝ))) 7 (501277494767/1000000000000 : ℝ) (501277494777/1000000000000 : ℝ) (501277494767/1000000000000 : ℝ) (501277494777/1000000000000 : ℝ) (501277494767/1000000000000 : ℝ) (501277494777/1000000000000 : ℝ) (501277494767/1000000000000 : ℝ) (501277494777/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66917/524288 : ℝ)) hmem 8 (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ) (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66917/524288 : ℝ))) hcmem 8 (501277494767/1000000000000 : ℝ) (501277494777/1000000000000 : ℝ) (501277494767/1000000000000 : ℝ) (501277494777/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66917/524288 : ℝ)) (992070387083/1000000000000 : ℝ) (992070387087/1000000000000 : ℝ) (501277494767/1000000000000 : ℝ) (501277494777/1000000000000 : ℝ) (793698569913/1000000000000 : ℝ) (396849284967/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0844_exp_lower
  have heNumeric : (20549015357/10000000000 : ℝ)/4 ≤ Real.exp (-21314125722263/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (20549015357/10000000000 : ℝ)/4 ≤ Real.exp ((16729/131072 : ℝ)-(396849284967/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16729/131072 : ℝ) (66917/524288 : ℝ) (396849284967/500000000000 : ℝ) (20549015357/10000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0845; no trusted numerical premise.
theorem cover8_leaf0845_exp_radius : (499003837754463307/500000000000000000 : ℝ) ≤ Real.exp ((-33459/2097152 : ℝ)/8) ∧ Real.exp ((-33459/2097152 : ℝ)/8) ≤ (199601535101785323/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33459/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0845_exp_lower : (920113447869335077/1000000000000000000 : ℝ) ≤ Real.exp ((-85256502927371/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256502927371/128000000000000 : ℝ)/8) ≤ (460056723934667539/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256502927371/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0845_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980307017/200000000000 : ℝ) ≤ 4*Real.exp (66917/524288 : ℝ)*Real.exp (-mu (radius 8 (33459/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980307017/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33459/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0845_exp_radius
  have hrNumeric : (984172104303/1000000000000 : ℝ) ≤ Real.exp (-33459/2097152 : ℝ) ∧ Real.exp (-33459/2097152 : ℝ) ≤ (61510756519/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984172104303/1000000000000 : ℝ) ≤ (radius 8 (33459/262144 : ℝ)) ∧ (radius 8 (33459/262144 : ℝ)) ≤ (61510756519/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33459/262144 : ℝ)) (984172104303/1000000000000 : ℝ) (61510756519/62500000000 : ℝ) (5537978703/31250000000 : ℝ) (177215318503/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33459/262144 : ℝ)) (984172104303/1000000000000 : ℝ) (61510756519/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33459/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984172104303/1000000000000 : ℝ) (61510756519/62500000000 : ℝ) (992086052151/1000000000000 : ℝ) (124010756519/125000000000 : ℝ) (992054486559/1000000000000 : ℝ) (992054486561/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33459/262144 : ℝ)) 1 (992086052151/1000000000000 : ℝ) (124010756519/125000000000 : ℝ) (992054486559/1000000000000 : ℝ) (992054486561/1000000000000 : ℝ) (198414053871/200000000000 : ℝ) (992070269357/1000000000000 : ℝ) (992070269229/1000000000000 : ℝ) (992070269231/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33459/262144 : ℝ)) 2 (198414053871/200000000000 : ℝ) (992070269357/1000000000000 : ℝ) (992070269229/1000000000000 : ℝ) (992070269231/1000000000000 : ℝ) (248017567323/250000000000 : ℝ) (496035134647/500000000000 : ℝ) (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33459/262144 : ℝ)) 3 (248017567323/250000000000 : ℝ) (496035134647/500000000000 : ℝ) (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ) (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ) (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33459/262144 : ℝ)) 4 (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ) (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ) (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ) (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33459/262144 : ℝ)) 5 (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ) (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ) (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ) (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33459/262144 : ℝ)) 6 (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ) (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ) (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ) (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33459/262144 : ℝ)) 7 (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ) (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ) (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ) (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33459/262144 : ℝ))) (5537978703/31250000000 : ℝ) (177215318503/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33459/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5537978703/31250000000 : ℝ) (177215318503/1000000000000 : ℝ) (36787978703/62500000000 : ℝ) (147151914813/250000000000 : ℝ) (52621187287/125000000000 : ℝ) (84193899661/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33459/262144 : ℝ))) 1 (36787978703/62500000000 : ℝ) (147151914813/250000000000 : ℝ) (52621187287/125000000000 : ℝ) (84193899661/200000000000 : ℝ) (126197144693/250000000000 : ℝ) (504788578779/1000000000000 : ℝ) (497780946809/1000000000000 : ℝ) (497780946817/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33459/262144 : ℝ))) 2 (126197144693/250000000000 : ℝ) (504788578779/1000000000000 : ℝ) (497780946809/1000000000000 : ℝ) (497780946817/1000000000000 : ℝ) (50128476279/100000000000 : ℝ) (250642381399/500000000000 : ℝ) (501272517379/1000000000000 : ℝ) (501272517387/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33459/262144 : ℝ))) 3 (50128476279/100000000000 : ℝ) (250642381399/500000000000 : ℝ) (501272517379/1000000000000 : ℝ) (501272517387/1000000000000 : ℝ) (125319660021/250000000000 : ℝ) (501278640093/1000000000000 : ℝ) (501278640047/1000000000000 : ℝ) (62659830007/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33459/262144 : ℝ))) 4 (125319660021/250000000000 : ℝ) (501278640093/1000000000000 : ℝ) (501278640047/1000000000000 : ℝ) (62659830007/125000000000 : ℝ) (100255728013/200000000000 : ℝ) (20051145603/40000000000 : ℝ) (100255728013/200000000000 : ℝ) (20051145603/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33459/262144 : ℝ))) 5 (100255728013/200000000000 : ℝ) (20051145603/40000000000 : ℝ) (100255728013/200000000000 : ℝ) (20051145603/40000000000 : ℝ) (100255728013/200000000000 : ℝ) (20051145603/40000000000 : ℝ) (100255728013/200000000000 : ℝ) (20051145603/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33459/262144 : ℝ))) 6 (100255728013/200000000000 : ℝ) (20051145603/40000000000 : ℝ) (100255728013/200000000000 : ℝ) (20051145603/40000000000 : ℝ) (100255728013/200000000000 : ℝ) (20051145603/40000000000 : ℝ) (100255728013/200000000000 : ℝ) (20051145603/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33459/262144 : ℝ))) 7 (100255728013/200000000000 : ℝ) (20051145603/40000000000 : ℝ) (100255728013/200000000000 : ℝ) (20051145603/40000000000 : ℝ) (100255728013/200000000000 : ℝ) (20051145603/40000000000 : ℝ) (100255728013/200000000000 : ℝ) (20051145603/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33459/262144 : ℝ)) hmem 8 (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ) (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33459/262144 : ℝ))) hcmem 8 (100255728013/200000000000 : ℝ) (20051145603/40000000000 : ℝ) (100255728013/200000000000 : ℝ) (20051145603/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33459/262144 : ℝ)) (992070269291/1000000000000 : ℝ) (496035134647/500000000000 : ℝ) (100255728013/200000000000 : ℝ) (20051145603/40000000000 : ℝ) (793700477563/1000000000000 : ℝ) (396850238791/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0845_exp_lower
  have heNumeric : (410980307017/200000000000 : ℝ)/4 ≤ Real.exp (-85256502927371/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980307017/200000000000 : ℝ)/4 ≤ Real.exp ((66917/524288 : ℝ)-(396850238791/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66917/524288 : ℝ) (33459/262144 : ℝ) (396850238791/500000000000 : ℝ) (410980307017/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0846; no trusted numerical premise.
theorem cover8_leaf0846_exp_radius : (499003822882990283/500000000000000000 : ℝ) ≤ Real.exp ((-66919/4194304 : ℝ)/8) ∧ Real.exp ((-66919/4194304 : ℝ)/8) ≤ (998007645765980567/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66919/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0846_exp_lower : (920113447837203889/1000000000000000000 : ℝ) ≤ Real.exp ((-8525650296313/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525650296313/12800000000000 : ℝ)/8) ≤ (92011344783720389/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525650296313/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0846_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901534511/1000000000000 : ℝ) ≤ 4*Real.exp (33459/262144 : ℝ)*Real.exp (-mu (radius 8 (66919/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901534511/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66919/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0846_exp_radius
  have hrNumeric : (492085934829/500000000000 : ℝ) ≤ Real.exp (-66919/4194304 : ℝ) ∧ Real.exp (-66919/4194304 : ℝ) ≤ (984171869659/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492085934829/500000000000 : ℝ) ≤ (radius 8 (66919/524288 : ℝ)) ∧ (radius 8 (66919/524288 : ℝ)) ≤ (984171869659/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66919/524288 : ℝ)) (492085934829/500000000000 : ℝ) (984171869659/1000000000000 : ℝ) (177216621601/1000000000000 : ℝ) (22152077701/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66919/524288 : ℝ)) (492085934829/500000000000 : ℝ) (984171869659/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66919/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492085934829/500000000000 : ℝ) (984171869659/1000000000000 : ℝ) (992085934829/1000000000000 : ℝ) (99208593483/100000000000 : ℝ) (992054368297/1000000000000 : ℝ) (496027184149/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66919/524288 : ℝ)) 1 (992085934829/1000000000000 : ℝ) (99208593483/100000000000 : ℝ) (992054368297/1000000000000 : ℝ) (496027184149/500000000000 : ℝ) (992070151563/1000000000000 : ℝ) (248017537891/250000000000 : ℝ) (992070151437/1000000000000 : ℝ) (992070151439/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66919/524288 : ℝ)) 2 (992070151563/1000000000000 : ℝ) (248017537891/250000000000 : ℝ) (992070151437/1000000000000 : ℝ) (992070151439/1000000000000 : ℝ) (1984140303/2000000000 : ℝ) (496035075751/500000000000 : ℝ) (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66919/524288 : ℝ)) 3 (1984140303/2000000000 : ℝ) (496035075751/500000000000 : ℝ) (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ) (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ) (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66919/524288 : ℝ)) 4 (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ) (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ) (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ) (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66919/524288 : ℝ)) 5 (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ) (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ) (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ) (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66919/524288 : ℝ)) 6 (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ) (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ) (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ) (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66919/524288 : ℝ)) 7 (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ) (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ) (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ) (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66919/524288 : ℝ))) (177216621601/1000000000000 : ℝ) (22152077701/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66919/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177216621601/1000000000000 : ℝ) (22152077701/125000000000 : ℝ) (1471520777/2500000000 : ℝ) (147152077701/250000000000 : ℝ) (105242761509/250000000000 : ℝ) (84194209209/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66919/524288 : ℝ))) 1 (1471520777/2500000000 : ℝ) (147152077701/250000000000 : ℝ) (105242761509/250000000000 : ℝ) (84194209209/200000000000 : ℝ) (252394839209/500000000000 : ℝ) (20191587137/40000000000 : ℝ) (124445534347/250000000000 : ℝ) (124445534349/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66919/524288 : ℝ))) 2 (252394839209/500000000000 : ℝ) (20191587137/40000000000 : ℝ) (124445534347/250000000000 : ℝ) (124445534349/250000000000 : ℝ) (501285907903/1000000000000 : ℝ) (501285907911/1000000000000 : ℝ) (501273662837/1000000000000 : ℝ) (100254732569/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66919/524288 : ℝ))) 3 (501285907903/1000000000000 : ℝ) (501285907911/1000000000000 : ℝ) (501273662837/1000000000000 : ℝ) (100254732569/200000000000 : ℝ) (50127978537/100000000000 : ℝ) (250639892689/500000000000 : ℝ) (125319946333/250000000000 : ℝ) (501279785341/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66919/524288 : ℝ))) 4 (50127978537/100000000000 : ℝ) (250639892689/500000000000 : ℝ) (125319946333/250000000000 : ℝ) (501279785341/1000000000000 : ℝ) (501279785351/1000000000000 : ℝ) (6265997317/12500000000 : ℝ) (10025595707/20000000000 : ℝ) (6265997317/12500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66919/524288 : ℝ))) 5 (501279785351/1000000000000 : ℝ) (6265997317/12500000000 : ℝ) (10025595707/20000000000 : ℝ) (6265997317/12500000000 : ℝ) (10025595707/20000000000 : ℝ) (6265997317/12500000000 : ℝ) (10025595707/20000000000 : ℝ) (6265997317/12500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66919/524288 : ℝ))) 6 (10025595707/20000000000 : ℝ) (6265997317/12500000000 : ℝ) (10025595707/20000000000 : ℝ) (6265997317/12500000000 : ℝ) (10025595707/20000000000 : ℝ) (6265997317/12500000000 : ℝ) (10025595707/20000000000 : ℝ) (6265997317/12500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66919/524288 : ℝ))) 7 (10025595707/20000000000 : ℝ) (6265997317/12500000000 : ℝ) (10025595707/20000000000 : ℝ) (6265997317/12500000000 : ℝ) (10025595707/20000000000 : ℝ) (6265997317/12500000000 : ℝ) (10025595707/20000000000 : ℝ) (6265997317/12500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66919/524288 : ℝ)) hmem 8 (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ) (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66919/524288 : ℝ))) hcmem 8 (10025595707/20000000000 : ℝ) (6265997317/12500000000 : ℝ) (10025595707/20000000000 : ℝ) (6265997317/12500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66919/524288 : ℝ)) (992070151499/1000000000000 : ℝ) (496035075751/500000000000 : ℝ) (10025595707/20000000000 : ℝ) (6265997317/12500000000 : ℝ) (793702385191/1000000000000 : ℝ) (79370238521/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0846_exp_lower
  have heNumeric : (2054901534511/1000000000000 : ℝ)/4 ≤ Real.exp (-8525650296313/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901534511/1000000000000 : ℝ)/4 ≤ Real.exp ((33459/262144 : ℝ)-(79370238521/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33459/262144 : ℝ) (66919/524288 : ℝ) (79370238521/100000000000 : ℝ) (2054901534511/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0847; no trusted numerical premise.
theorem cover8_leaf0847_exp_radius : (199601523204607081/200000000000000000 : ℝ) ≤ Real.exp ((-8365/524288 : ℝ)/8) ∧ Real.exp ((-8365/524288 : ℝ)/8) ≤ (499003808011517703/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8365/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0847_exp_lower : (920113447806912927/1000000000000000000 : ℝ) ≤ Real.exp ((-85256502996841/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256502996841/128000000000000 : ℝ)/8) ≤ (28753545243966029/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256502996841/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0847_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901533969/1000000000000 : ℝ) ≤ 4*Real.exp (66919/524288 : ℝ)*Real.exp (-mu (radius 8 (8365/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901533969/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8365/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0847_exp_radius
  have hrNumeric : (984171635013/1000000000000 : ℝ) ≤ Real.exp (-8365/524288 : ℝ) ∧ Real.exp (-8365/524288 : ℝ) ≤ (492085817507/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984171635013/1000000000000 : ℝ) ≤ (radius 8 (8365/65536 : ℝ)) ∧ (radius 8 (8365/65536 : ℝ)) ≤ (492085817507/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8365/65536 : ℝ)) (984171635013/1000000000000 : ℝ) (492085817507/500000000000 : ℝ) (22152240587/125000000000 : ℝ) (177217924703/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8365/65536 : ℝ)) (984171635013/1000000000000 : ℝ) (492085817507/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8365/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984171635013/1000000000000 : ℝ) (492085817507/500000000000 : ℝ) (496042908753/500000000000 : ℝ) (992085817507/1000000000000 : ℝ) (198410850007/200000000000 : ℝ) (248013562509/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8365/65536 : ℝ)) 1 (496042908753/500000000000 : ℝ) (992085817507/1000000000000 : ℝ) (198410850007/200000000000 : ℝ) (248013562509/250000000000 : ℝ) (99207003377/100000000000 : ℝ) (248017508443/250000000000 : ℝ) (248017508411/250000000000 : ℝ) (496035016823/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8365/65536 : ℝ)) 2 (99207003377/100000000000 : ℝ) (248017508443/250000000000 : ℝ) (248017508411/250000000000 : ℝ) (496035016823/500000000000 : ℝ) (992070033707/1000000000000 : ℝ) (992070033709/1000000000000 : ℝ) (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8365/65536 : ℝ)) 3 (992070033707/1000000000000 : ℝ) (992070033709/1000000000000 : ℝ) (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ) (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ) (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8365/65536 : ℝ)) 4 (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ) (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ) (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ) (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8365/65536 : ℝ)) 5 (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ) (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ) (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ) (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8365/65536 : ℝ)) 6 (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ) (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ) (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ) (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8365/65536 : ℝ)) 7 (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ) (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ) (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ) (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8365/65536 : ℝ))) (22152240587/125000000000 : ℝ) (177217924703/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8365/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22152240587/125000000000 : ℝ) (177217924703/1000000000000 : ℝ) (147152240587/250000000000 : ℝ) (36788060147/62500000000 : ℝ) (210486296879/500000000000 : ℝ) (52621574221/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8365/65536 : ℝ))) 1 (147152240587/250000000000 : ℝ) (36788060147/62500000000 : ℝ) (210486296879/500000000000 : ℝ) (52621574221/125000000000 : ℝ) (504790778053/1000000000000 : ℝ) (25239538903/50000000000 : ℝ) (497783327953/1000000000000 : ℝ) (248891663981/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8365/65536 : ℝ))) 2 (504790778053/1000000000000 : ℝ) (25239538903/50000000000 : ℝ) (497783327953/1000000000000 : ℝ) (248891663981/500000000000 : ℝ) (501287053003/1000000000000 : ℝ) (501287053011/1000000000000 : ℝ) (501274808283/1000000000000 : ℝ) (125318702073/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8365/65536 : ℝ))) 3 (501287053003/1000000000000 : ℝ) (501287053011/1000000000000 : ℝ) (501274808283/1000000000000 : ℝ) (125318702073/250000000000 : ℝ) (501280930643/1000000000000 : ℝ) (125320232663/250000000000 : ℝ) (100256186121/200000000000 : ℝ) (100256186123/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8365/65536 : ℝ))) 4 (501280930643/1000000000000 : ℝ) (125320232663/250000000000 : ℝ) (100256186121/200000000000 : ℝ) (100256186123/200000000000 : ℝ) (7832514541/15625000000 : ℝ) (250640465317/500000000000 : ℝ) (501280930623/1000000000000 : ℝ) (250640465317/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8365/65536 : ℝ))) 5 (7832514541/15625000000 : ℝ) (250640465317/500000000000 : ℝ) (501280930623/1000000000000 : ℝ) (250640465317/500000000000 : ℝ) (501280930623/1000000000000 : ℝ) (250640465317/500000000000 : ℝ) (501280930623/1000000000000 : ℝ) (250640465317/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8365/65536 : ℝ))) 6 (501280930623/1000000000000 : ℝ) (250640465317/500000000000 : ℝ) (501280930623/1000000000000 : ℝ) (250640465317/500000000000 : ℝ) (501280930623/1000000000000 : ℝ) (250640465317/500000000000 : ℝ) (501280930623/1000000000000 : ℝ) (250640465317/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8365/65536 : ℝ))) 7 (501280930623/1000000000000 : ℝ) (250640465317/500000000000 : ℝ) (501280930623/1000000000000 : ℝ) (250640465317/500000000000 : ℝ) (501280930623/1000000000000 : ℝ) (250640465317/500000000000 : ℝ) (501280930623/1000000000000 : ℝ) (250640465317/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8365/65536 : ℝ)) hmem 8 (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ) (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8365/65536 : ℝ))) hcmem 8 (501280930623/1000000000000 : ℝ) (250640465317/500000000000 : ℝ) (501280930623/1000000000000 : ℝ) (250640465317/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8365/65536 : ℝ)) (496035016853/500000000000 : ℝ) (992070033709/1000000000000 : ℝ) (501280930623/1000000000000 : ℝ) (250640465317/500000000000 : ℝ) (793704292801/1000000000000 : ℝ) (396852146411/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0847_exp_lower
  have heNumeric : (2054901533969/1000000000000 : ℝ)/4 ≤ Real.exp (-85256502996841/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901533969/1000000000000 : ℝ)/4 ≤ Real.exp ((66919/524288 : ℝ)-(396852146411/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66919/524288 : ℝ) (8365/65536 : ℝ) (396852146411/500000000000 : ℝ) (2054901533969/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0848; no trusted numerical premise.
theorem cover8_leaf0848_exp_radius : (99800758628009113/100000000000000000 : ℝ) ≤ Real.exp ((-66921/4194304 : ℝ)/8) ∧ Real.exp ((-66921/4194304 : ℝ)/8) ≤ (998007586280091131/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66921/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0848_exp_lower : (460056723889691153/500000000000000000 : ℝ) ≤ Real.exp ((-2131412575687/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131412575687/3200000000000 : ℝ)/8) ≤ (920113447779382307/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131412575687/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0848_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901533477/1000000000000 : ℝ) ≤ 4*Real.exp (8365/65536 : ℝ)*Real.exp (-mu (radius 8 (66921/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901533477/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66921/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0848_exp_radius
  have hrNumeric : (61510712523/62500000000 : ℝ) ≤ Real.exp (-66921/4194304 : ℝ) ∧ Real.exp (-66921/4194304 : ℝ) ≤ (984171400369/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61510712523/62500000000 : ℝ) ≤ (radius 8 (66921/524288 : ℝ)) ∧ (radius 8 (66921/524288 : ℝ)) ≤ (984171400369/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66921/524288 : ℝ)) (61510712523/62500000000 : ℝ) (984171400369/1000000000000 : ℝ) (88609613891/500000000000 : ℝ) (44304806947/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66921/524288 : ℝ)) (61510712523/62500000000 : ℝ) (984171400369/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66921/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61510712523/62500000000 : ℝ) (984171400369/1000000000000 : ℝ) (124010712523/125000000000 : ℝ) (198417140037/200000000000 : ℝ) (992054131773/1000000000000 : ℝ) (496027065887/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66921/524288 : ℝ)) 1 (124010712523/125000000000 : ℝ) (198417140037/200000000000 : ℝ) (992054131773/1000000000000 : ℝ) (496027065887/500000000000 : ℝ) (496034957989/500000000000 : ℝ) (49603495799/50000000000 : ℝ) (248017478963/250000000000 : ℝ) (496034957927/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66921/524288 : ℝ)) 2 (496034957989/500000000000 : ℝ) (49603495799/50000000000 : ℝ) (248017478963/250000000000 : ℝ) (496034957927/500000000000 : ℝ) (198413983183/200000000000 : ℝ) (992069915917/1000000000000 : ℝ) (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66921/524288 : ℝ)) 3 (198413983183/200000000000 : ℝ) (992069915917/1000000000000 : ℝ) (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ) (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ) (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66921/524288 : ℝ)) 4 (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ) (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ) (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ) (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66921/524288 : ℝ)) 5 (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ) (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ) (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ) (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66921/524288 : ℝ)) 6 (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ) (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ) (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ) (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66921/524288 : ℝ)) 7 (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ) (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ) (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ) (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66921/524288 : ℝ))) (88609613891/500000000000 : ℝ) (44304806947/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66921/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88609613891/500000000000 : ℝ) (44304806947/250000000000 : ℝ) (588609613891/1000000000000 : ℝ) (294304806947/500000000000 : ℝ) (52621767683/125000000000 : ℝ) (13155441921/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66921/524288 : ℝ))) 1 (588609613891/1000000000000 : ℝ) (294304806947/500000000000 : ℝ) (52621767683/125000000000 : ℝ) (13155441921/31250000000 : ℝ) (504791877677/1000000000000 : ℝ) (504791877683/1000000000000 : ℝ) (248892259253/500000000000 : ℝ) (497784518513/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66921/524288 : ℝ))) 2 (504791877677/1000000000000 : ℝ) (504791877683/1000000000000 : ℝ) (248892259253/500000000000 : ℝ) (497784518513/1000000000000 : ℝ) (501288198091/1000000000000 : ℝ) (250644099049/500000000000 : ℝ) (501275953717/1000000000000 : ℝ) (125318988431/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66921/524288 : ℝ))) 3 (501288198091/1000000000000 : ℝ) (250644099049/500000000000 : ℝ) (501275953717/1000000000000 : ℝ) (125318988431/250000000000 : ℝ) (1958133109/3906250000 : ℝ) (501282075911/1000000000000 : ℝ) (250641037933/500000000000 : ℝ) (250641037937/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66921/524288 : ℝ))) 4 (1958133109/3906250000 : ℝ) (501282075911/1000000000000 : ℝ) (250641037933/500000000000 : ℝ) (250641037937/500000000000 : ℝ) (100256415177/200000000000 : ℝ) (501282075893/1000000000000 : ℝ) (125320518971/250000000000 : ℝ) (501282075893/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66921/524288 : ℝ))) 5 (100256415177/200000000000 : ℝ) (501282075893/1000000000000 : ℝ) (125320518971/250000000000 : ℝ) (501282075893/1000000000000 : ℝ) (125320518971/250000000000 : ℝ) (501282075893/1000000000000 : ℝ) (125320518971/250000000000 : ℝ) (501282075893/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66921/524288 : ℝ))) 6 (125320518971/250000000000 : ℝ) (501282075893/1000000000000 : ℝ) (125320518971/250000000000 : ℝ) (501282075893/1000000000000 : ℝ) (125320518971/250000000000 : ℝ) (501282075893/1000000000000 : ℝ) (125320518971/250000000000 : ℝ) (501282075893/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66921/524288 : ℝ))) 7 (125320518971/250000000000 : ℝ) (501282075893/1000000000000 : ℝ) (125320518971/250000000000 : ℝ) (501282075893/1000000000000 : ℝ) (125320518971/250000000000 : ℝ) (501282075893/1000000000000 : ℝ) (125320518971/250000000000 : ℝ) (501282075893/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66921/524288 : ℝ)) hmem 8 (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ) (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66921/524288 : ℝ))) hcmem 8 (125320518971/250000000000 : ℝ) (501282075893/1000000000000 : ℝ) (125320518971/250000000000 : ℝ) (501282075893/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66921/524288 : ℝ)) (496034957957/500000000000 : ℝ) (992069915917/1000000000000 : ℝ) (125320518971/250000000000 : ℝ) (501282075893/1000000000000 : ℝ) (793706200393/1000000000000 : ℝ) (79370620041/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0848_exp_lower
  have heNumeric : (2054901533477/1000000000000 : ℝ)/4 ≤ Real.exp (-2131412575687/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901533477/1000000000000 : ℝ)/4 ≤ Real.exp ((8365/65536 : ℝ)-(79370620041/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8365/65536 : ℝ) (66921/524288 : ℝ) (79370620041/100000000000 : ℝ) (2054901533477/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0849; no trusted numerical premise.
theorem cover8_leaf0849_exp_radius : (499003778268573871/500000000000000000 : ℝ) ≤ Real.exp ((-33461/2097152 : ℝ)/8) ∧ Real.exp ((-33461/2097152 : ℝ)/8) ≤ (998007556537147743/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33461/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0849_exp_lower : (920113447754381997/1000000000000000000 : ℝ) ≤ Real.exp ((-85256503055303/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256503055303/128000000000000 : ℝ)/8) ≤ (460056723877190999/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256503055303/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0849_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901533031/1000000000000 : ℝ) ≤ 4*Real.exp (66921/524288 : ℝ)*Real.exp (-mu (radius 8 (33461/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901533031/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33461/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0849_exp_radius
  have hrNumeric : (246042791431/250000000000 : ℝ) ≤ Real.exp (-33461/2097152 : ℝ) ∧ Real.exp (-33461/2097152 : ℝ) ≤ (39366846629/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246042791431/250000000000 : ℝ) ≤ (radius 8 (33461/262144 : ℝ)) ∧ (radius 8 (33461/262144 : ℝ)) ≤ (39366846629/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33461/262144 : ℝ)) (246042791431/250000000000 : ℝ) (39366846629/40000000000 : ℝ) (44305132713/250000000000 : ℝ) (88610265429/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33461/262144 : ℝ)) (246042791431/250000000000 : ℝ) (39366846629/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33461/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246042791431/250000000000 : ℝ) (39366846629/40000000000 : ℝ) (496042791431/500000000000 : ℝ) (992085582863/1000000000000 : ℝ) (992054013511/1000000000000 : ℝ) (124006751689/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33461/262144 : ℝ)) 1 (496042791431/500000000000 : ℝ) (992085582863/1000000000000 : ℝ) (992054013511/1000000000000 : ℝ) (124006751689/125000000000 : ℝ) (496034899093/500000000000 : ℝ) (248017449547/250000000000 : ℝ) (49603489903/50000000000 : ℝ) (496034899031/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33461/262144 : ℝ)) 2 (496034899093/500000000000 : ℝ) (248017449547/250000000000 : ℝ) (49603489903/50000000000 : ℝ) (496034899031/500000000000 : ℝ) (992069798123/1000000000000 : ℝ) (1587311677/1600000000 : ℝ) (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33461/262144 : ℝ)) 3 (992069798123/1000000000000 : ℝ) (1587311677/1600000000 : ℝ) (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ) (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ) (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33461/262144 : ℝ)) 4 (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ) (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ) (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ) (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33461/262144 : ℝ)) 5 (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ) (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ) (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ) (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33461/262144 : ℝ)) 6 (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ) (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ) (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ) (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33461/262144 : ℝ)) 7 (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ) (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ) (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ) (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33461/262144 : ℝ))) (44305132713/250000000000 : ℝ) (88610265429/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33461/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44305132713/250000000000 : ℝ) (88610265429/500000000000 : ℝ) (294305132713/500000000000 : ℝ) (588610265429/1000000000000 : ℝ) (210487844573/500000000000 : ℝ) (210487844577/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33461/262144 : ℝ))) 1 (294305132713/500000000000 : ℝ) (588610265429/1000000000000 : ℝ) (210487844573/500000000000 : ℝ) (210487844577/500000000000 : ℝ) (252396488643/500000000000 : ℝ) (126198244323/250000000000 : ℝ) (497785709041/1000000000000 : ℝ) (62223213631/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33461/262144 : ℝ))) 2 (252396488643/500000000000 : ℝ) (126198244323/250000000000 : ℝ) (497785709041/1000000000000 : ℝ) (62223213631/125000000000 : ℝ) (501289343163/1000000000000 : ℝ) (50128934317/100000000000 : ℝ) (100255419827/200000000000 : ℝ) (250638549571/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33461/262144 : ℝ))) 3 (501289343163/1000000000000 : ℝ) (50128934317/100000000000 : ℝ) (100255419827/200000000000 : ℝ) (250638549571/500000000000 : ℝ) (501283221149/1000000000000 : ℝ) (125320805289/250000000000 : ℝ) (501283221111/1000000000000 : ℝ) (501283221119/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33461/262144 : ℝ))) 4 (501283221149/1000000000000 : ℝ) (125320805289/250000000000 : ℝ) (501283221111/1000000000000 : ℝ) (501283221119/1000000000000 : ℝ) (50128322113/100000000000 : ℝ) (250641610569/500000000000 : ℝ) (501283221129/1000000000000 : ℝ) (250641610569/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33461/262144 : ℝ))) 5 (50128322113/100000000000 : ℝ) (250641610569/500000000000 : ℝ) (501283221129/1000000000000 : ℝ) (250641610569/500000000000 : ℝ) (501283221129/1000000000000 : ℝ) (250641610569/500000000000 : ℝ) (501283221129/1000000000000 : ℝ) (250641610569/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33461/262144 : ℝ))) 6 (501283221129/1000000000000 : ℝ) (250641610569/500000000000 : ℝ) (501283221129/1000000000000 : ℝ) (250641610569/500000000000 : ℝ) (501283221129/1000000000000 : ℝ) (250641610569/500000000000 : ℝ) (501283221129/1000000000000 : ℝ) (250641610569/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33461/262144 : ℝ))) 7 (501283221129/1000000000000 : ℝ) (250641610569/500000000000 : ℝ) (501283221129/1000000000000 : ℝ) (250641610569/500000000000 : ℝ) (501283221129/1000000000000 : ℝ) (250641610569/500000000000 : ℝ) (501283221129/1000000000000 : ℝ) (250641610569/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33461/262144 : ℝ)) hmem 8 (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ) (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33461/262144 : ℝ))) hcmem 8 (501283221129/1000000000000 : ℝ) (250641610569/500000000000 : ℝ) (501283221129/1000000000000 : ℝ) (250641610569/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33461/262144 : ℝ)) (496034899061/500000000000 : ℝ) (1587311677/1600000000 : ℝ) (501283221129/1000000000000 : ℝ) (250641610569/500000000000 : ℝ) (793708107959/1000000000000 : ℝ) (99213513497/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0849_exp_lower
  have heNumeric : (2054901533031/1000000000000 : ℝ)/4 ≤ Real.exp (-85256503055303/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901533031/1000000000000 : ℝ)/4 ≤ Real.exp ((66921/524288 : ℝ)-(99213513497/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66921/524288 : ℝ) (33461/262144 : ℝ) (99213513497/125000000000 : ℝ) (2054901533031/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0825_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0825_certificate
#check SmaleRate.Proofs.cover8_leaf0826_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0826_certificate
#check SmaleRate.Proofs.cover8_leaf0827_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0827_certificate
#check SmaleRate.Proofs.cover8_leaf0828_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0828_certificate
#check SmaleRate.Proofs.cover8_leaf0829_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0829_certificate
#check SmaleRate.Proofs.cover8_leaf0830_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0830_certificate
#check SmaleRate.Proofs.cover8_leaf0831_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0831_certificate
#check SmaleRate.Proofs.cover8_leaf0832_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0832_certificate
#check SmaleRate.Proofs.cover8_leaf0833_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0833_certificate
#check SmaleRate.Proofs.cover8_leaf0834_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0834_certificate
#check SmaleRate.Proofs.cover8_leaf0835_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0835_certificate
#check SmaleRate.Proofs.cover8_leaf0836_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0836_certificate
#check SmaleRate.Proofs.cover8_leaf0837_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0837_certificate
#check SmaleRate.Proofs.cover8_leaf0838_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0838_certificate
#check SmaleRate.Proofs.cover8_leaf0839_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0839_certificate
#check SmaleRate.Proofs.cover8_leaf0840_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0840_certificate
#check SmaleRate.Proofs.cover8_leaf0841_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0841_certificate
#check SmaleRate.Proofs.cover8_leaf0842_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0842_certificate
#check SmaleRate.Proofs.cover8_leaf0843_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0843_certificate
#check SmaleRate.Proofs.cover8_leaf0844_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0844_certificate
#check SmaleRate.Proofs.cover8_leaf0845_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0845_certificate
#check SmaleRate.Proofs.cover8_leaf0846_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0846_certificate
#check SmaleRate.Proofs.cover8_leaf0847_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0847_certificate
#check SmaleRate.Proofs.cover8_leaf0848_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0848_certificate
#check SmaleRate.Proofs.cover8_leaf0849_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0849_certificate
