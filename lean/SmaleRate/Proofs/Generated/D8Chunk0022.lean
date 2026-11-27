/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0550; no trusted numerical premise.
theorem cover8_leaf0550_exp_radius : (249504112429177853/250000000000000000 : ℝ) ≤ Real.exp ((-66623/4194304 : ℝ)/8) ∧ Real.exp ((-66623/4194304 : ℝ)/8) ≤ (998016449716711413/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66623/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0550_exp_lower : (184022710943234417/200000000000000000 : ℝ) ≤ Real.exp ((-42628192008433/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628192008433/64000000000000 : ℝ)/8) ≤ (460056777358086043/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628192008433/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0550_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980688813/200000000000 : ℝ) ≤ 4*Real.exp (33311/262144 : ℝ)*Real.exp (-mu (radius 8 (66623/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980688813/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66623/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0550_exp_radius
  have hrNumeric : (984241326987/1000000000000 : ℝ) ≤ Real.exp (-66623/4194304 : ℝ) ∧ Real.exp (-66623/4194304 : ℝ) ≤ (246060331747/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984241326987/1000000000000 : ℝ) ≤ (radius 8 (66623/524288 : ℝ)) ∧ (radius 8 (66623/524288 : ℝ)) ≤ (246060331747/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66623/524288 : ℝ)) (984241326987/1000000000000 : ℝ) (246060331747/250000000000 : ℝ) (7073218249/40000000000 : ℝ) (22103807029/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66623/524288 : ℝ)) (984241326987/1000000000000 : ℝ) (246060331747/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66623/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984241326987/1000000000000 : ℝ) (246060331747/250000000000 : ℝ) (992120663493/1000000000000 : ℝ) (496060331747/500000000000 : ℝ) (198417874899/200000000000 : ℝ) (992089374497/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66623/524288 : ℝ)) 1 (992120663493/1000000000000 : ℝ) (496060331747/500000000000 : ℝ) (198417874899/200000000000 : ℝ) (992089374497/1000000000000 : ℝ) (496052509497/500000000000 : ℝ) (248026254749/250000000000 : ℝ) (99210501887/100000000000 : ℝ) (992105018873/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66623/524288 : ℝ)) 2 (496052509497/500000000000 : ℝ) (248026254749/250000000000 : ℝ) (99210501887/100000000000 : ℝ) (992105018873/1000000000000 : ℝ) (248026254733/250000000000 : ℝ) (198421003787/200000000000 : ℝ) (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66623/524288 : ℝ)) 3 (248026254733/250000000000 : ℝ) (198421003787/200000000000 : ℝ) (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ) (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ) (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66623/524288 : ℝ)) 4 (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ) (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ) (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ) (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66623/524288 : ℝ)) 5 (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ) (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ) (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ) (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66623/524288 : ℝ)) 6 (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ) (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ) (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ) (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66623/524288 : ℝ)) 7 (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ) (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ) (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ) (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66623/524288 : ℝ))) (7073218249/40000000000 : ℝ) (22103807029/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66623/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7073218249/40000000000 : ℝ) (22103807029/125000000000 : ℝ) (36775951757/62500000000 : ℝ) (147103807029/250000000000 : ℝ) (84102427129/200000000000 : ℝ) (210256067827/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66623/524288 : ℝ))) 1 (36775951757/62500000000 : ℝ) (147103807029/250000000000 : ℝ) (84102427129/200000000000 : ℝ) (210256067827/500000000000 : ℝ) (252231840939/500000000000 : ℝ) (100892736377/200000000000 : ℝ) (497429134871/1000000000000 : ℝ) (497429134879/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66623/524288 : ℝ))) 2 (252231840939/500000000000 : ℝ) (100892736377/200000000000 : ℝ) (497429134871/1000000000000 : ℝ) (497429134879/1000000000000 : ℝ) (250473204187/500000000000 : ℝ) (250473204191/500000000000 : ℝ) (500934060381/1000000000000 : ℝ) (50093406039/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66623/524288 : ℝ))) 3 (250473204187/500000000000 : ℝ) (250473204191/500000000000 : ℝ) (500934060381/1000000000000 : ℝ) (50093406039/100000000000 : ℝ) (500940234377/1000000000000 : ℝ) (250470117193/500000000000 : ℝ) (500940234339/1000000000000 : ℝ) (125235058587/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66623/524288 : ℝ))) 4 (500940234377/1000000000000 : ℝ) (250470117193/500000000000 : ℝ) (500940234339/1000000000000 : ℝ) (125235058587/250000000000 : ℝ) (250470117179/500000000000 : ℝ) (500940234367/1000000000000 : ℝ) (500940234357/1000000000000 : ℝ) (500940234367/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66623/524288 : ℝ))) 5 (250470117179/500000000000 : ℝ) (500940234367/1000000000000 : ℝ) (500940234357/1000000000000 : ℝ) (500940234367/1000000000000 : ℝ) (500940234357/1000000000000 : ℝ) (500940234367/1000000000000 : ℝ) (500940234357/1000000000000 : ℝ) (500940234367/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66623/524288 : ℝ))) 6 (500940234357/1000000000000 : ℝ) (500940234367/1000000000000 : ℝ) (500940234357/1000000000000 : ℝ) (500940234367/1000000000000 : ℝ) (500940234357/1000000000000 : ℝ) (500940234367/1000000000000 : ℝ) (500940234357/1000000000000 : ℝ) (500940234367/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66623/524288 : ℝ))) 7 (500940234357/1000000000000 : ℝ) (500940234367/1000000000000 : ℝ) (500940234357/1000000000000 : ℝ) (500940234367/1000000000000 : ℝ) (500940234357/1000000000000 : ℝ) (500940234367/1000000000000 : ℝ) (500940234357/1000000000000 : ℝ) (500940234367/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66623/524288 : ℝ)) hmem 8 (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ) (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66623/524288 : ℝ))) hcmem 8 (500940234357/1000000000000 : ℝ) (500940234367/1000000000000 : ℝ) (500940234357/1000000000000 : ℝ) (500940234367/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66623/524288 : ℝ)) (992105018931/1000000000000 : ℝ) (198421003787/200000000000 : ℝ) (500940234357/1000000000000 : ℝ) (500940234367/1000000000000 : ℝ) (793136880727/1000000000000 : ℝ) (793136880747/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0550_exp_lower
  have heNumeric : (410980688813/200000000000 : ℝ)/4 ≤ Real.exp (-42628192008433/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980688813/200000000000 : ℝ)/4 ≤ Real.exp ((33311/262144 : ℝ)-(793136880747/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33311/262144 : ℝ) (66623/524288 : ℝ) (793136880747/1000000000000 : ℝ) (410980688813/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0551; no trusted numerical premise.
theorem cover8_leaf0551_exp_radius : (998016419973503873/1000000000000000000 : ℝ) ≤ Real.exp ((-1041/65536 : ℝ)/8) ∧ Real.exp ((-1041/65536 : ℝ)/8) ≤ (499008209986751937/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1041/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0551_exp_lower : (184022710805139929/200000000000000000 : ℝ) ≤ Real.exp ((-85256384785297/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256384785297/128000000000000 : ℝ)/8) ≤ (460056777012849823/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256384785297/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0551_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903431729/1000000000000 : ℝ) ≤ 4*Real.exp (66623/524288 : ℝ)*Real.exp (-mu (radius 8 (1041/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903431729/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1041/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0551_exp_radius
  have hrNumeric : (492120546163/500000000000 : ℝ) ≤ Real.exp (-1041/65536 : ℝ) ∧ Real.exp (-1041/65536 : ℝ) ≤ (984241092327/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492120546163/500000000000 : ℝ) ≤ (radius 8 (1041/8192 : ℝ)) ∧ (radius 8 (1041/8192 : ℝ)) ≤ (984241092327/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1041/8192 : ℝ)) (492120546163/500000000000 : ℝ) (984241092327/1000000000000 : ℝ) (176831762347/1000000000000 : ℝ) (88415881177/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1041/8192 : ℝ)) (492120546163/500000000000 : ℝ) (984241092327/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1041/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492120546163/500000000000 : ℝ) (984241092327/1000000000000 : ℝ) (992120546163/1000000000000 : ℝ) (248030136541/250000000000 : ℝ) (992089256229/1000000000000 : ℝ) (992089256231/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1041/8192 : ℝ)) 1 (992120546163/1000000000000 : ℝ) (248030136541/250000000000 : ℝ) (992089256229/1000000000000 : ℝ) (992089256231/1000000000000 : ℝ) (248026225299/250000000000 : ℝ) (496052450599/500000000000 : ℝ) (62006556317/62500000000 : ℝ) (39684196043/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1041/8192 : ℝ)) 2 (248026225299/250000000000 : ℝ) (496052450599/500000000000 : ℝ) (62006556317/62500000000 : ℝ) (39684196043/40000000000 : ℝ) (496052450567/500000000000 : ℝ) (992104901137/1000000000000 : ℝ) (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1041/8192 : ℝ)) 3 (496052450567/500000000000 : ℝ) (992104901137/1000000000000 : ℝ) (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ) (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ) (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1041/8192 : ℝ)) 4 (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ) (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ) (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ) (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1041/8192 : ℝ)) 5 (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ) (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ) (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ) (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1041/8192 : ℝ)) 6 (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ) (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ) (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ) (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1041/8192 : ℝ)) 7 (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ) (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ) (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ) (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1041/8192 : ℝ))) (176831762347/1000000000000 : ℝ) (88415881177/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1041/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176831762347/1000000000000 : ℝ) (88415881177/500000000000 : ℝ) (588415881173/1000000000000 : ℝ) (588415881177/1000000000000 : ℝ) (84102737731/200000000000 : ℝ) (84102737733/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1041/8192 : ℝ))) 1 (588415881173/1000000000000 : ℝ) (588415881177/1000000000000 : ℝ) (84102737731/200000000000 : ℝ) (84102737733/200000000000 : ℝ) (252232392457/500000000000 : ℝ) (504464784921/1000000000000 : ℝ) (62178791181/125000000000 : ℝ) (497430329457/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1041/8192 : ℝ))) 2 (252232392457/500000000000 : ℝ) (504464784921/1000000000000 : ℝ) (62178791181/125000000000 : ℝ) (497430329457/1000000000000 : ℝ) (500947557181/1000000000000 : ℝ) (500947557189/1000000000000 : ℝ) (500935209537/1000000000000 : ℝ) (250467604773/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1041/8192 : ℝ))) 3 (500947557181/1000000000000 : ℝ) (500947557189/1000000000000 : ℝ) (500935209537/1000000000000 : ℝ) (250467604773/500000000000 : ℝ) (500941383359/1000000000000 : ℝ) (62617672921/125000000000 : ℝ) (12523534583/25000000000 : ℝ) (50094138333/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1041/8192 : ℝ))) 4 (500941383359/1000000000000 : ℝ) (62617672921/125000000000 : ℝ) (12523534583/25000000000 : ℝ) (50094138333/100000000000 : ℝ) (500941383339/1000000000000 : ℝ) (500941383349/1000000000000 : ℝ) (500941383339/1000000000000 : ℝ) (500941383349/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1041/8192 : ℝ))) 5 (500941383339/1000000000000 : ℝ) (500941383349/1000000000000 : ℝ) (500941383339/1000000000000 : ℝ) (500941383349/1000000000000 : ℝ) (500941383339/1000000000000 : ℝ) (500941383349/1000000000000 : ℝ) (500941383339/1000000000000 : ℝ) (500941383349/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1041/8192 : ℝ))) 6 (500941383339/1000000000000 : ℝ) (500941383349/1000000000000 : ℝ) (500941383339/1000000000000 : ℝ) (500941383349/1000000000000 : ℝ) (500941383339/1000000000000 : ℝ) (500941383349/1000000000000 : ℝ) (500941383339/1000000000000 : ℝ) (500941383349/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1041/8192 : ℝ))) 7 (500941383339/1000000000000 : ℝ) (500941383349/1000000000000 : ℝ) (500941383339/1000000000000 : ℝ) (500941383349/1000000000000 : ℝ) (500941383339/1000000000000 : ℝ) (500941383349/1000000000000 : ℝ) (500941383339/1000000000000 : ℝ) (500941383349/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1041/8192 : ℝ)) hmem 8 (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ) (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1041/8192 : ℝ))) hcmem 8 (500941383339/1000000000000 : ℝ) (500941383349/1000000000000 : ℝ) (500941383339/1000000000000 : ℝ) (500941383349/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1041/8192 : ℝ)) (992104901133/1000000000000 : ℝ) (992104901137/1000000000000 : ℝ) (500941383339/1000000000000 : ℝ) (500941383349/1000000000000 : ℝ) (793138794079/1000000000000 : ℝ) (793138794099/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0551_exp_lower
  have heNumeric : (2054903431729/1000000000000 : ℝ)/4 ≤ Real.exp (-85256384785297/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903431729/1000000000000 : ℝ)/4 ≤ Real.exp ((66623/524288 : ℝ)-(793138794099/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66623/524288 : ℝ) (1041/8192 : ℝ) (793138794099/1000000000000 : ℝ) (2054903431729/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0552; no trusted numerical premise.
theorem cover8_leaf0552_exp_radius : (49900819511514861/50000000000000000 : ℝ) ≤ Real.exp ((-66625/4194304 : ℝ)/8) ∧ Real.exp ((-66625/4194304 : ℝ)/8) ≤ (998016390230297221/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66625/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0552_exp_lower : (7360908426692859/8000000000000000 : ℝ) ≤ Real.exp ((-1332131024253/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332131024253/2000000000000 : ℝ)/8) ≤ (57507097083537961/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332131024253/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0552_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903419417/1000000000000 : ℝ) ≤ 4*Real.exp (1041/8192 : ℝ)*Real.exp (-mu (radius 8 (66625/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903419417/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66625/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0552_exp_radius
  have hrNumeric : (15378763401/15625000000 : ℝ) ≤ Real.exp (-66625/4194304 : ℝ) ∧ Real.exp (-66625/4194304 : ℝ) ≤ (196848171533/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (15378763401/15625000000 : ℝ) ≤ (radius 8 (66625/524288 : ℝ)) ∧ (radius 8 (66625/524288 : ℝ)) ≤ (196848171533/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66625/524288 : ℝ)) (15378763401/15625000000 : ℝ) (196848171533/200000000000 : ℝ) (35366613693/200000000000 : ℝ) (176833068471/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66625/524288 : ℝ)) (15378763401/15625000000 : ℝ) (196848171533/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66625/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (15378763401/15625000000 : ℝ) (196848171533/200000000000 : ℝ) (31003763401/31250000000 : ℝ) (992120428833/1000000000000 : ℝ) (496044568981/500000000000 : ℝ) (248022284491/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66625/524288 : ℝ)) 1 (31003763401/31250000000 : ℝ) (992120428833/1000000000000 : ℝ) (496044568981/500000000000 : ℝ) (248022284491/250000000000 : ℝ) (992104783397/1000000000000 : ℝ) (992104783399/1000000000000 : ℝ) (992104783273/1000000000000 : ℝ) (248026195819/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66625/524288 : ℝ)) 2 (992104783397/1000000000000 : ℝ) (992104783399/1000000000000 : ℝ) (992104783273/1000000000000 : ℝ) (248026195819/250000000000 : ℝ) (198420956667/200000000000 : ℝ) (496052391669/500000000000 : ℝ) (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66625/524288 : ℝ)) 3 (198420956667/200000000000 : ℝ) (496052391669/500000000000 : ℝ) (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ) (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ) (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66625/524288 : ℝ)) 4 (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ) (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ) (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ) (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66625/524288 : ℝ)) 5 (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ) (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ) (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ) (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66625/524288 : ℝ)) 6 (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ) (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ) (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ) (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66625/524288 : ℝ)) 7 (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ) (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ) (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ) (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66625/524288 : ℝ))) (35366613693/200000000000 : ℝ) (176833068471/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66625/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35366613693/200000000000 : ℝ) (176833068471/1000000000000 : ℝ) (73552066779/125000000000 : ℝ) (147104133559/250000000000 : ℝ) (84103048331/200000000000 : ℝ) (6570550651/15625000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66625/524288 : ℝ))) 1 (73552066779/125000000000 : ℝ) (147104133559/250000000000 : ℝ) (84103048331/200000000000 : ℝ) (6570550651/15625000000 : ℝ) (504465887943/1000000000000 : ℝ) (10089317759/20000000000 : ℝ) (497431524017/1000000000000 : ℝ) (19897260961/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66625/524288 : ℝ))) 2 (504465887943/1000000000000 : ℝ) (10089317759/20000000000 : ℝ) (497431524017/1000000000000 : ℝ) (19897260961/40000000000 : ℝ) (25047435299/50000000000 : ℝ) (125237176497/250000000000 : ℝ) (250468179343/500000000000 : ℝ) (250468179347/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66625/524288 : ℝ))) 3 (25047435299/50000000000 : ℝ) (125237176497/250000000000 : ℝ) (250468179343/500000000000 : ℝ) (250468179347/500000000000 : ℝ) (500942532333/1000000000000 : ℝ) (500942532341/1000000000000 : ℝ) (250471266147/500000000000 : ℝ) (500942532303/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66625/524288 : ℝ))) 4 (500942532333/1000000000000 : ℝ) (500942532341/1000000000000 : ℝ) (250471266147/500000000000 : ℝ) (500942532303/1000000000000 : ℝ) (500942532313/1000000000000 : ℝ) (250471266161/500000000000 : ℝ) (500942532313/1000000000000 : ℝ) (250471266161/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66625/524288 : ℝ))) 5 (500942532313/1000000000000 : ℝ) (250471266161/500000000000 : ℝ) (500942532313/1000000000000 : ℝ) (250471266161/500000000000 : ℝ) (500942532313/1000000000000 : ℝ) (250471266161/500000000000 : ℝ) (500942532313/1000000000000 : ℝ) (250471266161/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66625/524288 : ℝ))) 6 (500942532313/1000000000000 : ℝ) (250471266161/500000000000 : ℝ) (500942532313/1000000000000 : ℝ) (250471266161/500000000000 : ℝ) (500942532313/1000000000000 : ℝ) (250471266161/500000000000 : ℝ) (500942532313/1000000000000 : ℝ) (250471266161/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66625/524288 : ℝ))) 7 (500942532313/1000000000000 : ℝ) (250471266161/500000000000 : ℝ) (500942532313/1000000000000 : ℝ) (250471266161/500000000000 : ℝ) (500942532313/1000000000000 : ℝ) (250471266161/500000000000 : ℝ) (500942532313/1000000000000 : ℝ) (250471266161/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66625/524288 : ℝ)) hmem 8 (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ) (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66625/524288 : ℝ))) hcmem 8 (500942532313/1000000000000 : ℝ) (250471266161/500000000000 : ℝ) (500942532313/1000000000000 : ℝ) (250471266161/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66625/524288 : ℝ)) (496052391667/500000000000 : ℝ) (496052391669/500000000000 : ℝ) (500942532313/1000000000000 : ℝ) (250471266161/500000000000 : ℝ) (793140707421/1000000000000 : ℝ) (793140707439/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0552_exp_lower
  have heNumeric : (2054903419417/1000000000000 : ℝ)/4 ≤ Real.exp (-1332131024253/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903419417/1000000000000 : ℝ)/4 ≤ Real.exp ((1041/8192 : ℝ)-(793140707439/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1041/8192 : ℝ) (66625/524288 : ℝ) (793140707439/1000000000000 : ℝ) (2054903419417/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0553; no trusted numerical premise.
theorem cover8_leaf0553_exp_radius : (998016360487091453/1000000000000000000 : ℝ) ≤ Real.exp ((-33313/2097152 : ℝ)/8) ∧ Real.exp ((-33313/2097152 : ℝ)/8) ≤ (499008180243545727/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33313/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0553_exp_lower : (920113552650275447/1000000000000000000 : ℝ) ≤ Real.exp ((-17051277263203/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051277263203/25600000000000 : ℝ)/8) ≤ (115014194081284431/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051277263203/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0553_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980681431/200000000000 : ℝ) ≤ 4*Real.exp (66625/524288 : ℝ)*Real.exp (-mu (radius 8 (33313/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980681431/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33313/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0553_exp_radius
  have hrNumeric : (984240623003/1000000000000 : ℝ) ≤ Real.exp (-33313/2097152 : ℝ) ∧ Real.exp (-33313/2097152 : ℝ) ≤ (246060155751/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984240623003/1000000000000 : ℝ) ≤ (radius 8 (33313/262144 : ℝ)) ∧ (radius 8 (33313/262144 : ℝ)) ≤ (246060155751/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33313/262144 : ℝ)) (984240623003/1000000000000 : ℝ) (246060155751/250000000000 : ℝ) (176834374567/1000000000000 : ℝ) (88417187287/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33313/262144 : ℝ)) (984240623003/1000000000000 : ℝ) (246060155751/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33313/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984240623003/1000000000000 : ℝ) (246060155751/250000000000 : ℝ) (992120311501/1000000000000 : ℝ) (496060155751/500000000000 : ℝ) (62005563731/62500000000 : ℝ) (496044509849/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33313/262144 : ℝ)) 1 (992120311501/1000000000000 : ℝ) (496060155751/500000000000 : ℝ) (62005563731/62500000000 : ℝ) (496044509849/500000000000 : ℝ) (496052332799/500000000000 : ℝ) (77508177/78125000 : ℝ) (39684186619/40000000000 : ℝ) (992104665477/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33313/262144 : ℝ)) 2 (496052332799/500000000000 : ℝ) (77508177/78125000 : ℝ) (39684186619/40000000000 : ℝ) (992104665477/1000000000000 : ℝ) (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ) (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33313/262144 : ℝ)) 3 (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ) (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ) (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ) (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33313/262144 : ℝ)) 4 (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ) (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ) (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ) (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33313/262144 : ℝ)) 5 (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ) (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ) (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ) (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33313/262144 : ℝ)) 6 (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ) (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ) (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ) (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33313/262144 : ℝ)) 7 (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ) (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ) (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ) (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33313/262144 : ℝ))) (176834374567/1000000000000 : ℝ) (88417187287/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33313/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176834374567/1000000000000 : ℝ) (88417187287/500000000000 : ℝ) (588417187283/1000000000000 : ℝ) (588417187287/1000000000000 : ℝ) (420516794631/1000000000000 : ℝ) (5256459933/12500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33313/262144 : ℝ))) 1 (588417187283/1000000000000 : ℝ) (588417187287/1000000000000 : ℝ) (420516794631/1000000000000 : ℝ) (5256459933/12500000000 : ℝ) (504466990957/1000000000000 : ℝ) (126116747741/250000000000 : ℝ) (62179089821/125000000000 : ℝ) (31089544911/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33313/262144 : ℝ))) 2 (504466990957/1000000000000 : ℝ) (126116747741/250000000000 : ℝ) (62179089821/125000000000 : ℝ) (31089544911/62500000000 : ℝ) (250474927381/500000000000 : ℝ) (50094985477/100000000000 : ℝ) (250468753909/500000000000 : ℝ) (500937507827/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33313/262144 : ℝ))) 3 (250474927381/500000000000 : ℝ) (50094985477/100000000000 : ℝ) (250468753909/500000000000 : ℝ) (500937507827/1000000000000 : ℝ) (50094368129/100000000000 : ℝ) (500943681299/1000000000000 : ℝ) (500943681251/1000000000000 : ℝ) (500943681261/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33313/262144 : ℝ))) 4 (50094368129/100000000000 : ℝ) (500943681299/1000000000000 : ℝ) (500943681251/1000000000000 : ℝ) (500943681261/1000000000000 : ℝ) (50094368127/100000000000 : ℝ) (391362251/781250000 : ℝ) (50094368127/100000000000 : ℝ) (391362251/781250000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33313/262144 : ℝ))) 5 (50094368127/100000000000 : ℝ) (391362251/781250000 : ℝ) (50094368127/100000000000 : ℝ) (391362251/781250000 : ℝ) (50094368127/100000000000 : ℝ) (391362251/781250000 : ℝ) (50094368127/100000000000 : ℝ) (391362251/781250000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33313/262144 : ℝ))) 6 (50094368127/100000000000 : ℝ) (391362251/781250000 : ℝ) (50094368127/100000000000 : ℝ) (391362251/781250000 : ℝ) (50094368127/100000000000 : ℝ) (391362251/781250000 : ℝ) (50094368127/100000000000 : ℝ) (391362251/781250000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33313/262144 : ℝ))) 7 (50094368127/100000000000 : ℝ) (391362251/781250000 : ℝ) (50094368127/100000000000 : ℝ) (391362251/781250000 : ℝ) (50094368127/100000000000 : ℝ) (391362251/781250000 : ℝ) (50094368127/100000000000 : ℝ) (391362251/781250000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33313/262144 : ℝ)) hmem 8 (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ) (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33313/262144 : ℝ))) hcmem 8 (50094368127/100000000000 : ℝ) (391362251/781250000 : ℝ) (50094368127/100000000000 : ℝ) (391362251/781250000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33313/262144 : ℝ)) (15501635399/15625000000 : ℝ) (992104665539/1000000000000 : ℝ) (50094368127/100000000000 : ℝ) (391362251/781250000 : ℝ) (12392853449/15625000000 : ℝ) (158628524151/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0553_exp_lower
  have heNumeric : (410980681431/200000000000 : ℝ)/4 ≤ Real.exp (-17051277263203/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980681431/200000000000 : ℝ)/4 ≤ Real.exp ((66625/524288 : ℝ)-(158628524151/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66625/524288 : ℝ) (33313/262144 : ℝ) (158628524151/200000000000 : ℝ) (410980681431/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0554; no trusted numerical premise.
theorem cover8_leaf0554_exp_radius : (998016330743886573/1000000000000000000 : ℝ) ≤ Real.exp ((-66627/4194304 : ℝ)/8) ∧ Real.exp ((-66627/4194304 : ℝ)/8) ≤ (499008165371943287/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66627/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0554_exp_lower : (115014193995809229/125000000000000000 : ℝ) ≤ Real.exp ((-42628193538511/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628193538511/64000000000000 : ℝ)/8) ≤ (920113551966473833/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628193538511/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0554_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903394937/1000000000000 : ℝ) ≤ 4*Real.exp (33313/262144 : ℝ)*Real.exp (-mu (radius 8 (66627/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903394937/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66627/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0554_exp_radius
  have hrNumeric : (492120194171/500000000000 : ℝ) ≤ Real.exp (-66627/4194304 : ℝ) ∧ Real.exp (-66627/4194304 : ℝ) ≤ (984240388343/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492120194171/500000000000 : ℝ) ≤ (radius 8 (66627/524288 : ℝ)) ∧ (radius 8 (66627/524288 : ℝ)) ≤ (984240388343/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66627/524288 : ℝ)) (492120194171/500000000000 : ℝ) (984240388343/1000000000000 : ℝ) (176835680659/1000000000000 : ℝ) (88417840333/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66627/524288 : ℝ)) (492120194171/500000000000 : ℝ) (984240388343/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66627/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492120194171/500000000000 : ℝ) (984240388343/1000000000000 : ℝ) (992120194171/1000000000000 : ℝ) (248030048543/250000000000 : ℝ) (99208890143/100000000000 : ℝ) (124011112679/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66627/524288 : ℝ)) 1 (992120194171/1000000000000 : ℝ) (248030048543/250000000000 : ℝ) (99208890143/100000000000 : ℝ) (124011112679/125000000000 : ℝ) (4960522739/5000000000 : ℝ) (496052273901/500000000000 : ℝ) (992104547677/1000000000000 : ℝ) (992104547679/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66627/524288 : ℝ)) 2 (4960522739/5000000000 : ℝ) (496052273901/500000000000 : ℝ) (992104547677/1000000000000 : ℝ) (992104547679/1000000000000 : ℝ) (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ) (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66627/524288 : ℝ)) 3 (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ) (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ) (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ) (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66627/524288 : ℝ)) 4 (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ) (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ) (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ) (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66627/524288 : ℝ)) 5 (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ) (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ) (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ) (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66627/524288 : ℝ)) 6 (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ) (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ) (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ) (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66627/524288 : ℝ)) 7 (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ) (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ) (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ) (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66627/524288 : ℝ))) (176835680659/1000000000000 : ℝ) (88417840333/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66627/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176835680659/1000000000000 : ℝ) (88417840333/500000000000 : ℝ) (588417840329/1000000000000 : ℝ) (588417840333/1000000000000 : ℝ) (420518347589/1000000000000 : ℝ) (210259173799/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66627/524288 : ℝ))) 1 (588417840329/1000000000000 : ℝ) (588417840333/1000000000000 : ℝ) (420518347589/1000000000000 : ℝ) (210259173799/500000000000 : ℝ) (504468093959/1000000000000 : ℝ) (252234046983/500000000000 : ℝ) (99486782621/200000000000 : ℝ) (497433913113/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66627/524288 : ℝ))) 2 (504468093959/1000000000000 : ℝ) (252234046983/500000000000 : ℝ) (99486782621/200000000000 : ℝ) (497433913113/1000000000000 : ℝ) (125237750883/250000000000 : ℝ) (25047550177/50000000000 : ℝ) (500938656937/1000000000000 : ℝ) (250469328473/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66627/524288 : ℝ))) 3 (125237750883/250000000000 : ℝ) (25047550177/50000000000 : ℝ) (500938656937/1000000000000 : ℝ) (250469328473/500000000000 : ℝ) (250472415117/500000000000 : ℝ) (500944830243/1000000000000 : ℝ) (125236207549/250000000000 : ℝ) (100188966041/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66627/524288 : ℝ))) 4 (250472415117/500000000000 : ℝ) (500944830243/1000000000000 : ℝ) (125236207549/250000000000 : ℝ) (100188966041/200000000000 : ℝ) (100188966043/200000000000 : ℝ) (31309051889/62500000000 : ℝ) (250472415107/500000000000 : ℝ) (31309051889/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66627/524288 : ℝ))) 5 (100188966043/200000000000 : ℝ) (31309051889/62500000000 : ℝ) (250472415107/500000000000 : ℝ) (31309051889/62500000000 : ℝ) (250472415107/500000000000 : ℝ) (31309051889/62500000000 : ℝ) (250472415107/500000000000 : ℝ) (31309051889/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66627/524288 : ℝ))) 6 (250472415107/500000000000 : ℝ) (31309051889/62500000000 : ℝ) (250472415107/500000000000 : ℝ) (31309051889/62500000000 : ℝ) (250472415107/500000000000 : ℝ) (31309051889/62500000000 : ℝ) (250472415107/500000000000 : ℝ) (31309051889/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66627/524288 : ℝ))) 7 (250472415107/500000000000 : ℝ) (31309051889/62500000000 : ℝ) (250472415107/500000000000 : ℝ) (31309051889/62500000000 : ℝ) (250472415107/500000000000 : ℝ) (31309051889/62500000000 : ℝ) (250472415107/500000000000 : ℝ) (31309051889/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66627/524288 : ℝ)) hmem 8 (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ) (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66627/524288 : ℝ))) hcmem 8 (250472415107/500000000000 : ℝ) (31309051889/62500000000 : ℝ) (250472415107/500000000000 : ℝ) (31309051889/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66627/524288 : ℝ)) (496052273869/500000000000 : ℝ) (992104547741/1000000000000 : ℝ) (250472415107/500000000000 : ℝ) (31309051889/62500000000 : ℝ) (793144534029/1000000000000 : ℝ) (793144534049/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0554_exp_lower
  have heNumeric : (2054903394937/1000000000000 : ℝ)/4 ≤ Real.exp (-42628193538511/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903394937/1000000000000 : ℝ)/4 ≤ Real.exp ((33313/262144 : ℝ)-(793144534049/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33313/262144 : ℝ) (66627/524288 : ℝ) (793144534049/1000000000000 : ℝ) (2054903394937/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0555; no trusted numerical premise.
theorem cover8_leaf0555_exp_radius : (998016301000682579/1000000000000000000 : ℝ) ≤ Real.exp ((-16657/1048576 : ℝ)/8) ∧ Real.exp ((-16657/1048576 : ℝ)/8) ≤ (49900815050034129/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16657/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0555_exp_lower : (920113551284972501/1000000000000000000 : ℝ) ≤ Real.exp ((-85256387835469/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256387835469/128000000000000 : ℝ)/8) ≤ (460056775642486251/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256387835469/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0555_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903382761/1000000000000 : ℝ) ≤ 4*Real.exp (66627/524288 : ℝ)*Real.exp (-mu (radius 8 (16657/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903382761/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16657/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0555_exp_radius
  have hrNumeric : (984240153681/1000000000000 : ℝ) ≤ Real.exp (-16657/1048576 : ℝ) ∧ Real.exp (-16657/1048576 : ℝ) ≤ (492120076841/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984240153681/1000000000000 : ℝ) ≤ (radius 8 (16657/131072 : ℝ)) ∧ (radius 8 (16657/131072 : ℝ)) ≤ (492120076841/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16657/131072 : ℝ)) (984240153681/1000000000000 : ℝ) (492120076841/500000000000 : ℝ) (88418493371/500000000000 : ℝ) (44209246687/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16657/131072 : ℝ)) (984240153681/1000000000000 : ℝ) (492120076841/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16657/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984240153681/1000000000000 : ℝ) (492120076841/500000000000 : ℝ) (24803001921/25000000000 : ℝ) (992120076841/1000000000000 : ℝ) (248022195791/250000000000 : ℝ) (496044391583/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16657/131072 : ℝ)) 1 (24803001921/25000000000 : ℝ) (992120076841/1000000000000 : ℝ) (248022195791/250000000000 : ℝ) (496044391583/500000000000 : ℝ) (496052215001/500000000000 : ℝ) (248026107501/250000000000 : ℝ) (496052214939/500000000000 : ℝ) (992104429881/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16657/131072 : ℝ)) 2 (496052215001/500000000000 : ℝ) (248026107501/250000000000 : ℝ) (496052214939/500000000000 : ℝ) (992104429881/1000000000000 : ℝ) (49605221497/50000000000 : ℝ) (992104429943/1000000000000 : ℝ) (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16657/131072 : ℝ)) 3 (49605221497/50000000000 : ℝ) (992104429943/1000000000000 : ℝ) (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ) (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ) (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16657/131072 : ℝ)) 4 (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ) (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ) (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ) (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16657/131072 : ℝ)) 5 (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ) (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ) (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ) (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16657/131072 : ℝ)) 6 (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ) (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ) (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ) (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16657/131072 : ℝ)) 7 (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ) (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ) (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ) (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16657/131072 : ℝ))) (88418493371/500000000000 : ℝ) (44209246687/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16657/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88418493371/500000000000 : ℝ) (44209246687/250000000000 : ℝ) (588418493371/1000000000000 : ℝ) (294209246687/500000000000 : ℝ) (42051990053/100000000000 : ℝ) (210259950269/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16657/131072 : ℝ))) 1 (588418493371/1000000000000 : ℝ) (294209246687/500000000000 : ℝ) (42051990053/100000000000 : ℝ) (210259950269/500000000000 : ℝ) (10089383939/20000000000 : ℝ) (126117299239/250000000000 : ℝ) (497435107629/1000000000000 : ℝ) (124358776909/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16657/131072 : ℝ))) 2 (10089383939/20000000000 : ℝ) (126117299239/250000000000 : ℝ) (497435107629/1000000000000 : ℝ) (124358776909/250000000000 : ℝ) (500952152289/1000000000000 : ℝ) (62619019037/125000000000 : ℝ) (125234951511/250000000000 : ℝ) (125234951513/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16657/131072 : ℝ))) 3 (500952152289/1000000000000 : ℝ) (62619019037/125000000000 : ℝ) (125234951511/250000000000 : ℝ) (125234951513/250000000000 : ℝ) (250472989583/500000000000 : ℝ) (250472989587/500000000000 : ℝ) (62618247391/125000000000 : ℝ) (1956820231/3906250000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16657/131072 : ℝ))) 4 (250472989583/500000000000 : ℝ) (250472989587/500000000000 : ℝ) (62618247391/125000000000 : ℝ) (1956820231/3906250000 : ℝ) (500945979147/1000000000000 : ℝ) (100189195831/200000000000 : ℝ) (250472989573/500000000000 : ℝ) (100189195831/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16657/131072 : ℝ))) 5 (500945979147/1000000000000 : ℝ) (100189195831/200000000000 : ℝ) (250472989573/500000000000 : ℝ) (100189195831/200000000000 : ℝ) (250472989573/500000000000 : ℝ) (100189195831/200000000000 : ℝ) (250472989573/500000000000 : ℝ) (100189195831/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16657/131072 : ℝ))) 6 (250472989573/500000000000 : ℝ) (100189195831/200000000000 : ℝ) (250472989573/500000000000 : ℝ) (100189195831/200000000000 : ℝ) (250472989573/500000000000 : ℝ) (100189195831/200000000000 : ℝ) (250472989573/500000000000 : ℝ) (100189195831/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16657/131072 : ℝ))) 7 (250472989573/500000000000 : ℝ) (100189195831/200000000000 : ℝ) (250472989573/500000000000 : ℝ) (100189195831/200000000000 : ℝ) (250472989573/500000000000 : ℝ) (100189195831/200000000000 : ℝ) (250472989573/500000000000 : ℝ) (100189195831/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16657/131072 : ℝ)) hmem 8 (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ) (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16657/131072 : ℝ))) hcmem 8 (250472989573/500000000000 : ℝ) (100189195831/200000000000 : ℝ) (250472989573/500000000000 : ℝ) (100189195831/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16657/131072 : ℝ)) (992104429939/1000000000000 : ℝ) (992104429943/1000000000000 : ℝ) (250472989573/500000000000 : ℝ) (100189195831/200000000000 : ℝ) (158629289461/200000000000 : ℝ) (793146447323/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0555_exp_lower
  have heNumeric : (2054903382761/1000000000000 : ℝ)/4 ≤ Real.exp (-85256387835469/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903382761/1000000000000 : ℝ)/4 ≤ Real.exp ((66627/524288 : ℝ)-(793146447323/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66627/524288 : ℝ) (16657/131072 : ℝ) (793146447323/1000000000000 : ℝ) (2054903382761/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0556; no trusted numerical premise.
theorem cover8_leaf0556_exp_radius : (62376016953592467/62500000000000000 : ℝ) ≤ Real.exp ((-66629/4194304 : ℝ)/8) ∧ Real.exp ((-66629/4194304 : ℝ)/8) ≤ (998016271257479473/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66629/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0556_exp_lower : (92011355060427627/100000000000000000 : ℝ) ≤ Real.exp ((-4262819429651/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262819429651/6400000000000 : ℝ)/8) ≤ (920113550604276271/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262819429651/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0556_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (10274516853/5000000000 : ℝ) ≤ 4*Real.exp (16657/131072 : ℝ)*Real.exp (-mu (radius 8 (66629/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (10274516853/5000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66629/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0556_exp_radius
  have hrNumeric : (984239919019/1000000000000 : ℝ) ≤ Real.exp (-66629/4194304 : ℝ) ∧ Real.exp (-66629/4194304 : ℝ) ≤ (49211995951/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984239919019/1000000000000 : ℝ) ≤ (radius 8 (66629/524288 : ℝ)) ∧ (radius 8 (66629/524288 : ℝ)) ≤ (49211995951/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66629/524288 : ℝ)) (984239919019/1000000000000 : ℝ) (49211995951/50000000000 : ℝ) (8841914641/50000000000 : ℝ) (88419146413/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66629/524288 : ℝ)) (984239919019/1000000000000 : ℝ) (49211995951/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66629/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984239919019/1000000000000 : ℝ) (49211995951/50000000000 : ℝ) (992119959509/1000000000000 : ℝ) (99211995951/100000000000 : ℝ) (992088664897/1000000000000 : ℝ) (992088664899/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66629/524288 : ℝ)) 1 (992119959509/1000000000000 : ℝ) (99211995951/100000000000 : ℝ) (992088664897/1000000000000 : ℝ) (992088664899/1000000000000 : ℝ) (992104312203/1000000000000 : ℝ) (198420862441/200000000000 : ℝ) (992104312079/1000000000000 : ℝ) (496052156041/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66629/524288 : ℝ)) 2 (992104312203/1000000000000 : ℝ) (198420862441/200000000000 : ℝ) (992104312079/1000000000000 : ℝ) (496052156041/500000000000 : ℝ) (992104312141/1000000000000 : ℝ) (62006519509/62500000000 : ℝ) (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66629/524288 : ℝ)) 3 (992104312141/1000000000000 : ℝ) (62006519509/62500000000 : ℝ) (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ) (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ) (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66629/524288 : ℝ)) 4 (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ) (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ) (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ) (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66629/524288 : ℝ)) 5 (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ) (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ) (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ) (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66629/524288 : ℝ)) 6 (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ) (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ) (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ) (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66629/524288 : ℝ)) 7 (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ) (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ) (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ) (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66629/524288 : ℝ))) (8841914641/50000000000 : ℝ) (88419146413/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66629/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8841914641/50000000000 : ℝ) (88419146413/500000000000 : ℝ) (58841914641/100000000000 : ℝ) (588419146413/1000000000000 : ℝ) (420521453459/1000000000000 : ℝ) (105130363367/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66629/524288 : ℝ))) 1 (58841914641/100000000000 : ℝ) (588419146413/1000000000000 : ℝ) (420521453459/1000000000000 : ℝ) (105130363367/250000000000 : ℝ) (252235149967/500000000000 : ℝ) (504470299941/1000000000000 : ℝ) (7772442221/15625000000 : ℝ) (62179537769/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66629/524288 : ℝ))) 2 (252235149967/500000000000 : ℝ) (504470299941/1000000000000 : ℝ) (7772442221/15625000000 : ℝ) (62179537769/125000000000 : ℝ) (500953301039/1000000000000 : ℝ) (500953301047/1000000000000 : ℝ) (62617619393/125000000000 : ℝ) (31308809697/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66629/524288 : ℝ))) 3 (500953301039/1000000000000 : ℝ) (500953301047/1000000000000 : ℝ) (62617619393/125000000000 : ℝ) (31308809697/62500000000 : ℝ) (500947128091/1000000000000 : ℝ) (5009471281/10000000000 : ℝ) (500947128053/1000000000000 : ℝ) (250473564031/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66629/524288 : ℝ))) 4 (500947128091/1000000000000 : ℝ) (5009471281/10000000000 : ℝ) (500947128053/1000000000000 : ℝ) (250473564031/500000000000 : ℝ) (62618391009/125000000000 : ℝ) (500947128081/1000000000000 : ℝ) (500947128071/1000000000000 : ℝ) (500947128081/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66629/524288 : ℝ))) 5 (62618391009/125000000000 : ℝ) (500947128081/1000000000000 : ℝ) (500947128071/1000000000000 : ℝ) (500947128081/1000000000000 : ℝ) (500947128071/1000000000000 : ℝ) (500947128081/1000000000000 : ℝ) (500947128071/1000000000000 : ℝ) (500947128081/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66629/524288 : ℝ))) 6 (500947128071/1000000000000 : ℝ) (500947128081/1000000000000 : ℝ) (500947128071/1000000000000 : ℝ) (500947128081/1000000000000 : ℝ) (500947128071/1000000000000 : ℝ) (500947128081/1000000000000 : ℝ) (500947128071/1000000000000 : ℝ) (500947128081/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66629/524288 : ℝ))) 7 (500947128071/1000000000000 : ℝ) (500947128081/1000000000000 : ℝ) (500947128071/1000000000000 : ℝ) (500947128081/1000000000000 : ℝ) (500947128071/1000000000000 : ℝ) (500947128081/1000000000000 : ℝ) (500947128071/1000000000000 : ℝ) (500947128081/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66629/524288 : ℝ)) hmem 8 (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ) (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66629/524288 : ℝ))) hcmem 8 (500947128071/1000000000000 : ℝ) (500947128081/1000000000000 : ℝ) (500947128071/1000000000000 : ℝ) (500947128081/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66629/524288 : ℝ)) (49605215607/50000000000 : ℝ) (62006519509/62500000000 : ℝ) (500947128071/1000000000000 : ℝ) (500947128081/1000000000000 : ℝ) (79314836057/100000000000 : ℝ) (79314836059/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0556_exp_lower
  have heNumeric : (10274516853/5000000000 : ℝ)/4 ≤ Real.exp (-4262819429651/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (10274516853/5000000000 : ℝ)/4 ≤ Real.exp ((16657/131072 : ℝ)-(79314836059/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16657/131072 : ℝ) (66629/524288 : ℝ) (79314836059/100000000000 : ℝ) (10274516853/5000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0557; no trusted numerical premise.
theorem cover8_leaf0557_exp_radius : (998016241514277251/1000000000000000000 : ℝ) ≤ Real.exp ((-33315/2097152 : ℝ)/8) ∧ Real.exp ((-33315/2097152 : ℝ)/8) ≤ (249504060378569313/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33315/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0557_exp_lower : (920113549927145479/1000000000000000000 : ℝ) ≤ Real.exp ((-85256389346603/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256389346603/128000000000000 : ℝ)/8) ≤ (23002838748178637/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256389346603/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0557_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451679251/500000000000 : ℝ) ≤ 4*Real.exp (66629/524288 : ℝ)*Real.exp (-mu (radius 8 (33315/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451679251/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33315/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0557_exp_radius
  have hrNumeric : (492119842179/500000000000 : ℝ) ≤ Real.exp (-33315/2097152 : ℝ) ∧ Real.exp (-33315/2097152 : ℝ) ≤ (984239684359/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492119842179/500000000000 : ℝ) ≤ (radius 8 (33315/262144 : ℝ)) ∧ (radius 8 (33315/262144 : ℝ)) ≤ (984239684359/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33315/262144 : ℝ)) (492119842179/500000000000 : ℝ) (984239684359/1000000000000 : ℝ) (88419799441/500000000000 : ℝ) (22104949861/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33315/262144 : ℝ)) (492119842179/500000000000 : ℝ) (984239684359/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33315/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492119842179/500000000000 : ℝ) (984239684359/1000000000000 : ℝ) (992119842179/1000000000000 : ℝ) (49605992109/50000000000 : ℝ) (992088546631/1000000000000 : ℝ) (992088546633/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33315/262144 : ℝ)) 1 (992119842179/1000000000000 : ℝ) (49605992109/50000000000 : ℝ) (992088546631/1000000000000 : ℝ) (992088546633/1000000000000 : ℝ) (198420838881/200000000000 : ℝ) (992104194407/1000000000000 : ℝ) (992104194281/1000000000000 : ℝ) (248026048571/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33315/262144 : ℝ)) 2 (198420838881/200000000000 : ℝ) (992104194407/1000000000000 : ℝ) (992104194281/1000000000000 : ℝ) (248026048571/250000000000 : ℝ) (992104194343/1000000000000 : ℝ) (496052097173/500000000000 : ℝ) (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33315/262144 : ℝ)) 3 (992104194343/1000000000000 : ℝ) (496052097173/500000000000 : ℝ) (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ) (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ) (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33315/262144 : ℝ)) 4 (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ) (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ) (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ) (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33315/262144 : ℝ)) 5 (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ) (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ) (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ) (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33315/262144 : ℝ)) 6 (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ) (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ) (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ) (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33315/262144 : ℝ)) 7 (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ) (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ) (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ) (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33315/262144 : ℝ))) (88419799441/500000000000 : ℝ) (22104949861/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33315/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88419799441/500000000000 : ℝ) (22104949861/125000000000 : ℝ) (588419799441/1000000000000 : ℝ) (147104949861/250000000000 : ℝ) (105130751591/250000000000 : ℝ) (105130751593/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33315/262144 : ℝ))) 1 (588419799441/1000000000000 : ℝ) (147104949861/250000000000 : ℝ) (105130751591/250000000000 : ℝ) (105130751593/250000000000 : ℝ) (252235701451/500000000000 : ℝ) (126117850727/250000000000 : ℝ) (497437496641/1000000000000 : ℝ) (62179687081/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33315/262144 : ℝ))) 2 (252235701451/500000000000 : ℝ) (126117850727/250000000000 : ℝ) (497437496641/1000000000000 : ℝ) (62179687081/125000000000 : ℝ) (500954449771/1000000000000 : ℝ) (250477224889/500000000000 : ℝ) (250471052113/500000000000 : ℝ) (500942104233/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33315/262144 : ℝ))) 3 (500954449771/1000000000000 : ℝ) (250477224889/500000000000 : ℝ) (250471052113/500000000000 : ℝ) (500942104233/1000000000000 : ℝ) (250474138499/500000000000 : ℝ) (250474138503/500000000000 : ℝ) (3130926731/6250000000 : ℝ) (62618534621/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33315/262144 : ℝ))) 4 (250474138499/500000000000 : ℝ) (250474138503/500000000000 : ℝ) (3130926731/6250000000 : ℝ) (62618534621/125000000000 : ℝ) (500948276979/1000000000000 : ℝ) (500948276987/1000000000000 : ℝ) (250474138489/500000000000 : ℝ) (500948276987/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33315/262144 : ℝ))) 5 (500948276979/1000000000000 : ℝ) (500948276987/1000000000000 : ℝ) (250474138489/500000000000 : ℝ) (500948276987/1000000000000 : ℝ) (250474138489/500000000000 : ℝ) (500948276987/1000000000000 : ℝ) (250474138489/500000000000 : ℝ) (500948276987/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33315/262144 : ℝ))) 6 (250474138489/500000000000 : ℝ) (500948276987/1000000000000 : ℝ) (250474138489/500000000000 : ℝ) (500948276987/1000000000000 : ℝ) (250474138489/500000000000 : ℝ) (500948276987/1000000000000 : ℝ) (250474138489/500000000000 : ℝ) (500948276987/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33315/262144 : ℝ))) 7 (250474138489/500000000000 : ℝ) (500948276987/1000000000000 : ℝ) (250474138489/500000000000 : ℝ) (500948276987/1000000000000 : ℝ) (250474138489/500000000000 : ℝ) (500948276987/1000000000000 : ℝ) (250474138489/500000000000 : ℝ) (500948276987/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33315/262144 : ℝ)) hmem 8 (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ) (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33315/262144 : ℝ))) hcmem 8 (250474138489/500000000000 : ℝ) (500948276987/1000000000000 : ℝ) (250474138489/500000000000 : ℝ) (500948276987/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33315/262144 : ℝ)) (496052097171/500000000000 : ℝ) (496052097173/500000000000 : ℝ) (250474138489/500000000000 : ℝ) (500948276987/1000000000000 : ℝ) (793150273807/1000000000000 : ℝ) (396575136913/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0557_exp_lower
  have heNumeric : (1027451679251/500000000000 : ℝ)/4 ≤ Real.exp (-85256389346603/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451679251/500000000000 : ℝ)/4 ≤ Real.exp ((66629/524288 : ℝ)-(396575136913/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66629/524288 : ℝ) (33315/262144 : ℝ) (396575136913/500000000000 : ℝ) (1027451679251/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0558; no trusted numerical premise.
theorem cover8_leaf0558_exp_radius : (249504052942768979/250000000000000000 : ℝ) ≤ Real.exp ((-66631/4194304 : ℝ)/8) ∧ Real.exp ((-66631/4194304 : ℝ)/8) ≤ (998016211771075917/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66631/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0558_exp_lower : (920113549251969931/1000000000000000000 : ℝ) ≤ Real.exp ((-8525639009801/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525639009801/12800000000000 : ℝ)/8) ≤ (230028387312992483/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525639009801/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0558_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903346439/1000000000000 : ℝ) ≤ 4*Real.exp (33315/262144 : ℝ)*Real.exp (-mu (radius 8 (66631/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903346439/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66631/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0558_exp_radius
  have hrNumeric : (984239449697/1000000000000 : ℝ) ≤ Real.exp (-66631/4194304 : ℝ) ∧ Real.exp (-66631/4194304 : ℝ) ≤ (492119724849/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984239449697/1000000000000 : ℝ) ≤ (radius 8 (66631/524288 : ℝ)) ∧ (radius 8 (66631/524288 : ℝ)) ≤ (492119724849/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66631/524288 : ℝ)) (984239449697/1000000000000 : ℝ) (492119724849/500000000000 : ℝ) (88420452467/500000000000 : ℝ) (176840904941/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66631/524288 : ℝ)) (984239449697/1000000000000 : ℝ) (492119724849/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66631/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984239449697/1000000000000 : ℝ) (492119724849/500000000000 : ℝ) (62007482803/62500000000 : ℝ) (992119724849/1000000000000 : ℝ) (198417685673/200000000000 : ℝ) (992088428367/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66631/524288 : ℝ)) 1 (62007482803/62500000000 : ℝ) (992119724849/1000000000000 : ℝ) (198417685673/200000000000 : ℝ) (992088428367/1000000000000 : ℝ) (496052038303/500000000000 : ℝ) (15501626197/15625000000 : ℝ) (992104076483/1000000000000 : ℝ) (198420815297/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66631/524288 : ℝ)) 2 (496052038303/500000000000 : ℝ) (15501626197/15625000000 : ℝ) (992104076483/1000000000000 : ℝ) (198420815297/200000000000 : ℝ) (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ) (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66631/524288 : ℝ)) 3 (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ) (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ) (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ) (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66631/524288 : ℝ)) 4 (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ) (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ) (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ) (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66631/524288 : ℝ)) 5 (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ) (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ) (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ) (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66631/524288 : ℝ)) 6 (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ) (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ) (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ) (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66631/524288 : ℝ)) 7 (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ) (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ) (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ) (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66631/524288 : ℝ))) (88420452467/500000000000 : ℝ) (176840904941/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66631/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88420452467/500000000000 : ℝ) (176840904941/1000000000000 : ℝ) (588420452467/1000000000000 : ℝ) (588420452471/1000000000000 : ℝ) (420524559251/1000000000000 : ℝ) (420524559261/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66631/524288 : ℝ))) 1 (588420452467/1000000000000 : ℝ) (588420452471/1000000000000 : ℝ) (420524559251/1000000000000 : ℝ) (420524559261/1000000000000 : ℝ) (504472505859/1000000000000 : ℝ) (252236252933/500000000000 : ℝ) (124359672781/250000000000 : ℝ) (497438691133/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66631/524288 : ℝ))) 2 (504472505859/1000000000000 : ℝ) (252236252933/500000000000 : ℝ) (124359672781/250000000000 : ℝ) (497438691133/1000000000000 : ℝ) (500955598491/1000000000000 : ℝ) (1001911197/2000000000 : ℝ) (100188650659/200000000000 : ℝ) (62617906663/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66631/524288 : ℝ))) 3 (500955598491/1000000000000 : ℝ) (1001911197/2000000000 : ℝ) (100188650659/200000000000 : ℝ) (62617906663/125000000000 : ℝ) (500949425893/1000000000000 : ℝ) (250474712951/500000000000 : ℝ) (250474712927/500000000000 : ℝ) (62618678233/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66631/524288 : ℝ))) 4 (500949425893/1000000000000 : ℝ) (250474712951/500000000000 : ℝ) (250474712927/500000000000 : ℝ) (62618678233/125000000000 : ℝ) (500949425873/1000000000000 : ℝ) (500949425883/1000000000000 : ℝ) (500949425873/1000000000000 : ℝ) (500949425883/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66631/524288 : ℝ))) 5 (500949425873/1000000000000 : ℝ) (500949425883/1000000000000 : ℝ) (500949425873/1000000000000 : ℝ) (500949425883/1000000000000 : ℝ) (500949425873/1000000000000 : ℝ) (500949425883/1000000000000 : ℝ) (500949425873/1000000000000 : ℝ) (500949425883/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66631/524288 : ℝ))) 6 (500949425873/1000000000000 : ℝ) (500949425883/1000000000000 : ℝ) (500949425873/1000000000000 : ℝ) (500949425883/1000000000000 : ℝ) (500949425873/1000000000000 : ℝ) (500949425883/1000000000000 : ℝ) (500949425873/1000000000000 : ℝ) (500949425883/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66631/524288 : ℝ))) 7 (500949425873/1000000000000 : ℝ) (500949425883/1000000000000 : ℝ) (500949425873/1000000000000 : ℝ) (500949425883/1000000000000 : ℝ) (500949425873/1000000000000 : ℝ) (500949425883/1000000000000 : ℝ) (500949425873/1000000000000 : ℝ) (500949425883/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66631/524288 : ℝ)) hmem 8 (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ) (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66631/524288 : ℝ))) hcmem 8 (500949425873/1000000000000 : ℝ) (500949425883/1000000000000 : ℝ) (500949425873/1000000000000 : ℝ) (500949425883/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66631/524288 : ℝ)) (3875406549/3906250000 : ℝ) (992104076547/1000000000000 : ℝ) (500949425873/1000000000000 : ℝ) (500949425883/1000000000000 : ℝ) (396576093513/500000000000 : ℝ) (158630437409/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0558_exp_lower
  have heNumeric : (2054903346439/1000000000000 : ℝ)/4 ≤ Real.exp (-8525639009801/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903346439/1000000000000 : ℝ)/4 ≤ Real.exp ((33315/262144 : ℝ)-(158630437409/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33315/262144 : ℝ) (66631/524288 : ℝ) (158630437409/200000000000 : ℝ) (2054903346439/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0559; no trusted numerical premise.
theorem cover8_leaf0559_exp_radius : (249504045506968867/250000000000000000 : ℝ) ≤ Real.exp ((-8329/524288 : ℝ)/8) ∧ Real.exp ((-8329/524288 : ℝ)/8) ≤ (998016182027875469/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8329/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0559_exp_lower : (11501419357240121/12500000000000000 : ℝ) ≤ Real.exp ((-85256390846729/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256390846729/128000000000000 : ℝ)/8) ≤ (920113548579209681/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256390846729/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0559_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903334419/1000000000000 : ℝ) ≤ 4*Real.exp (66631/524288 : ℝ)*Real.exp (-mu (radius 8 (8329/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903334419/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8329/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0559_exp_radius
  have hrNumeric : (246059803759/250000000000 : ℝ) ≤ Real.exp (-8329/524288 : ℝ) ∧ Real.exp (-8329/524288 : ℝ) ≤ (984239215037/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246059803759/250000000000 : ℝ) ≤ (radius 8 (8329/65536 : ℝ)) ∧ (radius 8 (8329/65536 : ℝ)) ≤ (984239215037/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8329/65536 : ℝ)) (246059803759/250000000000 : ℝ) (984239215037/1000000000000 : ℝ) (176842210977/1000000000000 : ℝ) (176842210983/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8329/65536 : ℝ)) (246059803759/250000000000 : ℝ) (984239215037/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8329/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246059803759/250000000000 : ℝ) (984239215037/1000000000000 : ℝ) (496059803759/500000000000 : ℝ) (992119607519/1000000000000 : ℝ) (992088310099/1000000000000 : ℝ) (9920883101/10000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8329/65536 : ℝ)) 1 (496059803759/500000000000 : ℝ) (992119607519/1000000000000 : ℝ) (992088310099/1000000000000 : ℝ) (9920883101/10000000000 : ℝ) (124012994851/125000000000 : ℝ) (99210395881/100000000000 : ℝ) (198420791737/200000000000 : ℝ) (992103958687/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8329/65536 : ℝ)) 2 (124012994851/125000000000 : ℝ) (99210395881/100000000000 : ℝ) (198420791737/200000000000 : ℝ) (992103958687/1000000000000 : ℝ) (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ) (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8329/65536 : ℝ)) 3 (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ) (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ) (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ) (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8329/65536 : ℝ)) 4 (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ) (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ) (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ) (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8329/65536 : ℝ)) 5 (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ) (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ) (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ) (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8329/65536 : ℝ)) 6 (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ) (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ) (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ) (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8329/65536 : ℝ)) 7 (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ) (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ) (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ) (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8329/65536 : ℝ))) (176842210977/1000000000000 : ℝ) (176842210983/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8329/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176842210977/1000000000000 : ℝ) (176842210983/1000000000000 : ℝ) (36776319093/62500000000 : ℝ) (147105276373/250000000000 : ℝ) (210263056061/500000000000 : ℝ) (42052611213/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8329/65536 : ℝ))) 1 (36776319093/62500000000 : ℝ) (147105276373/250000000000 : ℝ) (210263056061/500000000000 : ℝ) (42052611213/100000000000 : ℝ) (100894721761/200000000000 : ℝ) (504473608811/1000000000000 : ℝ) (99487977119/200000000000 : ℝ) (497439885603/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8329/65536 : ℝ))) 2 (100894721761/200000000000 : ℝ) (504473608811/1000000000000 : ℝ) (99487977119/200000000000 : ℝ) (497439885603/1000000000000 : ℝ) (313097967/625000000 : ℝ) (500956747207/1000000000000 : ℝ) (500944402353/1000000000000 : ℝ) (500944402361/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8329/65536 : ℝ))) 3 (313097967/625000000 : ℝ) (500956747207/1000000000000 : ℝ) (500944402353/1000000000000 : ℝ) (500944402361/1000000000000 : ℝ) (62618821847/125000000000 : ℝ) (7827352731/15625000000 : ℝ) (250475287369/500000000000 : ℝ) (250475287373/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8329/65536 : ℝ))) 4 (62618821847/125000000000 : ℝ) (7827352731/15625000000 : ℝ) (250475287369/500000000000 : ℝ) (250475287373/500000000000 : ℝ) (500950574757/1000000000000 : ℝ) (100190114953/200000000000 : ℝ) (125237643689/250000000000 : ℝ) (100190114953/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8329/65536 : ℝ))) 5 (500950574757/1000000000000 : ℝ) (100190114953/200000000000 : ℝ) (125237643689/250000000000 : ℝ) (100190114953/200000000000 : ℝ) (125237643689/250000000000 : ℝ) (100190114953/200000000000 : ℝ) (125237643689/250000000000 : ℝ) (100190114953/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8329/65536 : ℝ))) 6 (125237643689/250000000000 : ℝ) (100190114953/200000000000 : ℝ) (125237643689/250000000000 : ℝ) (100190114953/200000000000 : ℝ) (125237643689/250000000000 : ℝ) (100190114953/200000000000 : ℝ) (125237643689/250000000000 : ℝ) (100190114953/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8329/65536 : ℝ))) 7 (125237643689/250000000000 : ℝ) (100190114953/200000000000 : ℝ) (125237643689/250000000000 : ℝ) (100190114953/200000000000 : ℝ) (125237643689/250000000000 : ℝ) (100190114953/200000000000 : ℝ) (125237643689/250000000000 : ℝ) (100190114953/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8329/65536 : ℝ)) hmem 8 (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ) (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8329/65536 : ℝ))) hcmem 8 (125237643689/250000000000 : ℝ) (100190114953/200000000000 : ℝ) (125237643689/250000000000 : ℝ) (100190114953/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8329/65536 : ℝ)) (496051979373/500000000000 : ℝ) (992103958749/1000000000000 : ℝ) (125237643689/250000000000 : ℝ) (100190114953/200000000000 : ℝ) (396577050113/500000000000 : ℝ) (793154100243/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0559_exp_lower
  have heNumeric : (2054903334419/1000000000000 : ℝ)/4 ≤ Real.exp (-85256390846729/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903334419/1000000000000 : ℝ)/4 ≤ Real.exp ((66631/524288 : ℝ)-(793154100243/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66631/524288 : ℝ) (8329/65536 : ℝ) (793154100243/1000000000000 : ℝ) (2054903334419/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0560; no trusted numerical premise.
theorem cover8_leaf0560_exp_radius : (499008076142337953/500000000000000000 : ℝ) ≤ Real.exp ((-66633/4194304 : ℝ)/8) ∧ Real.exp ((-66633/4194304 : ℝ)/8) ≤ (998016152284675907/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66633/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0560_exp_lower : (920113547909209771/1000000000000000000 : ℝ) ≤ Real.exp ((-10657048949047/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657048949047/16000000000000 : ℝ)/8) ≤ (230028386977302443/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657048949047/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0560_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431457653/62500000000 : ℝ) ≤ 4*Real.exp (8329/65536 : ℝ)*Real.exp (-mu (radius 8 (66633/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (128431457653/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66633/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0560_exp_radius
  have hrNumeric : (123029872547/125000000000 : ℝ) ≤ Real.exp (-66633/4194304 : ℝ) ∧ Real.exp (-66633/4194304 : ℝ) ≤ (984238980377/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123029872547/125000000000 : ℝ) ≤ (radius 8 (66633/524288 : ℝ)) ∧ (radius 8 (66633/524288 : ℝ)) ≤ (984238980377/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66633/524288 : ℝ)) (123029872547/125000000000 : ℝ) (984238980377/1000000000000 : ℝ) (44210879251/250000000000 : ℝ) (17684351701/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66633/524288 : ℝ)) (123029872547/125000000000 : ℝ) (984238980377/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66633/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123029872547/125000000000 : ℝ) (984238980377/1000000000000 : ℝ) (248029872547/250000000000 : ℝ) (992119490189/1000000000000 : ℝ) (992088191833/1000000000000 : ℝ) (198417638367/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66633/524288 : ℝ)) 1 (248029872547/250000000000 : ℝ) (992119490189/1000000000000 : ℝ) (992088191833/1000000000000 : ℝ) (198417638367/200000000000 : ℝ) (99210384101/100000000000 : ℝ) (248025960253/250000000000 : ℝ) (992103840887/1000000000000 : ℝ) (992103840889/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66633/524288 : ℝ)) 2 (99210384101/100000000000 : ℝ) (248025960253/250000000000 : ℝ) (992103840887/1000000000000 : ℝ) (992103840889/1000000000000 : ℝ) (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ) (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66633/524288 : ℝ)) 3 (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ) (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ) (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ) (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66633/524288 : ℝ)) 4 (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ) (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ) (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ) (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66633/524288 : ℝ)) 5 (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ) (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ) (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ) (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66633/524288 : ℝ)) 6 (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ) (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ) (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ) (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66633/524288 : ℝ)) 7 (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ) (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ) (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ) (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66633/524288 : ℝ))) (44210879251/250000000000 : ℝ) (17684351701/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66633/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44210879251/250000000000 : ℝ) (17684351701/100000000000 : ℝ) (294210879251/500000000000 : ℝ) (117684351701/200000000000 : ℝ) (52565958121/125000000000 : ℝ) (26282979061/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66633/524288 : ℝ))) 1 (294210879251/500000000000 : ℝ) (117684351701/200000000000 : ℝ) (52565958121/125000000000 : ℝ) (26282979061/62500000000 : ℝ) (100894942347/200000000000 : ℝ) (504474711741/1000000000000 : ℝ) (497441080047/1000000000000 : ℝ) (248720540027/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66633/524288 : ℝ))) 2 (100894942347/200000000000 : ℝ) (504474711741/1000000000000 : ℝ) (497441080047/1000000000000 : ℝ) (248720540027/500000000000 : ℝ) (500957895891/1000000000000 : ℝ) (250478947949/500000000000 : ℝ) (250472775697/500000000000 : ℝ) (500945551401/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66633/524288 : ℝ))) 3 (500957895891/1000000000000 : ℝ) (250478947949/500000000000 : ℝ) (250472775697/500000000000 : ℝ) (500945551401/1000000000000 : ℝ) (250475861821/500000000000 : ℝ) (10019034473/20000000000 : ℝ) (125237930901/250000000000 : ℝ) (125237930903/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66633/524288 : ℝ))) 4 (250475861821/500000000000 : ℝ) (10019034473/20000000000 : ℝ) (125237930901/250000000000 : ℝ) (125237930903/250000000000 : ℝ) (500951723623/1000000000000 : ℝ) (500951723631/1000000000000 : ℝ) (250475861811/500000000000 : ℝ) (500951723631/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66633/524288 : ℝ))) 5 (500951723623/1000000000000 : ℝ) (500951723631/1000000000000 : ℝ) (250475861811/500000000000 : ℝ) (500951723631/1000000000000 : ℝ) (250475861811/500000000000 : ℝ) (500951723631/1000000000000 : ℝ) (250475861811/500000000000 : ℝ) (500951723631/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66633/524288 : ℝ))) 6 (250475861811/500000000000 : ℝ) (500951723631/1000000000000 : ℝ) (250475861811/500000000000 : ℝ) (500951723631/1000000000000 : ℝ) (250475861811/500000000000 : ℝ) (500951723631/1000000000000 : ℝ) (250475861811/500000000000 : ℝ) (500951723631/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66633/524288 : ℝ))) 7 (250475861811/500000000000 : ℝ) (500951723631/1000000000000 : ℝ) (250475861811/500000000000 : ℝ) (500951723631/1000000000000 : ℝ) (250475861811/500000000000 : ℝ) (500951723631/1000000000000 : ℝ) (250475861811/500000000000 : ℝ) (500951723631/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66633/524288 : ℝ)) hmem 8 (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ) (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66633/524288 : ℝ))) hcmem 8 (250475861811/500000000000 : ℝ) (500951723631/1000000000000 : ℝ) (250475861811/500000000000 : ℝ) (500951723631/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66633/524288 : ℝ)) (248025960237/250000000000 : ℝ) (992103840951/1000000000000 : ℝ) (250475861811/500000000000 : ℝ) (500951723631/1000000000000 : ℝ) (793156013399/1000000000000 : ℝ) (793156013417/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0560_exp_lower
  have heNumeric : (128431457653/62500000000 : ℝ)/4 ≤ Real.exp (-10657048949047/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431457653/62500000000 : ℝ)/4 ≤ Real.exp ((8329/65536 : ℝ)-(793156013417/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8329/65536 : ℝ) (66633/524288 : ℝ) (793156013417/1000000000000 : ℝ) (128431457653/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0561; no trusted numerical premise.
theorem cover8_leaf0561_exp_radius : (998016122541477231/1000000000000000000 : ℝ) ≤ Real.exp ((-33317/2097152 : ℝ)/8) ∧ Real.exp ((-33317/2097152 : ℝ)/8) ≤ (62376007658842327/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33317/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0561_exp_lower : (920113547240475019/1000000000000000000 : ℝ) ≤ Real.exp ((-17051278467323/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051278467323/25600000000000 : ℝ)/8) ≤ (46005677362023751/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051278467323/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0561_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (4109806621/2000000000 : ℝ) ≤ 4*Real.exp (66633/524288 : ℝ)*Real.exp (-mu (radius 8 (33317/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (4109806621/2000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33317/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0561_exp_radius
  have hrNumeric : (196847749143/200000000000 : ℝ) ≤ Real.exp (-33317/2097152 : ℝ) ∧ Real.exp (-33317/2097152 : ℝ) ≤ (246059686429/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196847749143/200000000000 : ℝ) ≤ (radius 8 (33317/262144 : ℝ)) ∧ (radius 8 (33317/262144 : ℝ)) ≤ (246059686429/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33317/262144 : ℝ)) (196847749143/200000000000 : ℝ) (246059686429/250000000000 : ℝ) (88422411513/500000000000 : ℝ) (176844823033/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33317/262144 : ℝ)) (196847749143/200000000000 : ℝ) (246059686429/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33317/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196847749143/200000000000 : ℝ) (246059686429/250000000000 : ℝ) (992119372857/1000000000000 : ℝ) (496059686429/500000000000 : ℝ) (992088073567/1000000000000 : ℝ) (992088073569/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33317/262144 : ℝ)) 1 (992119372857/1000000000000 : ℝ) (496059686429/500000000000 : ℝ) (992088073567/1000000000000 : ℝ) (992088073569/1000000000000 : ℝ) (248025930803/250000000000 : ℝ) (496051861607/500000000000 : ℝ) (62006482693/62500000000 : ℝ) (992103723091/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33317/262144 : ℝ)) 2 (248025930803/250000000000 : ℝ) (496051861607/500000000000 : ℝ) (62006482693/62500000000 : ℝ) (992103723091/1000000000000 : ℝ) (19842074463/20000000000 : ℝ) (992103723153/1000000000000 : ℝ) (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33317/262144 : ℝ)) 3 (19842074463/20000000000 : ℝ) (992103723153/1000000000000 : ℝ) (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ) (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ) (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33317/262144 : ℝ)) 4 (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ) (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ) (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ) (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33317/262144 : ℝ)) 5 (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ) (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ) (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ) (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33317/262144 : ℝ)) 6 (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ) (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ) (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ) (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33317/262144 : ℝ)) 7 (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ) (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ) (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ) (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33317/262144 : ℝ))) (88422411513/500000000000 : ℝ) (176844823033/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33317/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88422411513/500000000000 : ℝ) (176844823033/1000000000000 : ℝ) (588422411513/1000000000000 : ℝ) (588422411517/1000000000000 : ℝ) (210264608901/500000000000 : ℝ) (105132304453/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33317/262144 : ℝ))) 1 (588422411513/1000000000000 : ℝ) (588422411517/1000000000000 : ℝ) (210264608901/500000000000 : ℝ) (105132304453/250000000000 : ℝ) (504475814657/1000000000000 : ℝ) (100895162933/200000000000 : ℝ) (49744227449/100000000000 : ℝ) (497442274499/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33317/262144 : ℝ))) 2 (504475814657/1000000000000 : ℝ) (100895162933/200000000000 : ℝ) (49744227449/100000000000 : ℝ) (497442274499/1000000000000 : ℝ) (500959044573/1000000000000 : ℝ) (250479522291/500000000000 : ℝ) (250473350213/500000000000 : ℝ) (100189340087/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33317/262144 : ℝ))) 3 (500959044573/1000000000000 : ℝ) (250479522291/500000000000 : ℝ) (250473350213/500000000000 : ℝ) (100189340087/200000000000 : ℝ) (500952872499/1000000000000 : ℝ) (500952872509/1000000000000 : ℝ) (500952872461/1000000000000 : ℝ) (500952872471/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33317/262144 : ℝ))) 4 (500952872499/1000000000000 : ℝ) (500952872509/1000000000000 : ℝ) (500952872461/1000000000000 : ℝ) (500952872471/1000000000000 : ℝ) (3130955453/6250000000 : ℝ) (50095287249/100000000000 : ℝ) (500952872479/1000000000000 : ℝ) (50095287249/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33317/262144 : ℝ))) 5 (3130955453/6250000000 : ℝ) (50095287249/100000000000 : ℝ) (500952872479/1000000000000 : ℝ) (50095287249/100000000000 : ℝ) (500952872479/1000000000000 : ℝ) (50095287249/100000000000 : ℝ) (500952872479/1000000000000 : ℝ) (50095287249/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33317/262144 : ℝ))) 6 (500952872479/1000000000000 : ℝ) (50095287249/100000000000 : ℝ) (500952872479/1000000000000 : ℝ) (50095287249/100000000000 : ℝ) (500952872479/1000000000000 : ℝ) (50095287249/100000000000 : ℝ) (500952872479/1000000000000 : ℝ) (50095287249/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33317/262144 : ℝ))) 7 (500952872479/1000000000000 : ℝ) (50095287249/100000000000 : ℝ) (500952872479/1000000000000 : ℝ) (50095287249/100000000000 : ℝ) (500952872479/1000000000000 : ℝ) (50095287249/100000000000 : ℝ) (500952872479/1000000000000 : ℝ) (50095287249/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33317/262144 : ℝ)) hmem 8 (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ) (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33317/262144 : ℝ))) hcmem 8 (500952872479/1000000000000 : ℝ) (50095287249/100000000000 : ℝ) (500952872479/1000000000000 : ℝ) (50095287249/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33317/262144 : ℝ)) (992103723149/1000000000000 : ℝ) (992103723153/1000000000000 : ℝ) (500952872479/1000000000000 : ℝ) (50095287249/100000000000 : ℝ) (396578963279/500000000000 : ℝ) (39657896329/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0561_exp_lower
  have heNumeric : (4109806621/2000000000 : ℝ)/4 ≤ Real.exp (-17051278467323/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (4109806621/2000000000 : ℝ)/4 ≤ Real.exp ((66633/524288 : ℝ)-(39657896329/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66633/524288 : ℝ) (33317/262144 : ℝ) (39657896329/50000000000 : ℝ) (4109806621/2000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0562; no trusted numerical premise.
theorem cover8_leaf0562_exp_radius : (499008046399139721/500000000000000000 : ℝ) ≤ Real.exp ((-66635/4194304 : ℝ)/8) ∧ Real.exp ((-66635/4194304 : ℝ)/8) ≤ (998016092798279443/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66635/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0562_exp_lower : (920113546573925537/1000000000000000000 : ℝ) ≤ Real.exp ((-42628196539211/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628196539211/64000000000000 : ℝ)/8) ≤ (460056773286962769/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628196539211/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0562_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903298591/1000000000000 : ℝ) ≤ 4*Real.exp (33317/262144 : ℝ)*Real.exp (-mu (radius 8 (66635/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903298591/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66635/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0562_exp_radius
  have hrNumeric : (492119255527/500000000000 : ℝ) ≤ Real.exp (-66635/4194304 : ℝ) ∧ Real.exp (-66635/4194304 : ℝ) ≤ (196847702211/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492119255527/500000000000 : ℝ) ≤ (radius 8 (66635/524288 : ℝ)) ∧ (radius 8 (66635/524288 : ℝ)) ≤ (196847702211/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66635/524288 : ℝ)) (492119255527/500000000000 : ℝ) (196847702211/200000000000 : ℝ) (176846129039/1000000000000 : ℝ) (88423064523/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66635/524288 : ℝ)) (492119255527/500000000000 : ℝ) (196847702211/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66635/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492119255527/500000000000 : ℝ) (196847702211/200000000000 : ℝ) (992119255527/1000000000000 : ℝ) (124014906941/125000000000 : ℝ) (992087955301/1000000000000 : ℝ) (496043977651/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66635/524288 : ℝ)) 1 (992119255527/1000000000000 : ℝ) (124014906941/125000000000 : ℝ) (992087955301/1000000000000 : ℝ) (496043977651/500000000000 : ℝ) (496051802707/500000000000 : ℝ) (198420721083/200000000000 : ℝ) (99210360529/100000000000 : ℝ) (248025901323/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66635/524288 : ℝ)) 2 (496051802707/500000000000 : ℝ) (198420721083/200000000000 : ℝ) (99210360529/100000000000 : ℝ) (248025901323/250000000000 : ℝ) (124012950669/125000000000 : ℝ) (496051802677/500000000000 : ℝ) (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66635/524288 : ℝ)) 3 (124012950669/125000000000 : ℝ) (496051802677/500000000000 : ℝ) (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ) (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ) (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66635/524288 : ℝ)) 4 (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ) (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ) (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ) (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66635/524288 : ℝ)) 5 (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ) (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ) (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ) (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66635/524288 : ℝ)) 6 (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ) (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ) (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ) (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66635/524288 : ℝ)) 7 (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ) (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ) (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ) (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66635/524288 : ℝ))) (176846129039/1000000000000 : ℝ) (88423064523/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66635/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176846129039/1000000000000 : ℝ) (88423064523/500000000000 : ℝ) (588423064519/1000000000000 : ℝ) (588423064523/1000000000000 : ℝ) (21026538531/50000000000 : ℝ) (42053077063/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66635/524288 : ℝ))) 1 (588423064519/1000000000000 : ℝ) (588423064523/1000000000000 : ℝ) (21026538531/50000000000 : ℝ) (42053077063/100000000000 : ℝ) (504476917569/1000000000000 : ℝ) (504476917577/1000000000000 : ℝ) (497443468921/1000000000000 : ℝ) (49744346893/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66635/524288 : ℝ))) 2 (504476917569/1000000000000 : ℝ) (504476917577/1000000000000 : ℝ) (497443468921/1000000000000 : ℝ) (49744346893/100000000000 : ℝ) (100192038649/200000000000 : ℝ) (250480096627/500000000000 : ℝ) (500947849447/1000000000000 : ℝ) (500947849457/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66635/524288 : ℝ))) 3 (100192038649/200000000000 : ℝ) (250480096627/500000000000 : ℝ) (500947849447/1000000000000 : ℝ) (500947849457/1000000000000 : ℝ) (250477010673/500000000000 : ℝ) (125238505339/250000000000 : ℝ) (500954021307/1000000000000 : ℝ) (250477010659/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66635/524288 : ℝ))) 4 (250477010673/500000000000 : ℝ) (125238505339/250000000000 : ℝ) (500954021307/1000000000000 : ℝ) (250477010659/500000000000 : ℝ) (250477010663/500000000000 : ℝ) (500954021337/1000000000000 : ℝ) (250477010663/500000000000 : ℝ) (500954021337/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66635/524288 : ℝ))) 5 (250477010663/500000000000 : ℝ) (500954021337/1000000000000 : ℝ) (250477010663/500000000000 : ℝ) (500954021337/1000000000000 : ℝ) (250477010663/500000000000 : ℝ) (500954021337/1000000000000 : ℝ) (250477010663/500000000000 : ℝ) (500954021337/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66635/524288 : ℝ))) 6 (250477010663/500000000000 : ℝ) (500954021337/1000000000000 : ℝ) (250477010663/500000000000 : ℝ) (500954021337/1000000000000 : ℝ) (250477010663/500000000000 : ℝ) (500954021337/1000000000000 : ℝ) (250477010663/500000000000 : ℝ) (500954021337/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66635/524288 : ℝ))) 7 (250477010663/500000000000 : ℝ) (500954021337/1000000000000 : ℝ) (250477010663/500000000000 : ℝ) (500954021337/1000000000000 : ℝ) (250477010663/500000000000 : ℝ) (500954021337/1000000000000 : ℝ) (250477010663/500000000000 : ℝ) (500954021337/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66635/524288 : ℝ)) hmem 8 (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ) (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66635/524288 : ℝ))) hcmem 8 (250477010663/500000000000 : ℝ) (500954021337/1000000000000 : ℝ) (250477010663/500000000000 : ℝ) (500954021337/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66635/524288 : ℝ)) (992103605351/1000000000000 : ℝ) (496051802677/500000000000 : ℝ) (250477010663/500000000000 : ℝ) (500954021337/1000000000000 : ℝ) (793159839703/1000000000000 : ℝ) (198289959931/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0562_exp_lower
  have heNumeric : (2054903298591/1000000000000 : ℝ)/4 ≤ Real.exp (-42628196539211/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903298591/1000000000000 : ℝ)/4 ≤ Real.exp ((33317/262144 : ℝ)-(198289959931/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33317/262144 : ℝ) (66635/524288 : ℝ) (198289959931/250000000000 : ℝ) (2054903298591/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0563; no trusted numerical premise.
theorem cover8_leaf0563_exp_radius : (49900803152754127/50000000000000000 : ℝ) ≤ Real.exp ((-16659/1048576 : ℝ)/8) ∧ Real.exp ((-16659/1048576 : ℝ)/8) ≤ (998016063055082541/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16659/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0563_exp_lower : (920113545910021381/1000000000000000000 : ℝ) ≤ Real.exp ((-17051278763457/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051278763457/25600000000000 : ℝ)/8) ≤ (460056772955010691/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051278763457/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0563_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490328673/100000000000 : ℝ) ≤ 4*Real.exp (66635/524288 : ℝ)*Real.exp (-mu (radius 8 (16659/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (205490328673/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16659/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0563_exp_radius
  have hrNumeric : (984238276393/1000000000000 : ℝ) ≤ Real.exp (-16659/1048576 : ℝ) ∧ Real.exp (-16659/1048576 : ℝ) ≤ (492119138197/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984238276393/1000000000000 : ℝ) ≤ (radius 8 (16659/131072 : ℝ)) ∧ (radius 8 (16659/131072 : ℝ)) ≤ (492119138197/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16659/131072 : ℝ)) (984238276393/1000000000000 : ℝ) (492119138197/500000000000 : ℝ) (88423717521/500000000000 : ℝ) (22105929381/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16659/131072 : ℝ)) (984238276393/1000000000000 : ℝ) (492119138197/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16659/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984238276393/1000000000000 : ℝ) (492119138197/500000000000 : ℝ) (248029784549/250000000000 : ℝ) (992119138197/1000000000000 : ℝ) (198417567407/200000000000 : ℝ) (248021959259/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16659/131072 : ℝ)) 1 (248029784549/250000000000 : ℝ) (992119138197/1000000000000 : ℝ) (198417567407/200000000000 : ℝ) (248021959259/250000000000 : ℝ) (198420697523/200000000000 : ℝ) (992103487617/1000000000000 : ℝ) (248025871873/250000000000 : ℝ) (496051743747/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16659/131072 : ℝ)) 2 (198420697523/200000000000 : ℝ) (992103487617/1000000000000 : ℝ) (248025871873/250000000000 : ℝ) (496051743747/500000000000 : ℝ) (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ) (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16659/131072 : ℝ)) 3 (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ) (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ) (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ) (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16659/131072 : ℝ)) 4 (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ) (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ) (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ) (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16659/131072 : ℝ)) 5 (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ) (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ) (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ) (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16659/131072 : ℝ)) 6 (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ) (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ) (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ) (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16659/131072 : ℝ)) 7 (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ) (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ) (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ) (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16659/131072 : ℝ))) (88423717521/500000000000 : ℝ) (22105929381/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16659/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88423717521/500000000000 : ℝ) (22105929381/125000000000 : ℝ) (588423717521/1000000000000 : ℝ) (147105929381/250000000000 : ℝ) (420532323421/1000000000000 : ℝ) (420532323429/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16659/131072 : ℝ))) 1 (588423717521/1000000000000 : ℝ) (147105929381/250000000000 : ℝ) (420532323421/1000000000000 : ℝ) (420532323429/1000000000000 : ℝ) (504478020471/1000000000000 : ℝ) (504478020477/1000000000000 : ℝ) (497444663339/1000000000000 : ℝ) (248722331673/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16659/131072 : ℝ))) 2 (504478020471/1000000000000 : ℝ) (504478020477/1000000000000 : ℝ) (497444663339/1000000000000 : ℝ) (248722331673/500000000000 : ℝ) (100192268381/200000000000 : ℝ) (62620167739/125000000000 : ℝ) (500948998457/1000000000000 : ℝ) (7827328101/15625000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16659/131072 : ℝ))) 3 (100192268381/200000000000 : ℝ) (62620167739/125000000000 : ℝ) (500948998457/1000000000000 : ℝ) (7827328101/15625000000 : ℝ) (500955170181/1000000000000 : ℝ) (125238792547/250000000000 : ℝ) (250477585071/500000000000 : ℝ) (10019103403/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16659/131072 : ℝ))) 4 (500955170181/1000000000000 : ℝ) (125238792547/250000000000 : ℝ) (250477585071/500000000000 : ℝ) (10019103403/20000000000 : ℝ) (500955170161/1000000000000 : ℝ) (500955170169/1000000000000 : ℝ) (500955170161/1000000000000 : ℝ) (500955170169/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16659/131072 : ℝ))) 5 (500955170161/1000000000000 : ℝ) (500955170169/1000000000000 : ℝ) (500955170161/1000000000000 : ℝ) (500955170169/1000000000000 : ℝ) (500955170161/1000000000000 : ℝ) (500955170169/1000000000000 : ℝ) (500955170161/1000000000000 : ℝ) (500955170169/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16659/131072 : ℝ))) 6 (500955170161/1000000000000 : ℝ) (500955170169/1000000000000 : ℝ) (500955170161/1000000000000 : ℝ) (500955170169/1000000000000 : ℝ) (500955170161/1000000000000 : ℝ) (500955170169/1000000000000 : ℝ) (500955170161/1000000000000 : ℝ) (500955170169/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16659/131072 : ℝ))) 7 (500955170161/1000000000000 : ℝ) (500955170169/1000000000000 : ℝ) (500955170161/1000000000000 : ℝ) (500955170169/1000000000000 : ℝ) (500955170161/1000000000000 : ℝ) (500955170169/1000000000000 : ℝ) (500955170161/1000000000000 : ℝ) (500955170169/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16659/131072 : ℝ)) hmem 8 (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ) (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16659/131072 : ℝ))) hcmem 8 (500955170161/1000000000000 : ℝ) (500955170169/1000000000000 : ℝ) (500955170161/1000000000000 : ℝ) (500955170169/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16659/131072 : ℝ)) (992103487553/1000000000000 : ℝ) (248025871889/250000000000 : ℝ) (500955170161/1000000000000 : ℝ) (500955170169/1000000000000 : ℝ) (793161752829/1000000000000 : ℝ) (158632350569/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0563_exp_lower
  have heNumeric : (205490328673/100000000000 : ℝ)/4 ≤ Real.exp (-17051278763457/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490328673/100000000000 : ℝ)/4 ≤ Real.exp ((66635/524288 : ℝ)-(158632350569/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66635/524288 : ℝ) (16659/131072 : ℝ) (158632350569/200000000000 : ℝ) (205490328673/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0564; no trusted numerical premise.
theorem cover8_leaf0564_exp_radius : (249504008327971631/250000000000000000 : ℝ) ≤ Real.exp ((-66637/4194304 : ℝ)/8) ∧ Real.exp ((-66637/4194304 : ℝ)/8) ≤ (39920641332475461/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66637/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0564_exp_lower : (920113545248992581/1000000000000000000 : ℝ) ≤ Real.exp ((-21314098638237/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314098638237/32000000000000 : ℝ)/8) ≤ (460056772624496291/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314098638237/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0564_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903274919/1000000000000 : ℝ) ≤ 4*Real.exp (16659/131072 : ℝ)*Real.exp (-mu (radius 8 (66637/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903274919/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66637/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0564_exp_radius
  have hrNumeric : (984238041733/1000000000000 : ℝ) ≤ Real.exp (-66637/4194304 : ℝ) ∧ Real.exp (-66637/4194304 : ℝ) ≤ (492119020867/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984238041733/1000000000000 : ℝ) ≤ (radius 8 (66637/524288 : ℝ)) ∧ (radius 8 (66637/524288 : ℝ)) ≤ (492119020867/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66637/524288 : ℝ)) (984238041733/1000000000000 : ℝ) (492119020867/500000000000 : ℝ) (176848741029/1000000000000 : ℝ) (35369748207/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66637/524288 : ℝ)) (984238041733/1000000000000 : ℝ) (492119020867/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66637/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984238041733/1000000000000 : ℝ) (492119020867/500000000000 : ℝ) (496059510433/500000000000 : ℝ) (992119020867/1000000000000 : ℝ) (992087718769/1000000000000 : ℝ) (99208771877/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66637/524288 : ℝ)) 1 (496059510433/500000000000 : ℝ) (992119020867/1000000000000 : ℝ) (992087718769/1000000000000 : ℝ) (99208771877/100000000000 : ℝ) (992103369817/1000000000000 : ℝ) (992103369819/1000000000000 : ℝ) (496051684847/500000000000 : ℝ) (31003230303/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66637/524288 : ℝ)) 2 (992103369817/1000000000000 : ℝ) (992103369819/1000000000000 : ℝ) (496051684847/500000000000 : ℝ) (31003230303/31250000000 : ℝ) (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ) (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66637/524288 : ℝ)) 3 (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ) (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ) (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ) (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66637/524288 : ℝ)) 4 (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ) (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ) (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ) (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66637/524288 : ℝ)) 5 (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ) (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ) (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ) (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66637/524288 : ℝ)) 6 (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ) (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ) (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ) (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66637/524288 : ℝ)) 7 (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ) (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ) (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ) (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66637/524288 : ℝ))) (176848741029/1000000000000 : ℝ) (35369748207/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66637/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176848741029/1000000000000 : ℝ) (35369748207/200000000000 : ℝ) (294212185257/500000000000 : ℝ) (294212185259/500000000000 : ℝ) (105133469049/250000000000 : ℝ) (105133469051/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66637/524288 : ℝ))) 1 (294212185257/500000000000 : ℝ) (294212185259/500000000000 : ℝ) (105133469049/250000000000 : ℝ) (105133469051/250000000000 : ℝ) (100895824671/200000000000 : ℝ) (504479123361/1000000000000 : ℝ) (497445857737/1000000000000 : ℝ) (99489171549/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66637/524288 : ℝ))) 2 (100895824671/200000000000 : ℝ) (504479123361/1000000000000 : ℝ) (497445857737/1000000000000 : ℝ) (99489171549/200000000000 : ℝ) (250481245273/500000000000 : ℝ) (500962490553/1000000000000 : ℝ) (500950147447/1000000000000 : ℝ) (100190029491/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66637/524288 : ℝ))) 3 (250481245273/500000000000 : ℝ) (500962490553/1000000000000 : ℝ) (500950147447/1000000000000 : ℝ) (100190029491/200000000000 : ℝ) (125239079749/250000000000 : ℝ) (125239079751/250000000000 : ℝ) (250478159479/500000000000 : ℝ) (250478159483/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66637/524288 : ℝ))) 4 (125239079749/250000000000 : ℝ) (125239079751/250000000000 : ℝ) (250478159479/500000000000 : ℝ) (250478159483/500000000000 : ℝ) (500956318977/1000000000000 : ℝ) (100191263797/200000000000 : ℝ) (1956860621/3906250000 : ℝ) (100191263797/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66637/524288 : ℝ))) 5 (500956318977/1000000000000 : ℝ) (100191263797/200000000000 : ℝ) (1956860621/3906250000 : ℝ) (100191263797/200000000000 : ℝ) (1956860621/3906250000 : ℝ) (100191263797/200000000000 : ℝ) (1956860621/3906250000 : ℝ) (100191263797/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66637/524288 : ℝ))) 6 (1956860621/3906250000 : ℝ) (100191263797/200000000000 : ℝ) (1956860621/3906250000 : ℝ) (100191263797/200000000000 : ℝ) (1956860621/3906250000 : ℝ) (100191263797/200000000000 : ℝ) (1956860621/3906250000 : ℝ) (100191263797/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66637/524288 : ℝ))) 7 (1956860621/3906250000 : ℝ) (100191263797/200000000000 : ℝ) (1956860621/3906250000 : ℝ) (100191263797/200000000000 : ℝ) (1956860621/3906250000 : ℝ) (100191263797/200000000000 : ℝ) (1956860621/3906250000 : ℝ) (100191263797/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66637/524288 : ℝ)) hmem 8 (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ) (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66637/524288 : ℝ))) hcmem 8 (1956860621/3906250000 : ℝ) (100191263797/200000000000 : ℝ) (1956860621/3906250000 : ℝ) (100191263797/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66637/524288 : ℝ)) (198420673951/200000000000 : ℝ) (496051684879/500000000000 : ℝ) (1956860621/3906250000 : ℝ) (100191263797/200000000000 : ℝ) (793163665923/1000000000000 : ℝ) (793163665941/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0564_exp_lower
  have heNumeric : (2054903274919/1000000000000 : ℝ)/4 ≤ Real.exp (-21314098638237/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903274919/1000000000000 : ℝ)/4 ≤ Real.exp ((16659/131072 : ℝ)-(793163665941/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16659/131072 : ℝ) (66637/524288 : ℝ) (793163665941/1000000000000 : ℝ) (2054903274919/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0565; no trusted numerical premise.
theorem cover8_leaf0565_exp_radius : (499008001784345697/500000000000000000 : ℝ) ≤ Real.exp ((-33319/2097152 : ℝ)/8) ∧ Real.exp ((-33319/2097152 : ℝ)/8) ≤ (199603200713738279/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33319/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0565_exp_lower : (460056772294614469/500000000000000000 : ℝ) ≤ Real.exp ((-85256395287203/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256395287203/128000000000000 : ℝ)/8) ≤ (920113544589228939/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256395287203/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0565_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725815783/250000000000 : ℝ) ≤ 4*Real.exp (66637/524288 : ℝ)*Real.exp (-mu (radius 8 (33319/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725815783/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33319/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0565_exp_radius
  have hrNumeric : (30757431471/31250000000 : ℝ) ≤ Real.exp (-33319/2097152 : ℝ) ∧ Real.exp (-33319/2097152 : ℝ) ≤ (984237807073/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30757431471/31250000000 : ℝ) ≤ (radius 8 (33319/262144 : ℝ)) ∧ (radius 8 (33319/262144 : ℝ)) ≤ (984237807073/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33319/262144 : ℝ)) (30757431471/31250000000 : ℝ) (984237807073/1000000000000 : ℝ) (176850047011/1000000000000 : ℝ) (88425023509/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33319/262144 : ℝ)) (30757431471/31250000000 : ℝ) (984237807073/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33319/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30757431471/31250000000 : ℝ) (984237807073/1000000000000 : ℝ) (62007431471/62500000000 : ℝ) (992118903537/1000000000000 : ℝ) (992087600503/1000000000000 : ℝ) (124010950063/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33319/262144 : ℝ)) 1 (62007431471/62500000000 : ℝ) (992118903537/1000000000000 : ℝ) (992087600503/1000000000000 : ℝ) (124010950063/125000000000 : ℝ) (992103252019/1000000000000 : ℝ) (992103252021/1000000000000 : ℝ) (124012906487/125000000000 : ℝ) (496051625949/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33319/262144 : ℝ)) 2 (992103252019/1000000000000 : ℝ) (992103252021/1000000000000 : ℝ) (124012906487/125000000000 : ℝ) (496051625949/500000000000 : ℝ) (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ) (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33319/262144 : ℝ)) 3 (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ) (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ) (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ) (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33319/262144 : ℝ)) 4 (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ) (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ) (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ) (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33319/262144 : ℝ)) 5 (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ) (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ) (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ) (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33319/262144 : ℝ)) 6 (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ) (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ) (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ) (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33319/262144 : ℝ)) 7 (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ) (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ) (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ) (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33319/262144 : ℝ))) (176850047011/1000000000000 : ℝ) (88425023509/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33319/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176850047011/1000000000000 : ℝ) (88425023509/500000000000 : ℝ) (117685004701/200000000000 : ℝ) (588425023509/1000000000000 : ℝ) (2628346431/6250000000 : ℝ) (420535428969/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33319/262144 : ℝ))) 1 (117685004701/200000000000 : ℝ) (588425023509/1000000000000 : ℝ) (2628346431/6250000000 : ℝ) (420535428969/1000000000000 : ℝ) (63060028279/125000000000 : ℝ) (504480226239/1000000000000 : ℝ) (497447052127/1000000000000 : ℝ) (99489410427/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33319/262144 : ℝ))) 2 (63060028279/125000000000 : ℝ) (504480226239/1000000000000 : ℝ) (497447052127/1000000000000 : ℝ) (99489410427/200000000000 : ℝ) (500963639179/1000000000000 : ℝ) (500963639187/1000000000000 : ℝ) (50095129643/100000000000 : ℝ) (500951296439/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33319/262144 : ℝ))) 3 (500963639179/1000000000000 : ℝ) (500963639187/1000000000000 : ℝ) (50095129643/100000000000 : ℝ) (500951296439/1000000000000 : ℝ) (125239366951/250000000000 : ℝ) (500957467813/1000000000000 : ℝ) (250478733883/500000000000 : ℝ) (20038298711/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33319/262144 : ℝ))) 4 (125239366951/250000000000 : ℝ) (500957467813/1000000000000 : ℝ) (250478733883/500000000000 : ℝ) (20038298711/40000000000 : ℝ) (100191493557/200000000000 : ℝ) (250478733897/500000000000 : ℝ) (62619683473/125000000000 : ℝ) (250478733897/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33319/262144 : ℝ))) 5 (100191493557/200000000000 : ℝ) (250478733897/500000000000 : ℝ) (62619683473/125000000000 : ℝ) (250478733897/500000000000 : ℝ) (62619683473/125000000000 : ℝ) (250478733897/500000000000 : ℝ) (62619683473/125000000000 : ℝ) (250478733897/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33319/262144 : ℝ))) 6 (62619683473/125000000000 : ℝ) (250478733897/500000000000 : ℝ) (62619683473/125000000000 : ℝ) (250478733897/500000000000 : ℝ) (62619683473/125000000000 : ℝ) (250478733897/500000000000 : ℝ) (62619683473/125000000000 : ℝ) (250478733897/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33319/262144 : ℝ))) 7 (62619683473/125000000000 : ℝ) (250478733897/500000000000 : ℝ) (62619683473/125000000000 : ℝ) (250478733897/500000000000 : ℝ) (62619683473/125000000000 : ℝ) (250478733897/500000000000 : ℝ) (62619683473/125000000000 : ℝ) (250478733897/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33319/262144 : ℝ)) hmem 8 (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ) (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33319/262144 : ℝ))) hcmem 8 (62619683473/125000000000 : ℝ) (250478733897/500000000000 : ℝ) (62619683473/125000000000 : ℝ) (250478733897/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33319/262144 : ℝ)) (992103251957/1000000000000 : ℝ) (24802581299/25000000000 : ℝ) (62619683473/125000000000 : ℝ) (250478733897/500000000000 : ℝ) (396582789503/500000000000 : ℝ) (396582789513/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0565_exp_lower
  have heNumeric : (513725815783/250000000000 : ℝ)/4 ≤ Real.exp (-85256395287203/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725815783/250000000000 : ℝ)/4 ≤ Real.exp ((66637/524288 : ℝ)-(396582789513/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66637/524288 : ℝ) (33319/262144 : ℝ) (396582789513/500000000000 : ℝ) (513725815783/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0566; no trusted numerical premise.
theorem cover8_leaf0566_exp_radius : (998015973825497151/1000000000000000000 : ℝ) ≤ Real.exp ((-66639/4194304 : ℝ)/8) ∧ Real.exp ((-66639/4194304 : ℝ)/8) ≤ (15593999591023393/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66639/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0566_exp_lower : (460056771965652761/500000000000000000 : ℝ) ≤ Real.exp ((-8525639601941/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525639601941/12800000000000 : ℝ)/8) ≤ (920113543931305523/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525639601941/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0566_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903251377/1000000000000 : ℝ) ≤ 4*Real.exp (33319/262144 : ℝ)*Real.exp (-mu (radius 8 (66639/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903251377/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66639/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0566_exp_radius
  have hrNumeric : (984237572411/1000000000000 : ℝ) ≤ Real.exp (-66639/4194304 : ℝ) ∧ Real.exp (-66639/4194304 : ℝ) ≤ (246059393103/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984237572411/1000000000000 : ℝ) ≤ (radius 8 (66639/524288 : ℝ)) ∧ (radius 8 (66639/524288 : ℝ)) ≤ (246059393103/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66639/524288 : ℝ)) (984237572411/1000000000000 : ℝ) (246059393103/250000000000 : ℝ) (22106419123/125000000000 : ℝ) (176851352991/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66639/524288 : ℝ)) (984237572411/1000000000000 : ℝ) (246059393103/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66639/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984237572411/1000000000000 : ℝ) (246059393103/250000000000 : ℝ) (198423757241/200000000000 : ℝ) (496059393103/500000000000 : ℝ) (248021870559/250000000000 : ℝ) (496043741119/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66639/524288 : ℝ)) 1 (198423757241/200000000000 : ℝ) (496059393103/500000000000 : ℝ) (248021870559/250000000000 : ℝ) (496043741119/500000000000 : ℝ) (49605156711/50000000000 : ℝ) (496051567111/500000000000 : ℝ) (992103134097/1000000000000 : ℝ) (992103134099/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66639/524288 : ℝ)) 2 (49605156711/50000000000 : ℝ) (496051567111/500000000000 : ℝ) (992103134097/1000000000000 : ℝ) (992103134099/1000000000000 : ℝ) (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ) (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66639/524288 : ℝ)) 3 (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ) (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ) (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ) (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66639/524288 : ℝ)) 4 (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ) (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ) (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ) (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66639/524288 : ℝ)) 5 (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ) (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ) (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ) (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66639/524288 : ℝ)) 6 (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ) (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ) (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ) (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66639/524288 : ℝ)) 7 (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ) (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ) (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ) (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66639/524288 : ℝ))) (22106419123/125000000000 : ℝ) (176851352991/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66639/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22106419123/125000000000 : ℝ) (176851352991/1000000000000 : ℝ) (147106419123/250000000000 : ℝ) (36776604781/62500000000 : ℝ) (420536981707/1000000000000 : ℝ) (420536981717/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66639/524288 : ℝ))) 1 (147106419123/250000000000 : ℝ) (36776604781/62500000000 : ℝ) (420536981707/1000000000000 : ℝ) (420536981717/1000000000000 : ℝ) (504481329099/1000000000000 : ℝ) (504481329107/1000000000000 : ℝ) (62181030813/125000000000 : ℝ) (497448246513/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66639/524288 : ℝ))) 2 (504481329099/1000000000000 : ℝ) (504481329107/1000000000000 : ℝ) (62181030813/125000000000 : ℝ) (497448246513/1000000000000 : ℝ) (500964787801/1000000000000 : ℝ) (50096478781/100000000000 : ℝ) (250476222701/500000000000 : ℝ) (500952445411/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66639/524288 : ℝ))) 3 (500964787801/1000000000000 : ℝ) (50096478781/100000000000 : ℝ) (250476222701/500000000000 : ℝ) (500952445411/1000000000000 : ℝ) (500958616601/1000000000000 : ℝ) (500958616611/1000000000000 : ℝ) (500958616563/1000000000000 : ℝ) (500958616573/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66639/524288 : ℝ))) 4 (500958616601/1000000000000 : ℝ) (500958616611/1000000000000 : ℝ) (500958616563/1000000000000 : ℝ) (500958616573/1000000000000 : ℝ) (250479308291/500000000000 : ℝ) (31309913537/62500000000 : ℝ) (500958616581/1000000000000 : ℝ) (31309913537/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66639/524288 : ℝ))) 5 (250479308291/500000000000 : ℝ) (31309913537/62500000000 : ℝ) (500958616581/1000000000000 : ℝ) (31309913537/62500000000 : ℝ) (500958616581/1000000000000 : ℝ) (31309913537/62500000000 : ℝ) (500958616581/1000000000000 : ℝ) (31309913537/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66639/524288 : ℝ))) 6 (500958616581/1000000000000 : ℝ) (31309913537/62500000000 : ℝ) (500958616581/1000000000000 : ℝ) (31309913537/62500000000 : ℝ) (500958616581/1000000000000 : ℝ) (31309913537/62500000000 : ℝ) (500958616581/1000000000000 : ℝ) (31309913537/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66639/524288 : ℝ))) 7 (500958616581/1000000000000 : ℝ) (31309913537/62500000000 : ℝ) (500958616581/1000000000000 : ℝ) (31309913537/62500000000 : ℝ) (500958616581/1000000000000 : ℝ) (31309913537/62500000000 : ℝ) (500958616581/1000000000000 : ℝ) (31309913537/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66639/524288 : ℝ)) hmem 8 (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ) (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66639/524288 : ℝ))) hcmem 8 (500958616581/1000000000000 : ℝ) (31309913537/62500000000 : ℝ) (500958616581/1000000000000 : ℝ) (31309913537/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66639/524288 : ℝ)) (496051567079/500000000000 : ℝ) (992103134161/1000000000000 : ℝ) (500958616581/1000000000000 : ℝ) (31309913537/62500000000 : ℝ) (396583746037/500000000000 : ℝ) (158633498419/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0566_exp_lower
  have heNumeric : (2054903251377/1000000000000 : ℝ)/4 ≤ Real.exp (-8525639601941/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903251377/1000000000000 : ℝ)/4 ≤ Real.exp ((33319/262144 : ℝ)-(158633498419/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33319/262144 : ℝ) (66639/524288 : ℝ) (158633498419/200000000000 : ℝ) (2054903251377/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0567; no trusted numerical premise.
theorem cover8_leaf0567_exp_radius : (499007972041151897/500000000000000000 : ℝ) ≤ Real.exp ((-4165/262144 : ℝ)/8) ∧ Real.exp ((-4165/262144 : ℝ)/8) ≤ (199603188816460759/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4165/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0567_exp_lower : (460056771638473773/500000000000000000 : ℝ) ≤ Real.exp ((-85256396747649/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256396747649/128000000000000 : ℝ)/8) ≤ (920113543276947547/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256396747649/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0567_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451619843/500000000000 : ℝ) ≤ 4*Real.exp (66639/524288 : ℝ)*Real.exp (-mu (radius 8 (4165/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451619843/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4165/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0567_exp_radius
  have hrNumeric : (984237337751/1000000000000 : ℝ) ≤ Real.exp (-4165/262144 : ℝ) ∧ Real.exp (-4165/262144 : ℝ) ≤ (123029667219/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984237337751/1000000000000 : ℝ) ≤ (radius 8 (4165/32768 : ℝ)) ∧ (radius 8 (4165/32768 : ℝ)) ≤ (123029667219/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4165/32768 : ℝ)) (984237337751/1000000000000 : ℝ) (123029667219/125000000000 : ℝ) (88426329471/500000000000 : ℝ) (44213164737/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4165/32768 : ℝ)) (984237337751/1000000000000 : ℝ) (123029667219/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4165/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984237337751/1000000000000 : ℝ) (123029667219/125000000000 : ℝ) (7936949351/8000000000 : ℝ) (248029667219/250000000000 : ℝ) (992087363971/1000000000000 : ℝ) (248021840993/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4165/32768 : ℝ)) 1 (7936949351/8000000000 : ℝ) (248029667219/250000000000 : ℝ) (992087363971/1000000000000 : ℝ) (248021840993/250000000000 : ℝ) (992103016423/1000000000000 : ℝ) (124012877053/125000000000 : ℝ) (992103016299/1000000000000 : ℝ) (992103016301/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4165/32768 : ℝ)) 2 (992103016423/1000000000000 : ℝ) (124012877053/125000000000 : ℝ) (992103016299/1000000000000 : ℝ) (992103016301/1000000000000 : ℝ) (992103016361/1000000000000 : ℝ) (992103016363/1000000000000 : ℝ) (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4165/32768 : ℝ)) 3 (992103016361/1000000000000 : ℝ) (992103016363/1000000000000 : ℝ) (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ) (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ) (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4165/32768 : ℝ)) 4 (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ) (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ) (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ) (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4165/32768 : ℝ)) 5 (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ) (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ) (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ) (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4165/32768 : ℝ)) 6 (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ) (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ) (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ) (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4165/32768 : ℝ)) 7 (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ) (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ) (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ) (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4165/32768 : ℝ))) (88426329471/500000000000 : ℝ) (44213164737/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4165/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88426329471/500000000000 : ℝ) (44213164737/250000000000 : ℝ) (588426329471/1000000000000 : ℝ) (294213164737/500000000000 : ℝ) (420538534431/1000000000000 : ℝ) (420538534439/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4165/32768 : ℝ))) 1 (588426329471/1000000000000 : ℝ) (294213164737/500000000000 : ℝ) (420538534431/1000000000000 : ℝ) (420538534439/1000000000000 : ℝ) (504482431951/1000000000000 : ℝ) (504482431957/1000000000000 : ℝ) (15545295027/31250000000 : ℝ) (497449440871/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4165/32768 : ℝ))) 2 (504482431951/1000000000000 : ℝ) (504482431957/1000000000000 : ℝ) (15545295027/31250000000 : ℝ) (497449440871/1000000000000 : ℝ) (500965936407/1000000000000 : ℝ) (250482968207/500000000000 : ℝ) (500953594357/1000000000000 : ℝ) (100190718873/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4165/32768 : ℝ))) 3 (500965936407/1000000000000 : ℝ) (250482968207/500000000000 : ℝ) (500953594357/1000000000000 : ℝ) (100190718873/200000000000 : ℝ) (250479882691/500000000000 : ℝ) (50095976539/100000000000 : ℝ) (500959765343/1000000000000 : ℝ) (62619970669/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4165/32768 : ℝ))) 4 (250479882691/500000000000 : ℝ) (50095976539/100000000000 : ℝ) (500959765343/1000000000000 : ℝ) (62619970669/125000000000 : ℝ) (250479882681/500000000000 : ℝ) (500959765371/1000000000000 : ℝ) (250479882681/500000000000 : ℝ) (500959765371/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4165/32768 : ℝ))) 5 (250479882681/500000000000 : ℝ) (500959765371/1000000000000 : ℝ) (250479882681/500000000000 : ℝ) (500959765371/1000000000000 : ℝ) (250479882681/500000000000 : ℝ) (500959765371/1000000000000 : ℝ) (250479882681/500000000000 : ℝ) (500959765371/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4165/32768 : ℝ))) 6 (250479882681/500000000000 : ℝ) (500959765371/1000000000000 : ℝ) (250479882681/500000000000 : ℝ) (500959765371/1000000000000 : ℝ) (250479882681/500000000000 : ℝ) (500959765371/1000000000000 : ℝ) (250479882681/500000000000 : ℝ) (500959765371/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4165/32768 : ℝ))) 7 (250479882681/500000000000 : ℝ) (500959765371/1000000000000 : ℝ) (250479882681/500000000000 : ℝ) (500959765371/1000000000000 : ℝ) (250479882681/500000000000 : ℝ) (500959765371/1000000000000 : ℝ) (250479882681/500000000000 : ℝ) (500959765371/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4165/32768 : ℝ)) hmem 8 (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ) (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4165/32768 : ℝ))) hcmem 8 (250479882681/500000000000 : ℝ) (500959765371/1000000000000 : ℝ) (250479882681/500000000000 : ℝ) (500959765371/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4165/32768 : ℝ)) (24802575409/25000000000 : ℝ) (992103016363/1000000000000 : ℝ) (250479882681/500000000000 : ℝ) (500959765371/1000000000000 : ℝ) (198292351279/250000000000 : ℝ) (793169405133/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0567_exp_lower
  have heNumeric : (1027451619843/500000000000 : ℝ)/4 ≤ Real.exp (-85256396747649/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451619843/500000000000 : ℝ)/4 ≤ Real.exp ((66639/524288 : ℝ)-(793169405133/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66639/524288 : ℝ) (4165/32768 : ℝ) (793169405133/1000000000000 : ℝ) (1027451619843/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0568; no trusted numerical premise.
theorem cover8_leaf0568_exp_radius : (249503978584777831/250000000000000000 : ℝ) ≤ Real.exp ((-66641/4194304 : ℝ)/8) ∧ Real.exp ((-66641/4194304 : ℝ)/8) ≤ (39920636573564453/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66641/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0568_exp_lower : (920113542623739713/1000000000000000000 : ℝ) ≤ Real.exp ((-5328524842163/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328524842163/8000000000000 : ℝ)/8) ≤ (460056771311869857/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328524842163/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0568_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980645603/200000000000 : ℝ) ≤ 4*Real.exp (4165/32768 : ℝ)*Real.exp (-mu (radius 8 (66641/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980645603/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66641/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0568_exp_radius
  have hrNumeric : (98423710309/100000000000 : ℝ) ≤ Real.exp (-66641/4194304 : ℝ) ∧ Real.exp (-66641/4194304 : ℝ) ≤ (984237103091/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98423710309/100000000000 : ℝ) ≤ (radius 8 (66641/524288 : ℝ)) ∧ (radius 8 (66641/524288 : ℝ)) ≤ (984237103091/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66641/524288 : ℝ)) (98423710309/100000000000 : ℝ) (984237103091/1000000000000 : ℝ) (88426982447/500000000000 : ℝ) (176853964901/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66641/524288 : ℝ)) (98423710309/100000000000 : ℝ) (984237103091/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66641/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98423710309/100000000000 : ℝ) (984237103091/1000000000000 : ℝ) (198423710309/200000000000 : ℝ) (496059275773/500000000000 : ℝ) (124010905713/125000000000 : ℝ) (496043622853/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66641/524288 : ℝ)) 1 (198423710309/200000000000 : ℝ) (496059275773/500000000000 : ℝ) (124010905713/125000000000 : ℝ) (496043622853/500000000000 : ℝ) (15501607791/15625000000 : ℝ) (496051449313/500000000000 : ℝ) (992102898501/1000000000000 : ℝ) (992102898503/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66641/524288 : ℝ)) 2 (15501607791/15625000000 : ℝ) (496051449313/500000000000 : ℝ) (992102898501/1000000000000 : ℝ) (992102898503/1000000000000 : ℝ) (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ) (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66641/524288 : ℝ)) 3 (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ) (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ) (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ) (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66641/524288 : ℝ)) 4 (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ) (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ) (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ) (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66641/524288 : ℝ)) 5 (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ) (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ) (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ) (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66641/524288 : ℝ)) 6 (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ) (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ) (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ) (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66641/524288 : ℝ)) 7 (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ) (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ) (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ) (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66641/524288 : ℝ))) (88426982447/500000000000 : ℝ) (176853964901/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66641/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88426982447/500000000000 : ℝ) (176853964901/1000000000000 : ℝ) (588426982447/1000000000000 : ℝ) (588426982451/1000000000000 : ℝ) (210270043571/500000000000 : ℝ) (26283755447/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66641/524288 : ℝ))) 1 (588426982447/1000000000000 : ℝ) (588426982451/1000000000000 : ℝ) (210270043571/500000000000 : ℝ) (26283755447/62500000000 : ℝ) (252241767397/500000000000 : ℝ) (252241767401/500000000000 : ℝ) (248725317607/500000000000 : ℝ) (248725317611/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66641/524288 : ℝ))) 2 (252241767397/500000000000 : ℝ) (252241767401/500000000000 : ℝ) (248725317607/500000000000 : ℝ) (248725317611/500000000000 : ℝ) (125241771251/250000000000 : ℝ) (125241771253/250000000000 : ℝ) (500954743303/1000000000000 : ℝ) (31309671457/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66641/524288 : ℝ))) 3 (125241771251/250000000000 : ℝ) (125241771253/250000000000 : ℝ) (500954743303/1000000000000 : ℝ) (31309671457/62500000000 : ℝ) (500960914153/1000000000000 : ℝ) (250480457081/500000000000 : ℝ) (100192182823/200000000000 : ℝ) (125240228531/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66641/524288 : ℝ))) 4 (500960914153/1000000000000 : ℝ) (250480457081/500000000000 : ℝ) (100192182823/200000000000 : ℝ) (125240228531/250000000000 : ℝ) (250480457067/500000000000 : ℝ) (500960914143/1000000000000 : ℝ) (500960914133/1000000000000 : ℝ) (500960914143/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66641/524288 : ℝ))) 5 (250480457067/500000000000 : ℝ) (500960914143/1000000000000 : ℝ) (500960914133/1000000000000 : ℝ) (500960914143/1000000000000 : ℝ) (500960914133/1000000000000 : ℝ) (500960914143/1000000000000 : ℝ) (500960914133/1000000000000 : ℝ) (500960914143/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66641/524288 : ℝ))) 6 (500960914133/1000000000000 : ℝ) (500960914143/1000000000000 : ℝ) (500960914133/1000000000000 : ℝ) (500960914143/1000000000000 : ℝ) (500960914133/1000000000000 : ℝ) (500960914143/1000000000000 : ℝ) (500960914133/1000000000000 : ℝ) (500960914143/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66641/524288 : ℝ))) 7 (500960914133/1000000000000 : ℝ) (500960914143/1000000000000 : ℝ) (500960914133/1000000000000 : ℝ) (500960914143/1000000000000 : ℝ) (500960914133/1000000000000 : ℝ) (500960914143/1000000000000 : ℝ) (500960914133/1000000000000 : ℝ) (500960914143/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66641/524288 : ℝ)) hmem 8 (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ) (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66641/524288 : ℝ))) hcmem 8 (500960914133/1000000000000 : ℝ) (500960914143/1000000000000 : ℝ) (500960914133/1000000000000 : ℝ) (500960914143/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66641/524288 : ℝ)) (496051449281/500000000000 : ℝ) (198420579713/200000000000 : ℝ) (500960914133/1000000000000 : ℝ) (500960914143/1000000000000 : ℝ) (396585659071/500000000000 : ℝ) (793171318161/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0568_exp_lower
  have heNumeric : (410980645603/200000000000 : ℝ)/4 ≤ Real.exp (-5328524842163/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980645603/200000000000 : ℝ)/4 ≤ Real.exp ((4165/32768 : ℝ)-(793171318161/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4165/32768 : ℝ) (66641/524288 : ℝ) (793171318161/1000000000000 : ℝ) (410980645603/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0569; no trusted numerical premise.
theorem cover8_leaf0569_exp_radius : (49900794229795987/50000000000000000 : ℝ) ≤ Real.exp ((-33321/2097152 : ℝ)/8) ∧ Real.exp ((-33321/2097152 : ℝ)/8) ≤ (998015884595919741/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33321/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0569_exp_lower : (920113541973522249/1000000000000000000 : ℝ) ≤ Real.exp ((-85256398198239/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256398198239/128000000000000 : ℝ)/8) ≤ (3680454167894089/4000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256398198239/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0569_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451608199/500000000000 : ℝ) ≤ 4*Real.exp (66641/524288 : ℝ)*Real.exp (-mu (radius 8 (33321/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451608199/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33321/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0569_exp_radius
  have hrNumeric : (98423686843/100000000000 : ℝ) ≤ Real.exp (-33321/2097152 : ℝ) ∧ Real.exp (-33321/2097152 : ℝ) ≤ (984236868431/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98423686843/100000000000 : ℝ) ≤ (radius 8 (33321/262144 : ℝ)) ∧ (radius 8 (33321/262144 : ℝ)) ≤ (984236868431/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33321/262144 : ℝ)) (98423686843/100000000000 : ℝ) (984236868431/1000000000000 : ℝ) (11053454427/62500000000 : ℝ) (88427635419/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33321/262144 : ℝ)) (98423686843/100000000000 : ℝ) (984236868431/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33321/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98423686843/100000000000 : ℝ) (984236868431/1000000000000 : ℝ) (198423686843/200000000000 : ℝ) (124014804277/125000000000 : ℝ) (496043563719/500000000000 : ℝ) (12401089093/12500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33321/262144 : ℝ)) 1 (198423686843/200000000000 : ℝ) (124014804277/125000000000 : ℝ) (496043563719/500000000000 : ℝ) (12401089093/12500000000 : ℝ) (496051390413/500000000000 : ℝ) (248025695207/250000000000 : ℝ) (992102780703/1000000000000 : ℝ) (198420556141/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33321/262144 : ℝ)) 2 (496051390413/500000000000 : ℝ) (248025695207/250000000000 : ℝ) (992102780703/1000000000000 : ℝ) (198420556141/200000000000 : ℝ) (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ) (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33321/262144 : ℝ)) 3 (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ) (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ) (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ) (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33321/262144 : ℝ)) 4 (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ) (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ) (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ) (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33321/262144 : ℝ)) 5 (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ) (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ) (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ) (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33321/262144 : ℝ)) 6 (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ) (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ) (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ) (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33321/262144 : ℝ)) 7 (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ) (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ) (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ) (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33321/262144 : ℝ))) (11053454427/62500000000 : ℝ) (88427635419/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33321/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11053454427/62500000000 : ℝ) (88427635419/500000000000 : ℝ) (73553454427/125000000000 : ℝ) (588427635419/1000000000000 : ℝ) (420541639831/1000000000000 : ℝ) (420541639839/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33321/262144 : ℝ))) 1 (73553454427/125000000000 : ℝ) (588427635419/1000000000000 : ℝ) (420541639831/1000000000000 : ℝ) (420541639839/1000000000000 : ℝ) (504484637623/1000000000000 : ℝ) (504484637629/1000000000000 : ℝ) (497451829547/1000000000000 : ℝ) (248725914777/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33321/262144 : ℝ))) 2 (504484637623/1000000000000 : ℝ) (504484637629/1000000000000 : ℝ) (497451829547/1000000000000 : ℝ) (248725914777/500000000000 : ℝ) (100193646717/200000000000 : ℝ) (62621029199/125000000000 : ℝ) (500955892233/1000000000000 : ℝ) (500955892241/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33321/262144 : ℝ))) 3 (100193646717/200000000000 : ℝ) (62621029199/125000000000 : ℝ) (500955892233/1000000000000 : ℝ) (500955892241/1000000000000 : ℝ) (500962062909/1000000000000 : ℝ) (500962062917/1000000000000 : ℝ) (50096206287/100000000000 : ℝ) (500962062879/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33321/262144 : ℝ))) 4 (500962062909/1000000000000 : ℝ) (500962062917/1000000000000 : ℝ) (50096206287/100000000000 : ℝ) (500962062879/1000000000000 : ℝ) (500962062889/1000000000000 : ℝ) (250481031449/500000000000 : ℝ) (500962062889/1000000000000 : ℝ) (250481031449/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33321/262144 : ℝ))) 5 (500962062889/1000000000000 : ℝ) (250481031449/500000000000 : ℝ) (500962062889/1000000000000 : ℝ) (250481031449/500000000000 : ℝ) (500962062889/1000000000000 : ℝ) (250481031449/500000000000 : ℝ) (500962062889/1000000000000 : ℝ) (250481031449/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33321/262144 : ℝ))) 6 (500962062889/1000000000000 : ℝ) (250481031449/500000000000 : ℝ) (500962062889/1000000000000 : ℝ) (250481031449/500000000000 : ℝ) (500962062889/1000000000000 : ℝ) (250481031449/500000000000 : ℝ) (500962062889/1000000000000 : ℝ) (250481031449/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33321/262144 : ℝ))) 7 (500962062889/1000000000000 : ℝ) (250481031449/500000000000 : ℝ) (500962062889/1000000000000 : ℝ) (250481031449/500000000000 : ℝ) (500962062889/1000000000000 : ℝ) (250481031449/500000000000 : ℝ) (500962062889/1000000000000 : ℝ) (250481031449/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33321/262144 : ℝ)) hmem 8 (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ) (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33321/262144 : ℝ))) hcmem 8 (500962062889/1000000000000 : ℝ) (250481031449/500000000000 : ℝ) (500962062889/1000000000000 : ℝ) (250481031449/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33321/262144 : ℝ)) (248025695191/250000000000 : ℝ) (992102780767/1000000000000 : ℝ) (500962062889/1000000000000 : ℝ) (250481031449/500000000000 : ℝ) (158634646229/200000000000 : ℝ) (793173231163/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0569_exp_lower
  have heNumeric : (1027451608199/500000000000 : ℝ)/4 ≤ Real.exp (-85256398198239/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451608199/500000000000 : ℝ)/4 ≤ Real.exp ((66641/524288 : ℝ)-(793173231163/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66641/524288 : ℝ) (33321/262144 : ℝ) (793173231163/1000000000000 : ℝ) (1027451608199/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0570; no trusted numerical premise.
theorem cover8_leaf0570_exp_radius : (499007927426364521/500000000000000000 : ℝ) ≤ Real.exp ((-66643/4194304 : ℝ)/8) ∧ Real.exp ((-66643/4194304 : ℝ)/8) ≤ (998015854852729043/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66643/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0570_exp_lower : (115014192665686257/125000000000000000 : ℝ) ≤ Real.exp ((-42628199459719/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628199459719/64000000000000 : ℝ)/8) ≤ (920113541325490057/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628199459719/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0570_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745160241/50000000000 : ℝ) ≤ 4*Real.exp (33321/262144 : ℝ)*Real.exp (-mu (radius 8 (66643/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (102745160241/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66643/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0570_exp_radius
  have hrNumeric : (98423663377/100000000000 : ℝ) ≤ Real.exp (-66643/4194304 : ℝ) ∧ Real.exp (-66643/4194304 : ℝ) ≤ (984236633771/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98423663377/100000000000 : ℝ) ≤ (radius 8 (66643/524288 : ℝ)) ∧ (radius 8 (66643/524288 : ℝ)) ≤ (984236633771/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66643/524288 : ℝ)) (98423663377/100000000000 : ℝ) (984236633771/1000000000000 : ℝ) (176856576759/1000000000000 : ℝ) (88428288383/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66643/524288 : ℝ)) (98423663377/100000000000 : ℝ) (984236633771/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66643/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98423663377/100000000000 : ℝ) (984236633771/1000000000000 : ℝ) (198423663377/200000000000 : ℝ) (496059158443/500000000000 : ℝ) (992087009173/1000000000000 : ℝ) (496043504587/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66643/524288 : ℝ)) 1 (198423663377/200000000000 : ℝ) (496059158443/500000000000 : ℝ) (992087009173/1000000000000 : ℝ) (496043504587/500000000000 : ℝ) (992102663029/1000000000000 : ℝ) (99210266303/100000000000 : ℝ) (198420532581/200000000000 : ℝ) (992102662907/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66643/524288 : ℝ)) 2 (992102663029/1000000000000 : ℝ) (99210266303/100000000000 : ℝ) (198420532581/200000000000 : ℝ) (992102662907/1000000000000 : ℝ) (992102662967/1000000000000 : ℝ) (992102662969/1000000000000 : ℝ) (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66643/524288 : ℝ)) 3 (992102662967/1000000000000 : ℝ) (992102662969/1000000000000 : ℝ) (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ) (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ) (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66643/524288 : ℝ)) 4 (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ) (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ) (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ) (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66643/524288 : ℝ)) 5 (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ) (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ) (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ) (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66643/524288 : ℝ)) 6 (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ) (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ) (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ) (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66643/524288 : ℝ)) 7 (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ) (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ) (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ) (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66643/524288 : ℝ))) (176856576759/1000000000000 : ℝ) (88428288383/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66643/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176856576759/1000000000000 : ℝ) (88428288383/500000000000 : ℝ) (588428288379/1000000000000 : ℝ) (588428288383/1000000000000 : ℝ) (420543192501/1000000000000 : ℝ) (42054319251/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66643/524288 : ℝ))) 1 (588428288379/1000000000000 : ℝ) (588428288383/1000000000000 : ℝ) (420543192501/1000000000000 : ℝ) (42054319251/100000000000 : ℝ) (12612143511/25000000000 : ℝ) (504485740447/1000000000000 : ℝ) (99490604773/200000000000 : ℝ) (497453023873/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66643/524288 : ℝ))) 2 (12612143511/25000000000 : ℝ) (504485740447/1000000000000 : ℝ) (99490604773/200000000000 : ℝ) (497453023873/1000000000000 : ℝ) (62621172769/125000000000 : ℝ) (6262117277/12500000000 : ℝ) (10019140823/20000000000 : ℝ) (500957041159/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66643/524288 : ℝ))) 3 (62621172769/125000000000 : ℝ) (6262117277/12500000000 : ℝ) (10019140823/20000000000 : ℝ) (500957041159/1000000000000 : ℝ) (500963211651/1000000000000 : ℝ) (25048160583/50000000000 : ℝ) (125240802903/250000000000 : ℝ) (250481605811/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66643/524288 : ℝ))) 4 (500963211651/1000000000000 : ℝ) (25048160583/50000000000 : ℝ) (125240802903/250000000000 : ℝ) (250481605811/500000000000 : ℝ) (500963211631/1000000000000 : ℝ) (500963211641/1000000000000 : ℝ) (500963211631/1000000000000 : ℝ) (500963211641/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66643/524288 : ℝ))) 5 (500963211631/1000000000000 : ℝ) (500963211641/1000000000000 : ℝ) (500963211631/1000000000000 : ℝ) (500963211641/1000000000000 : ℝ) (500963211631/1000000000000 : ℝ) (500963211641/1000000000000 : ℝ) (500963211631/1000000000000 : ℝ) (500963211641/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66643/524288 : ℝ))) 6 (500963211631/1000000000000 : ℝ) (500963211641/1000000000000 : ℝ) (500963211631/1000000000000 : ℝ) (500963211641/1000000000000 : ℝ) (500963211631/1000000000000 : ℝ) (500963211641/1000000000000 : ℝ) (500963211631/1000000000000 : ℝ) (500963211641/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66643/524288 : ℝ))) 7 (500963211631/1000000000000 : ℝ) (500963211641/1000000000000 : ℝ) (500963211631/1000000000000 : ℝ) (500963211641/1000000000000 : ℝ) (500963211631/1000000000000 : ℝ) (500963211641/1000000000000 : ℝ) (500963211631/1000000000000 : ℝ) (500963211641/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66643/524288 : ℝ)) hmem 8 (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ) (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66643/524288 : ℝ))) hcmem 8 (500963211631/1000000000000 : ℝ) (500963211641/1000000000000 : ℝ) (500963211631/1000000000000 : ℝ) (500963211641/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66643/524288 : ℝ)) (496051331483/500000000000 : ℝ) (992102662969/1000000000000 : ℝ) (500963211631/1000000000000 : ℝ) (500963211641/1000000000000 : ℝ) (793175144127/1000000000000 : ℝ) (396587572073/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0570_exp_lower
  have heNumeric : (102745160241/50000000000 : ℝ)/4 ≤ Real.exp (-42628199459719/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745160241/50000000000 : ℝ)/4 ≤ Real.exp ((33321/262144 : ℝ)-(396587572073/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33321/262144 : ℝ) (66643/524288 : ℝ) (396587572073/500000000000 : ℝ) (102745160241/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0571; no trusted numerical premise.
theorem cover8_leaf0571_exp_radius : (998015825109539231/1000000000000000000 : ℝ) ≤ Real.exp ((-16661/1048576 : ℝ)/8) ∧ Real.exp ((-16661/1048576 : ℝ)/8) ≤ (31187994534673101/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16661/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0571_exp_lower : (920113540678838033/1000000000000000000 : ℝ) ≤ Real.exp ((-85256399639101/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256399639101/128000000000000 : ℝ)/8) ≤ (460056770339419017/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256399639101/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0571_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903193267/1000000000000 : ℝ) ≤ 4*Real.exp (66643/524288 : ℝ)*Real.exp (-mu (radius 8 (16661/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903193267/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16661/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0571_exp_radius
  have hrNumeric : (984236399109/1000000000000 : ℝ) ≤ Real.exp (-16661/1048576 : ℝ) ∧ Real.exp (-16661/1048576 : ℝ) ≤ (98423639911/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984236399109/1000000000000 : ℝ) ≤ (radius 8 (16661/131072 : ℝ)) ∧ (radius 8 (16661/131072 : ℝ)) ≤ (98423639911/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16661/131072 : ℝ)) (984236399109/1000000000000 : ℝ) (98423639911/100000000000 : ℝ) (88428941341/500000000000 : ℝ) (176857882689/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16661/131072 : ℝ)) (984236399109/1000000000000 : ℝ) (98423639911/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16661/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984236399109/1000000000000 : ℝ) (98423639911/100000000000 : ℝ) (496059099777/500000000000 : ℝ) (198423639911/200000000000 : ℝ) (496043445453/500000000000 : ℝ) (248021722727/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16661/131072 : ℝ)) 1 (496059099777/500000000000 : ℝ) (198423639911/200000000000 : ℝ) (496043445453/500000000000 : ℝ) (248021722727/250000000000 : ℝ) (99210254523/100000000000 : ℝ) (62006409077/62500000000 : ℝ) (496051272553/500000000000 : ℝ) (248025636277/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16661/131072 : ℝ)) 2 (99210254523/100000000000 : ℝ) (62006409077/62500000000 : ℝ) (496051272553/500000000000 : ℝ) (248025636277/250000000000 : ℝ) (62006409073/62500000000 : ℝ) (99210254517/100000000000 : ℝ) (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16661/131072 : ℝ)) 3 (62006409073/62500000000 : ℝ) (99210254517/100000000000 : ℝ) (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ) (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ) (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16661/131072 : ℝ)) 4 (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ) (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ) (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ) (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16661/131072 : ℝ)) 5 (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ) (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ) (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ) (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16661/131072 : ℝ)) 6 (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ) (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ) (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ) (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16661/131072 : ℝ)) 7 (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ) (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ) (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ) (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16661/131072 : ℝ))) (88428941341/500000000000 : ℝ) (176857882689/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16661/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88428941341/500000000000 : ℝ) (176857882689/1000000000000 : ℝ) (588428941341/1000000000000 : ℝ) (117685788269/200000000000 : ℝ) (10513618629/25000000000 : ℝ) (420544745169/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16661/131072 : ℝ))) 1 (588428941341/1000000000000 : ℝ) (117685788269/200000000000 : ℝ) (10513618629/25000000000 : ℝ) (420544745169/1000000000000 : ℝ) (2017947373/4000000000 : ℝ) (504486843257/1000000000000 : ℝ) (19898168727/40000000000 : ℝ) (497454218183/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16661/131072 : ℝ))) 2 (2017947373/4000000000 : ℝ) (504486843257/1000000000000 : ℝ) (19898168727/40000000000 : ℝ) (497454218183/1000000000000 : ℝ) (62621316339/125000000000 : ℝ) (3131065817/6250000000 : ℝ) (25047909503/50000000000 : ℝ) (125239547517/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16661/131072 : ℝ))) 3 (62621316339/125000000000 : ℝ) (3131065817/6250000000 : ℝ) (25047909503/50000000000 : ℝ) (125239547517/250000000000 : ℝ) (250482180193/500000000000 : ℝ) (250482180197/500000000000 : ℝ) (125241090087/250000000000 : ℝ) (500964360357/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16661/131072 : ℝ))) 4 (250482180193/500000000000 : ℝ) (250482180197/500000000000 : ℝ) (125241090087/250000000000 : ℝ) (500964360357/1000000000000 : ℝ) (500964360367/1000000000000 : ℝ) (62620545047/125000000000 : ℝ) (250482180183/500000000000 : ℝ) (62620545047/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16661/131072 : ℝ))) 5 (500964360367/1000000000000 : ℝ) (62620545047/125000000000 : ℝ) (250482180183/500000000000 : ℝ) (62620545047/125000000000 : ℝ) (250482180183/500000000000 : ℝ) (62620545047/125000000000 : ℝ) (250482180183/500000000000 : ℝ) (62620545047/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16661/131072 : ℝ))) 6 (250482180183/500000000000 : ℝ) (62620545047/125000000000 : ℝ) (250482180183/500000000000 : ℝ) (62620545047/125000000000 : ℝ) (250482180183/500000000000 : ℝ) (62620545047/125000000000 : ℝ) (250482180183/500000000000 : ℝ) (62620545047/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16661/131072 : ℝ))) 7 (250482180183/500000000000 : ℝ) (62620545047/125000000000 : ℝ) (250482180183/500000000000 : ℝ) (62620545047/125000000000 : ℝ) (250482180183/500000000000 : ℝ) (62620545047/125000000000 : ℝ) (250482180183/500000000000 : ℝ) (62620545047/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16661/131072 : ℝ)) hmem 8 (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ) (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16661/131072 : ℝ))) hcmem 8 (250482180183/500000000000 : ℝ) (62620545047/125000000000 : ℝ) (250482180183/500000000000 : ℝ) (62620545047/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16661/131072 : ℝ)) (992102545167/1000000000000 : ℝ) (99210254517/100000000000 : ℝ) (250482180183/500000000000 : ℝ) (62620545047/125000000000 : ℝ) (396588528549/500000000000 : ℝ) (793177057117/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0571_exp_lower
  have heNumeric : (2054903193267/1000000000000 : ℝ)/4 ≤ Real.exp (-85256399639101/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903193267/1000000000000 : ℝ)/4 ≤ Real.exp ((66643/524288 : ℝ)-(793177057117/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66643/524288 : ℝ) (16661/131072 : ℝ) (793177057117/1000000000000 : ℝ) (2054903193267/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0572; no trusted numerical premise.
theorem cover8_leaf0572_exp_radius : (499007897683175153/500000000000000000 : ℝ) ≤ Real.exp ((-66645/4194304 : ℝ)/8) ∧ Real.exp ((-66645/4194304 : ℝ)/8) ≤ (998015795366350307/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66645/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0572_exp_lower : (46005677001758819/50000000000000000 : ℝ) ≤ Real.exp ((-21314100088859/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314100088859/32000000000000 : ℝ)/8) ≤ (920113540035176381/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314100088859/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0572_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903181767/1000000000000 : ℝ) ≤ 4*Real.exp (16661/131072 : ℝ)*Real.exp (-mu (radius 8 (66645/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903181767/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66645/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0572_exp_radius
  have hrNumeric : (984236164449/1000000000000 : ℝ) ≤ Real.exp (-66645/4194304 : ℝ) ∧ Real.exp (-66645/4194304 : ℝ) ≤ (19684723289/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984236164449/1000000000000 : ℝ) ≤ (radius 8 (66645/524288 : ℝ)) ∧ (radius 8 (66645/524288 : ℝ)) ≤ (19684723289/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66645/524288 : ℝ)) (984236164449/1000000000000 : ℝ) (19684723289/20000000000 : ℝ) (17685918859/100000000000 : ℝ) (44214797149/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66645/524288 : ℝ)) (984236164449/1000000000000 : ℝ) (19684723289/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66645/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984236164449/1000000000000 : ℝ) (19684723289/20000000000 : ℝ) (62007380139/62500000000 : ℝ) (39684723289/40000000000 : ℝ) (6200542329/6250000000 : ℝ) (496043386321/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66645/524288 : ℝ)) 1 (62007380139/62500000000 : ℝ) (39684723289/40000000000 : ℝ) (6200542329/6250000000 : ℝ) (496043386321/500000000000 : ℝ) (124012803429/125000000000 : ℝ) (496051213717/500000000000 : ℝ) (248025606827/250000000000 : ℝ) (99210242731/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66645/524288 : ℝ)) 2 (124012803429/125000000000 : ℝ) (496051213717/500000000000 : ℝ) (248025606827/250000000000 : ℝ) (99210242731/100000000000 : ℝ) (99210242737/100000000000 : ℝ) (248025606843/250000000000 : ℝ) (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66645/524288 : ℝ)) 3 (99210242737/100000000000 : ℝ) (248025606843/250000000000 : ℝ) (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ) (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ) (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66645/524288 : ℝ)) 4 (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ) (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ) (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ) (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66645/524288 : ℝ)) 5 (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ) (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ) (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ) (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66645/524288 : ℝ)) 6 (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ) (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ) (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ) (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66645/524288 : ℝ)) 7 (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ) (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ) (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ) (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66645/524288 : ℝ))) (17685918859/100000000000 : ℝ) (44214797149/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66645/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17685918859/100000000000 : ℝ) (44214797149/250000000000 : ℝ) (117685918859/200000000000 : ℝ) (294214797149/500000000000 : ℝ) (105136574449/250000000000 : ℝ) (105136574451/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66645/524288 : ℝ))) 1 (117685918859/200000000000 : ℝ) (294214797149/500000000000 : ℝ) (105136574449/250000000000 : ℝ) (105136574451/250000000000 : ℝ) (100897589209/200000000000 : ℝ) (504487946051/1000000000000 : ℝ) (124363853117/250000000000 : ℝ) (19898216499/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66645/524288 : ℝ))) 2 (100897589209/200000000000 : ℝ) (504487946051/1000000000000 : ℝ) (124363853117/250000000000 : ℝ) (19898216499/40000000000 : ℝ) (62621459907/125000000000 : ℝ) (500971679263/1000000000000 : ℝ) (500959338953/1000000000000 : ℝ) (500959338961/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66645/524288 : ℝ))) 3 (62621459907/125000000000 : ℝ) (500971679263/1000000000000 : ℝ) (500959338953/1000000000000 : ℝ) (500959338961/1000000000000 : ℝ) (31310344319/62500000000 : ℝ) (62620688639/125000000000 : ℝ) (250482754533/500000000000 : ℝ) (20038620363/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66645/524288 : ℝ))) 4 (31310344319/62500000000 : ℝ) (62620688639/125000000000 : ℝ) (250482754533/500000000000 : ℝ) (20038620363/40000000000 : ℝ) (100193101817/200000000000 : ℝ) (250482754547/500000000000 : ℝ) (125241377271/250000000000 : ℝ) (250482754547/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66645/524288 : ℝ))) 5 (100193101817/200000000000 : ℝ) (250482754547/500000000000 : ℝ) (125241377271/250000000000 : ℝ) (250482754547/500000000000 : ℝ) (125241377271/250000000000 : ℝ) (250482754547/500000000000 : ℝ) (125241377271/250000000000 : ℝ) (250482754547/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66645/524288 : ℝ))) 6 (125241377271/250000000000 : ℝ) (250482754547/500000000000 : ℝ) (125241377271/250000000000 : ℝ) (250482754547/500000000000 : ℝ) (125241377271/250000000000 : ℝ) (250482754547/500000000000 : ℝ) (125241377271/250000000000 : ℝ) (250482754547/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66645/524288 : ℝ))) 7 (125241377271/250000000000 : ℝ) (250482754547/500000000000 : ℝ) (125241377271/250000000000 : ℝ) (250482754547/500000000000 : ℝ) (125241377271/250000000000 : ℝ) (250482754547/500000000000 : ℝ) (125241377271/250000000000 : ℝ) (250482754547/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66645/524288 : ℝ)) hmem 8 (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ) (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66645/524288 : ℝ))) hcmem 8 (125241377271/250000000000 : ℝ) (250482754547/500000000000 : ℝ) (125241377271/250000000000 : ℝ) (250482754547/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66645/524288 : ℝ)) (992102427369/1000000000000 : ℝ) (248025606843/250000000000 : ℝ) (125241377271/250000000000 : ℝ) (250482754547/500000000000 : ℝ) (396589485021/500000000000 : ℝ) (396589485031/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0572_exp_lower
  have heNumeric : (2054903181767/1000000000000 : ℝ)/4 ≤ Real.exp (-21314100088859/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903181767/1000000000000 : ℝ)/4 ≤ Real.exp ((16661/131072 : ℝ)-(396589485031/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16661/131072 : ℝ) (66645/524288 : ℝ) (396589485031/500000000000 : ℝ) (2054903181767/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0573; no trusted numerical premise.
theorem cover8_leaf0573_exp_radius : (249503941405790567/250000000000000000 : ℝ) ≤ Real.exp ((-33323/2097152 : ℝ)/8) ∧ Real.exp ((-33323/2097152 : ℝ)/8) ≤ (998015765623162269/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33323/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0573_exp_lower : (920113539393815011/1000000000000000000 : ℝ) ≤ Real.exp ((-85256401069211/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256401069211/128000000000000 : ℝ)/8) ≤ (230028384848453753/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256401069211/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0573_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725792577/250000000000 : ℝ) ≤ 4*Real.exp (66645/524288 : ℝ)*Real.exp (-mu (radius 8 (33323/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725792577/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33323/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0573_exp_radius
  have hrNumeric : (984235929789/1000000000000 : ℝ) ≤ Real.exp (-33323/2097152 : ℝ) ∧ Real.exp (-33323/2097152 : ℝ) ≤ (98423592979/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984235929789/1000000000000 : ℝ) ≤ (radius 8 (33323/262144 : ℝ)) ∧ (radius 8 (33323/262144 : ℝ)) ≤ (98423592979/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33323/262144 : ℝ)) (984235929789/1000000000000 : ℝ) (98423592979/100000000000 : ℝ) (176860494487/1000000000000 : ℝ) (88430247247/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33323/262144 : ℝ)) (984235929789/1000000000000 : ℝ) (98423592979/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33323/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984235929789/1000000000000 : ℝ) (98423592979/100000000000 : ℝ) (496058982447/500000000000 : ℝ) (198423592979/200000000000 : ℝ) (1587338647/1600000000 : ℝ) (124010831797/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33323/262144 : ℝ)) 1 (496058982447/500000000000 : ℝ) (198423592979/200000000000 : ℝ) (1587338647/1600000000 : ℝ) (124010831797/125000000000 : ℝ) (496051154817/500000000000 : ℝ) (248025577409/250000000000 : ℝ) (99210230951/100000000000 : ℝ) (124012788689/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33323/262144 : ℝ)) 2 (496051154817/500000000000 : ℝ) (248025577409/250000000000 : ℝ) (99210230951/100000000000 : ℝ) (124012788689/125000000000 : ℝ) (248025577393/250000000000 : ℝ) (496051154787/500000000000 : ℝ) (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33323/262144 : ℝ)) 3 (248025577393/250000000000 : ℝ) (496051154787/500000000000 : ℝ) (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ) (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ) (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33323/262144 : ℝ)) 4 (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ) (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ) (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ) (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33323/262144 : ℝ)) 5 (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ) (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ) (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ) (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33323/262144 : ℝ)) 6 (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ) (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ) (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ) (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33323/262144 : ℝ)) 7 (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ) (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ) (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ) (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33323/262144 : ℝ))) (176860494487/1000000000000 : ℝ) (88430247247/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33323/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176860494487/1000000000000 : ℝ) (88430247247/500000000000 : ℝ) (588430247243/1000000000000 : ℝ) (588430247247/1000000000000 : ℝ) (420547850413/1000000000000 : ℝ) (210273925211/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33323/262144 : ℝ))) 1 (588430247243/1000000000000 : ℝ) (588430247247/1000000000000 : ℝ) (420547850413/1000000000000 : ℝ) (210273925211/500000000000 : ℝ) (126122262207/250000000000 : ℝ) (100897809767/200000000000 : ℝ) (248728303373/500000000000 : ℝ) (248728303377/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33323/262144 : ℝ))) 2 (126122262207/250000000000 : ℝ) (100897809767/200000000000 : ℝ) (248728303373/500000000000 : ℝ) (248728303377/500000000000 : ℝ) (500972827787/1000000000000 : ℝ) (100194565559/200000000000 : ℝ) (500960487833/1000000000000 : ℝ) (250480243921/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33323/262144 : ℝ))) 3 (500972827787/1000000000000 : ℝ) (100194565559/200000000000 : ℝ) (500960487833/1000000000000 : ℝ) (250480243921/500000000000 : ℝ) (50096665781/100000000000 : ℝ) (500966657819/1000000000000 : ℝ) (125241664443/250000000000 : ℝ) (500966657781/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33323/262144 : ℝ))) 4 (50096665781/100000000000 : ℝ) (500966657819/1000000000000 : ℝ) (125241664443/250000000000 : ℝ) (500966657781/1000000000000 : ℝ) (500966657791/1000000000000 : ℝ) (2504833289/5000000000 : ℝ) (50096665779/100000000000 : ℝ) (2504833289/5000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33323/262144 : ℝ))) 5 (500966657791/1000000000000 : ℝ) (2504833289/5000000000 : ℝ) (50096665779/100000000000 : ℝ) (2504833289/5000000000 : ℝ) (50096665779/100000000000 : ℝ) (2504833289/5000000000 : ℝ) (50096665779/100000000000 : ℝ) (2504833289/5000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33323/262144 : ℝ))) 6 (50096665779/100000000000 : ℝ) (2504833289/5000000000 : ℝ) (50096665779/100000000000 : ℝ) (2504833289/5000000000 : ℝ) (50096665779/100000000000 : ℝ) (2504833289/5000000000 : ℝ) (50096665779/100000000000 : ℝ) (2504833289/5000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33323/262144 : ℝ))) 7 (50096665779/100000000000 : ℝ) (2504833289/5000000000 : ℝ) (50096665779/100000000000 : ℝ) (2504833289/5000000000 : ℝ) (50096665779/100000000000 : ℝ) (2504833289/5000000000 : ℝ) (50096665779/100000000000 : ℝ) (2504833289/5000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33323/262144 : ℝ)) hmem 8 (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ) (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33323/262144 : ℝ))) hcmem 8 (50096665779/100000000000 : ℝ) (2504833289/5000000000 : ℝ) (50096665779/100000000000 : ℝ) (2504833289/5000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33323/262144 : ℝ)) (992102309571/1000000000000 : ℝ) (496051154787/500000000000 : ℝ) (50096665779/100000000000 : ℝ) (2504833289/5000000000 : ℝ) (99147610371/125000000000 : ℝ) (793180882987/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0573_exp_lower
  have heNumeric : (513725792577/250000000000 : ℝ)/4 ≤ Real.exp (-85256401069211/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725792577/250000000000 : ℝ)/4 ≤ Real.exp ((66645/524288 : ℝ)-(793180882987/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66645/524288 : ℝ) (33323/262144 : ℝ) (793180882987/1000000000000 : ℝ) (513725792577/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0574; no trusted numerical premise.
theorem cover8_leaf0574_exp_radius : (249503933969993779/250000000000000000 : ℝ) ≤ Real.exp ((-66647/4194304 : ℝ)/8) ∧ Real.exp ((-66647/4194304 : ℝ)/8) ≤ (998015735879975117/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66647/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0574_exp_lower : (14376774043041233/15625000000000000 : ℝ) ≤ Real.exp ((-42628200890277/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628200890277/64000000000000 : ℝ)/8) ≤ (920113538754638913/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628200890277/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0574_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862894861/125000000000 : ℝ) ≤ 4*Real.exp (33323/262144 : ℝ)*Real.exp (-mu (radius 8 (66647/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862894861/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66647/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0574_exp_radius
  have hrNumeric : (984235695129/1000000000000 : ℝ) ≤ Real.exp (-66647/4194304 : ℝ) ∧ Real.exp (-66647/4194304 : ℝ) ≤ (98423569513/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984235695129/1000000000000 : ℝ) ≤ (radius 8 (66647/524288 : ℝ)) ∧ (radius 8 (66647/524288 : ℝ)) ≤ (98423569513/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66647/524288 : ℝ)) (984235695129/1000000000000 : ℝ) (98423569513/100000000000 : ℝ) (1414894403/8000000000 : ℝ) (176861800381/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66647/524288 : ℝ)) (984235695129/1000000000000 : ℝ) (98423569513/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66647/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984235695129/1000000000000 : ℝ) (98423569513/100000000000 : ℝ) (248029461891/250000000000 : ℝ) (198423569513/200000000000 : ℝ) (992086536109/1000000000000 : ℝ) (99208653611/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66647/524288 : ℝ)) 1 (248029461891/250000000000 : ℝ) (198423569513/200000000000 : ℝ) (992086536109/1000000000000 : ℝ) (99208653611/100000000000 : ℝ) (248025547959/250000000000 : ℝ) (496051095919/500000000000 : ℝ) (31003193491/31250000000 : ℝ) (496051095857/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66647/524288 : ℝ)) 2 (248025547959/250000000000 : ℝ) (496051095919/500000000000 : ℝ) (31003193491/31250000000 : ℝ) (496051095857/500000000000 : ℝ) (496051095887/500000000000 : ℝ) (31003193493/31250000000 : ℝ) (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66647/524288 : ℝ)) 3 (496051095887/500000000000 : ℝ) (31003193493/31250000000 : ℝ) (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ) (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ) (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66647/524288 : ℝ)) 4 (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ) (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ) (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ) (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66647/524288 : ℝ)) 5 (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ) (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ) (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ) (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66647/524288 : ℝ)) 6 (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ) (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ) (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ) (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66647/524288 : ℝ)) 7 (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ) (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ) (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ) (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66647/524288 : ℝ))) (1414894403/8000000000 : ℝ) (176861800381/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66647/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1414894403/8000000000 : ℝ) (176861800381/1000000000000 : ℝ) (588430900187/1000000000000 : ℝ) (588430900191/1000000000000 : ℝ) (420549403013/1000000000000 : ℝ) (420549403021/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66647/524288 : ℝ))) 1 (588430900187/1000000000000 : ℝ) (588430900191/1000000000000 : ℝ) (420549403013/1000000000000 : ℝ) (420549403021/1000000000000 : ℝ) (1261225379/2500000000 : ℝ) (252245075803/500000000000 : ℝ) (124364450253/250000000000 : ℝ) (497457801019/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66647/524288 : ℝ))) 2 (1261225379/2500000000 : ℝ) (252245075803/500000000000 : ℝ) (124364450253/250000000000 : ℝ) (497457801019/1000000000000 : ℝ) (250486988153/500000000000 : ℝ) (500973976313/1000000000000 : ℝ) (500961636701/1000000000000 : ℝ) (500961636709/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66647/524288 : ℝ))) 3 (250486988153/500000000000 : ℝ) (500973976313/1000000000000 : ℝ) (500961636701/1000000000000 : ℝ) (500961636709/1000000000000 : ℝ) (500967806503/1000000000000 : ℝ) (500967806511/1000000000000 : ℝ) (100193561293/200000000000 : ℝ) (250483903237/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66647/524288 : ℝ))) 4 (500967806503/1000000000000 : ℝ) (500967806511/1000000000000 : ℝ) (100193561293/200000000000 : ℝ) (250483903237/500000000000 : ℝ) (125241951621/250000000000 : ℝ) (500967806493/1000000000000 : ℝ) (500967806483/1000000000000 : ℝ) (500967806493/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66647/524288 : ℝ))) 5 (125241951621/250000000000 : ℝ) (500967806493/1000000000000 : ℝ) (500967806483/1000000000000 : ℝ) (500967806493/1000000000000 : ℝ) (500967806483/1000000000000 : ℝ) (500967806493/1000000000000 : ℝ) (500967806483/1000000000000 : ℝ) (500967806493/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66647/524288 : ℝ))) 6 (500967806483/1000000000000 : ℝ) (500967806493/1000000000000 : ℝ) (500967806483/1000000000000 : ℝ) (500967806493/1000000000000 : ℝ) (500967806483/1000000000000 : ℝ) (500967806493/1000000000000 : ℝ) (500967806483/1000000000000 : ℝ) (500967806493/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66647/524288 : ℝ))) 7 (500967806483/1000000000000 : ℝ) (500967806493/1000000000000 : ℝ) (500967806483/1000000000000 : ℝ) (500967806493/1000000000000 : ℝ) (500967806483/1000000000000 : ℝ) (500967806493/1000000000000 : ℝ) (500967806483/1000000000000 : ℝ) (500967806493/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66647/524288 : ℝ)) hmem 8 (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ) (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66647/524288 : ℝ))) hcmem 8 (500967806483/1000000000000 : ℝ) (500967806493/1000000000000 : ℝ) (500967806483/1000000000000 : ℝ) (500967806493/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66647/524288 : ℝ)) (992102191773/1000000000000 : ℝ) (31003193493/31250000000 : ℝ) (500967806483/1000000000000 : ℝ) (500967806493/1000000000000 : ℝ) (396591397937/500000000000 : ℝ) (793182795893/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0574_exp_lower
  have heNumeric : (256862894861/125000000000 : ℝ)/4 ≤ Real.exp (-42628200890277/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862894861/125000000000 : ℝ)/4 ≤ Real.exp ((33323/262144 : ℝ)-(793182795893/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33323/262144 : ℝ) (66647/524288 : ℝ) (793182795893/1000000000000 : ℝ) (256862894861/125000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0550_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0550_certificate
#check SmaleRate.Proofs.cover8_leaf0551_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0551_certificate
#check SmaleRate.Proofs.cover8_leaf0552_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0552_certificate
#check SmaleRate.Proofs.cover8_leaf0553_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0553_certificate
#check SmaleRate.Proofs.cover8_leaf0554_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0554_certificate
#check SmaleRate.Proofs.cover8_leaf0555_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0555_certificate
#check SmaleRate.Proofs.cover8_leaf0556_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0556_certificate
#check SmaleRate.Proofs.cover8_leaf0557_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0557_certificate
#check SmaleRate.Proofs.cover8_leaf0558_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0558_certificate
#check SmaleRate.Proofs.cover8_leaf0559_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0559_certificate
#check SmaleRate.Proofs.cover8_leaf0560_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0560_certificate
#check SmaleRate.Proofs.cover8_leaf0561_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0561_certificate
#check SmaleRate.Proofs.cover8_leaf0562_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0562_certificate
#check SmaleRate.Proofs.cover8_leaf0563_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0563_certificate
#check SmaleRate.Proofs.cover8_leaf0564_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0564_certificate
#check SmaleRate.Proofs.cover8_leaf0565_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0565_certificate
#check SmaleRate.Proofs.cover8_leaf0566_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0566_certificate
#check SmaleRate.Proofs.cover8_leaf0567_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0567_certificate
#check SmaleRate.Proofs.cover8_leaf0568_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0568_certificate
#check SmaleRate.Proofs.cover8_leaf0569_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0569_certificate
#check SmaleRate.Proofs.cover8_leaf0570_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0570_certificate
#check SmaleRate.Proofs.cover8_leaf0571_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0571_certificate
#check SmaleRate.Proofs.cover8_leaf0572_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0572_certificate
#check SmaleRate.Proofs.cover8_leaf0573_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0573_certificate
#check SmaleRate.Proofs.cover8_leaf0574_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0574_certificate
