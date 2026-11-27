/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0325; no trusted numerical premise.
theorem cover8_leaf0325_exp_radius : (199605758644871219/200000000000000000 : ℝ) ≤ Real.exp ((-2069/131072 : ℝ)/8) ∧ Real.exp ((-2069/131072 : ℝ)/8) ≤ (3898549973532641/3906250000000000 : ℝ) := by
  have h := exp_small_bounds ((-2069/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0325_exp_lower : (920113377480176487/1000000000000000000 : ℝ) ≤ Real.exp ((-21314145315977/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314145315977/32000000000000 : ℝ)/8) ≤ (115014172185022061/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314145315977/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0325_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900277477/1000000000000 : ℝ) ≤ 4*Real.exp (16551/131072 : ℝ)*Real.exp (-mu (radius 8 (2069/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900277477/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2069/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0325_exp_radius
  have hrNumeric : (492169358147/500000000000 : ℝ) ≤ Real.exp (-2069/131072 : ℝ) ∧ Real.exp (-2069/131072 : ℝ) ≤ (196867743259/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492169358147/500000000000 : ℝ) ≤ (radius 8 (2069/16384 : ℝ)) ∧ (radius 8 (2069/16384 : ℝ)) ≤ (196867743259/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2069/16384 : ℝ)) (492169358147/500000000000 : ℝ) (196867743259/200000000000 : ℝ) (88143762687/500000000000 : ℝ) (176287525381/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2069/16384 : ℝ)) (492169358147/500000000000 : ℝ) (196867743259/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2069/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492169358147/500000000000 : ℝ) (196867743259/200000000000 : ℝ) (992169358147/1000000000000 : ℝ) (248042339537/250000000000 : ℝ) (992138456211/1000000000000 : ℝ) (992138456213/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2069/16384 : ℝ)) 1 (992169358147/1000000000000 : ℝ) (248042339537/250000000000 : ℝ) (992138456211/1000000000000 : ℝ) (992138456213/1000000000000 : ℝ) (992153907179/1000000000000 : ℝ) (992153907181/1000000000000 : ℝ) (496076953529/500000000000 : ℝ) (992153907061/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2069/16384 : ℝ)) 2 (992153907179/1000000000000 : ℝ) (992153907181/1000000000000 : ℝ) (496076953529/500000000000 : ℝ) (992153907061/1000000000000 : ℝ) (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ) (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2069/16384 : ℝ)) 3 (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ) (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ) (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ) (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2069/16384 : ℝ)) 4 (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ) (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ) (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ) (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2069/16384 : ℝ)) 5 (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ) (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ) (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ) (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2069/16384 : ℝ)) 6 (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ) (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ) (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ) (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2069/16384 : ℝ)) 7 (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ) (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ) (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ) (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2069/16384 : ℝ))) (88143762687/500000000000 : ℝ) (176287525381/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2069/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88143762687/500000000000 : ℝ) (176287525381/1000000000000 : ℝ) (588143762687/1000000000000 : ℝ) (588143762691/1000000000000 : ℝ) (83973216057/200000000000 : ℝ) (209933040147/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2069/16384 : ℝ))) 1 (588143762687/1000000000000 : ℝ) (588143762691/1000000000000 : ℝ) (83973216057/200000000000 : ℝ) (209933040147/500000000000 : ℝ) (252002460743/500000000000 : ℝ) (504004921493/1000000000000 : ℝ) (124233051229/250000000000 : ℝ) (124233051231/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2069/16384 : ℝ))) 2 (252002460743/500000000000 : ℝ) (504004921493/1000000000000 : ℝ) (124233051229/250000000000 : ℝ) (124233051231/250000000000 : ℝ) (500468563201/1000000000000 : ℝ) (500468563209/1000000000000 : ℝ) (500456068923/1000000000000 : ℝ) (125114017233/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2069/16384 : ℝ))) 3 (500468563201/1000000000000 : ℝ) (500468563209/1000000000000 : ℝ) (500456068923/1000000000000 : ℝ) (125114017233/250000000000 : ℝ) (250231158031/500000000000 : ℝ) (500462316071/1000000000000 : ℝ) (500462316023/1000000000000 : ℝ) (977465461/1953125000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2069/16384 : ℝ))) 4 (250231158031/500000000000 : ℝ) (500462316071/1000000000000 : ℝ) (500462316023/1000000000000 : ℝ) (977465461/1953125000 : ℝ) (250231158021/500000000000 : ℝ) (125115579013/250000000000 : ℝ) (250231158021/500000000000 : ℝ) (125115579013/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2069/16384 : ℝ))) 5 (250231158021/500000000000 : ℝ) (125115579013/250000000000 : ℝ) (250231158021/500000000000 : ℝ) (125115579013/250000000000 : ℝ) (250231158021/500000000000 : ℝ) (125115579013/250000000000 : ℝ) (250231158021/500000000000 : ℝ) (125115579013/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2069/16384 : ℝ))) 6 (250231158021/500000000000 : ℝ) (125115579013/250000000000 : ℝ) (250231158021/500000000000 : ℝ) (125115579013/250000000000 : ℝ) (250231158021/500000000000 : ℝ) (125115579013/250000000000 : ℝ) (250231158021/500000000000 : ℝ) (125115579013/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2069/16384 : ℝ))) 7 (250231158021/500000000000 : ℝ) (125115579013/250000000000 : ℝ) (250231158021/500000000000 : ℝ) (125115579013/250000000000 : ℝ) (250231158021/500000000000 : ℝ) (125115579013/250000000000 : ℝ) (250231158021/500000000000 : ℝ) (125115579013/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2069/16384 : ℝ)) hmem 8 (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ) (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2069/16384 : ℝ))) hcmem 8 (250231158021/500000000000 : ℝ) (125115579013/250000000000 : ℝ) (250231158021/500000000000 : ℝ) (125115579013/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2069/16384 : ℝ)) (496076953559/500000000000 : ℝ) (992153907121/1000000000000 : ℝ) (250231158021/500000000000 : ℝ) (125115579013/250000000000 : ℝ) (99042643749/125000000000 : ℝ) (792341150011/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0325_exp_lower
  have heNumeric : (2054900277477/1000000000000 : ℝ)/4 ≤ Real.exp (-21314145315977/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900277477/1000000000000 : ℝ)/4 ≤ Real.exp ((16551/131072 : ℝ)-(792341150011/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16551/131072 : ℝ) (2069/16384 : ℝ) (792341150011/1000000000000 : ℝ) (2054900277477/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0326; no trusted numerical premise.
theorem cover8_leaf0326_exp_radius : (199605734850011959/200000000000000000 : ℝ) ≤ Real.exp ((-16553/1048576 : ℝ)/8) ∧ Real.exp ((-16553/1048576 : ℝ)/8) ≤ (249507168562514949/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16553/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0326_exp_lower : (230028342747353201/250000000000000000 : ℝ) ≤ Real.exp ((-532853678047/800000000000 : ℝ)/8) ∧ Real.exp ((-532853678047/800000000000 : ℝ)/8) ≤ (184022674197882561/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-532853678047/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0326_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900161509/1000000000000 : ℝ) ≤ 4*Real.exp (2069/16384 : ℝ)*Real.exp (-mu (radius 8 (16553/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900161509/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16553/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0326_exp_radius
  have hrNumeric : (246084444389/250000000000 : ℝ) ≤ Real.exp (-16553/1048576 : ℝ) ∧ Real.exp (-16553/1048576 : ℝ) ≤ (984337777557/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246084444389/250000000000 : ℝ) ≤ (radius 8 (16553/131072 : ℝ)) ∧ (radius 8 (16553/131072 : ℝ)) ≤ (984337777557/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16553/131072 : ℝ)) (246084444389/250000000000 : ℝ) (984337777557/1000000000000 : ℝ) (22036595867/125000000000 : ℝ) (176292766943/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16553/131072 : ℝ)) (246084444389/250000000000 : ℝ) (984337777557/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16553/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246084444389/250000000000 : ℝ) (984337777557/1000000000000 : ℝ) (496084444389/500000000000 : ℝ) (992168888779/1000000000000 : ℝ) (992137983123/1000000000000 : ℝ) (248034495781/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16553/131072 : ℝ)) 1 (496084444389/500000000000 : ℝ) (992168888779/1000000000000 : ℝ) (992137983123/1000000000000 : ℝ) (248034495781/250000000000 : ℝ) (19843068719/20000000000 : ℝ) (62009589747/62500000000 : ℝ) (99215343583/100000000000 : ℝ) (124019179479/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16553/131072 : ℝ)) 2 (19843068719/20000000000 : ℝ) (62009589747/62500000000 : ℝ) (99215343583/100000000000 : ℝ) (124019179479/125000000000 : ℝ) (99215343589/100000000000 : ℝ) (248038358973/250000000000 : ℝ) (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16553/131072 : ℝ)) 3 (99215343589/100000000000 : ℝ) (248038358973/250000000000 : ℝ) (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ) (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ) (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16553/131072 : ℝ)) 4 (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ) (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ) (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ) (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16553/131072 : ℝ)) 5 (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ) (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ) (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ) (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16553/131072 : ℝ)) 6 (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ) (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ) (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ) (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16553/131072 : ℝ)) 7 (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ) (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ) (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ) (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16553/131072 : ℝ))) (22036595867/125000000000 : ℝ) (176292766943/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16553/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22036595867/125000000000 : ℝ) (176292766943/1000000000000 : ℝ) (147036595867/250000000000 : ℝ) (36759148967/62500000000 : ℝ) (419872322183/1000000000000 : ℝ) (419872322193/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16553/131072 : ℝ))) 1 (147036595867/250000000000 : ℝ) (36759148967/62500000000 : ℝ) (419872322183/1000000000000 : ℝ) (419872322193/1000000000000 : ℝ) (20160374113/40000000000 : ℝ) (504009352833/1000000000000 : ℝ) (496937005877/1000000000000 : ℝ) (99387401177/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16553/131072 : ℝ))) 2 (20160374113/40000000000 : ℝ) (504009352833/1000000000000 : ℝ) (496937005877/1000000000000 : ℝ) (99387401177/200000000000 : ℝ) (500473179351/1000000000000 : ℝ) (500473179359/1000000000000 : ℝ) (250230343247/500000000000 : ℝ) (500460686503/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16553/131072 : ℝ))) 3 (500473179351/1000000000000 : ℝ) (500473179359/1000000000000 : ℝ) (250230343247/500000000000 : ℝ) (500460686503/1000000000000 : ℝ) (250233466461/500000000000 : ℝ) (500466932931/1000000000000 : ℝ) (500466932883/1000000000000 : ℝ) (500466932893/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16553/131072 : ℝ))) 4 (250233466461/500000000000 : ℝ) (500466932931/1000000000000 : ℝ) (500466932883/1000000000000 : ℝ) (500466932893/1000000000000 : ℝ) (250233466451/500000000000 : ℝ) (31279183307/62500000000 : ℝ) (250233466451/500000000000 : ℝ) (31279183307/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16553/131072 : ℝ))) 5 (250233466451/500000000000 : ℝ) (31279183307/62500000000 : ℝ) (250233466451/500000000000 : ℝ) (31279183307/62500000000 : ℝ) (250233466451/500000000000 : ℝ) (31279183307/62500000000 : ℝ) (250233466451/500000000000 : ℝ) (31279183307/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16553/131072 : ℝ))) 6 (250233466451/500000000000 : ℝ) (31279183307/62500000000 : ℝ) (250233466451/500000000000 : ℝ) (31279183307/62500000000 : ℝ) (250233466451/500000000000 : ℝ) (31279183307/62500000000 : ℝ) (250233466451/500000000000 : ℝ) (31279183307/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16553/131072 : ℝ))) 7 (250233466451/500000000000 : ℝ) (31279183307/62500000000 : ℝ) (250233466451/500000000000 : ℝ) (31279183307/62500000000 : ℝ) (250233466451/500000000000 : ℝ) (31279183307/62500000000 : ℝ) (250233466451/500000000000 : ℝ) (31279183307/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16553/131072 : ℝ)) hmem 8 (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ) (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16553/131072 : ℝ))) hcmem 8 (250233466451/500000000000 : ℝ) (31279183307/62500000000 : ℝ) (250233466451/500000000000 : ℝ) (31279183307/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16553/131072 : ℝ)) (992153435889/1000000000000 : ℝ) (248038358973/250000000000 : ℝ) (250233466451/500000000000 : ℝ) (31279183307/62500000000 : ℝ) (39617441791/50000000000 : ℝ) (38688908/48828125 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0326_exp_lower
  have heNumeric : (2054900161509/1000000000000 : ℝ)/4 ≤ Real.exp (-532853678047/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900161509/1000000000000 : ℝ)/4 ≤ Real.exp ((2069/16384 : ℝ)-(38688908/48828125 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2069/16384 : ℝ) (16553/131072 : ℝ) (38688908/48828125 : ℝ) (2054900161509/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0327; no trusted numerical premise.
theorem cover8_leaf0327_exp_radius : (499014277637888839/500000000000000000 : ℝ) ≤ Real.exp ((-8277/524288 : ℝ)/8) ∧ Real.exp ((-8277/524288 : ℝ)/8) ≤ (998028555275777679/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8277/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0327_exp_lower : (920113364533958517/1000000000000000000 : ℝ) ≤ Real.exp ((-21314148917959/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314148917959/32000000000000 : ℝ)/8) ≤ (460056682266979259/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314148917959/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0327_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900046173/1000000000000 : ℝ) ≤ 4*Real.exp (16553/131072 : ℝ)*Real.exp (-mu (radius 8 (8277/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900046173/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8277/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0327_exp_radius
  have hrNumeric : (492168419409/500000000000 : ℝ) ≤ Real.exp (-8277/524288 : ℝ) ∧ Real.exp (-8277/524288 : ℝ) ≤ (984336838819/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492168419409/500000000000 : ℝ) ≤ (radius 8 (8277/65536 : ℝ)) ∧ (radius 8 (8277/65536 : ℝ)) ≤ (984336838819/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8277/65536 : ℝ)) (492168419409/500000000000 : ℝ) (984336838819/1000000000000 : ℝ) (176298008337/1000000000000 : ℝ) (22037251043/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8277/65536 : ℝ)) (492168419409/500000000000 : ℝ) (984336838819/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8277/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492168419409/500000000000 : ℝ) (984336838819/1000000000000 : ℝ) (992168419409/1000000000000 : ℝ) (99216841941/100000000000 : ℝ) (496068755017/500000000000 : ℝ) (248034377509/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8277/65536 : ℝ)) 1 (992168419409/1000000000000 : ℝ) (99216841941/100000000000 : ℝ) (496068755017/500000000000 : ℝ) (248034377509/250000000000 : ℝ) (992152964721/1000000000000 : ℝ) (992152964723/1000000000000 : ℝ) (992152964601/1000000000000 : ℝ) (992152964603/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8277/65536 : ℝ)) 2 (992152964721/1000000000000 : ℝ) (992152964723/1000000000000 : ℝ) (992152964601/1000000000000 : ℝ) (992152964603/1000000000000 : ℝ) (992152964661/1000000000000 : ℝ) (992152964663/1000000000000 : ℝ) (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8277/65536 : ℝ)) 3 (992152964661/1000000000000 : ℝ) (992152964663/1000000000000 : ℝ) (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ) (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ) (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8277/65536 : ℝ)) 4 (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ) (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ) (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ) (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8277/65536 : ℝ)) 5 (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ) (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ) (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ) (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8277/65536 : ℝ)) 6 (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ) (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ) (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ) (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8277/65536 : ℝ)) 7 (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ) (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ) (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ) (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8277/65536 : ℝ))) (176298008337/1000000000000 : ℝ) (22037251043/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8277/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176298008337/1000000000000 : ℝ) (22037251043/125000000000 : ℝ) (73518625521/125000000000 : ℝ) (147037251043/250000000000 : ℝ) (419878563797/1000000000000 : ℝ) (419878563807/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8277/65536 : ℝ))) 1 (73518625521/125000000000 : ℝ) (147037251043/250000000000 : ℝ) (419878563797/1000000000000 : ℝ) (419878563807/1000000000000 : ℝ) (252006891991/500000000000 : ℝ) (50401378399/100000000000 : ℝ) (496941806621/1000000000000 : ℝ) (49694180663/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8277/65536 : ℝ))) 2 (252006891991/500000000000 : ℝ) (50401378399/100000000000 : ℝ) (496941806621/1000000000000 : ℝ) (49694180663/100000000000 : ℝ) (500477795301/1000000000000 : ℝ) (50047779531/100000000000 : ℝ) (250232651933/500000000000 : ℝ) (4003722431/8000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8277/65536 : ℝ))) 3 (500477795301/1000000000000 : ℝ) (50047779531/100000000000 : ℝ) (250232651933/500000000000 : ℝ) (4003722431/8000000000 : ℝ) (500471549583/1000000000000 : ℝ) (500471549593/1000000000000 : ℝ) (62558943693/125000000000 : ℝ) (250235774777/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8277/65536 : ℝ))) 4 (500471549583/1000000000000 : ℝ) (500471549593/1000000000000 : ℝ) (62558943693/125000000000 : ℝ) (250235774777/500000000000 : ℝ) (500471549563/1000000000000 : ℝ) (250235774787/500000000000 : ℝ) (500471549563/1000000000000 : ℝ) (250235774787/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8277/65536 : ℝ))) 5 (500471549563/1000000000000 : ℝ) (250235774787/500000000000 : ℝ) (500471549563/1000000000000 : ℝ) (250235774787/500000000000 : ℝ) (500471549563/1000000000000 : ℝ) (250235774787/500000000000 : ℝ) (500471549563/1000000000000 : ℝ) (250235774787/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8277/65536 : ℝ))) 6 (500471549563/1000000000000 : ℝ) (250235774787/500000000000 : ℝ) (500471549563/1000000000000 : ℝ) (250235774787/500000000000 : ℝ) (500471549563/1000000000000 : ℝ) (250235774787/500000000000 : ℝ) (500471549563/1000000000000 : ℝ) (250235774787/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8277/65536 : ℝ))) 7 (500471549563/1000000000000 : ℝ) (250235774787/500000000000 : ℝ) (500471549563/1000000000000 : ℝ) (250235774787/500000000000 : ℝ) (500471549563/1000000000000 : ℝ) (250235774787/500000000000 : ℝ) (500471549563/1000000000000 : ℝ) (250235774787/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8277/65536 : ℝ)) hmem 8 (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ) (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8277/65536 : ℝ))) hcmem 8 (500471549563/1000000000000 : ℝ) (250235774787/500000000000 : ℝ) (500471549563/1000000000000 : ℝ) (250235774787/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8277/65536 : ℝ)) (49607648233/50000000000 : ℝ) (992152964663/1000000000000 : ℝ) (500471549563/1000000000000 : ℝ) (250235774787/500000000000 : ℝ) (792356521341/1000000000000 : ℝ) (396178260681/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0327_exp_lower
  have heNumeric : (2054900046173/1000000000000 : ℝ)/4 ≤ Real.exp (-21314148917959/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900046173/1000000000000 : ℝ)/4 ≤ Real.exp ((16553/131072 : ℝ)-(396178260681/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16553/131072 : ℝ) (8277/65536 : ℝ) (396178260681/500000000000 : ℝ) (2054900046173/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0328; no trusted numerical premise.
theorem cover8_leaf0328_exp_radius : (499014247894320969/500000000000000000 : ℝ) ≤ Real.exp ((-33109/2097152 : ℝ)/8) ∧ Real.exp ((-33109/2097152 : ℝ)/8) ≤ (998028495788641939/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33109/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0328_exp_lower : (920113800064953203/1000000000000000000 : ℝ) ≤ Real.exp ((-10657013870843/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657013870843/16000000000000 : ℝ)/8) ≤ (230028450016238301/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657013870843/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0328_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453913799/500000000000 : ℝ) ≤ 4*Real.exp (8277/65536 : ℝ)*Real.exp (-mu (radius 8 (33109/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453913799/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33109/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0328_exp_radius
  have hrNumeric : (19686727389/20000000000 : ℝ) ≤ Real.exp (-33109/2097152 : ℝ) ∧ Real.exp (-33109/2097152 : ℝ) ≤ (984336369451/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (19686727389/20000000000 : ℝ) ≤ (radius 8 (33109/262144 : ℝ)) ∧ (radius 8 (33109/262144 : ℝ)) ≤ (984336369451/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33109/262144 : ℝ)) (19686727389/20000000000 : ℝ) (984336369451/1000000000000 : ℝ) (44075157243/250000000000 : ℝ) (88150314489/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33109/262144 : ℝ)) (19686727389/20000000000 : ℝ) (984336369451/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33109/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (19686727389/20000000000 : ℝ) (984336369451/1000000000000 : ℝ) (39686727389/40000000000 : ℝ) (496084092363/500000000000 : ℝ) (99213727349/100000000000 : ℝ) (248034318373/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33109/262144 : ℝ)) 1 (39686727389/40000000000 : ℝ) (496084092363/500000000000 : ℝ) (99213727349/100000000000 : ℝ) (248034318373/250000000000 : ℝ) (992152729107/1000000000000 : ℝ) (992152729109/1000000000000 : ℝ) (992152728987/1000000000000 : ℝ) (992152728989/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33109/262144 : ℝ)) 2 (992152729107/1000000000000 : ℝ) (992152729109/1000000000000 : ℝ) (992152728987/1000000000000 : ℝ) (992152728989/1000000000000 : ℝ) (992152729047/1000000000000 : ℝ) (992152729049/1000000000000 : ℝ) (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33109/262144 : ℝ)) 3 (992152729047/1000000000000 : ℝ) (992152729049/1000000000000 : ℝ) (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ) (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ) (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33109/262144 : ℝ)) 4 (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ) (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ) (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ) (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33109/262144 : ℝ)) 5 (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ) (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ) (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ) (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33109/262144 : ℝ)) 6 (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ) (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ) (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ) (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33109/262144 : ℝ)) 7 (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ) (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ) (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ) (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33109/262144 : ℝ))) (44075157243/250000000000 : ℝ) (88150314489/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33109/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44075157243/250000000000 : ℝ) (88150314489/500000000000 : ℝ) (294075157243/500000000000 : ℝ) (588150314489/1000000000000 : ℝ) (104970421123/250000000000 : ℝ) (839763369/2000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33109/262144 : ℝ))) 1 (294075157243/500000000000 : ℝ) (588150314489/1000000000000 : ℝ) (104970421123/250000000000 : ℝ) (839763369/2000000000 : ℝ) (504015999489/1000000000000 : ℝ) (100803199899/200000000000 : ℝ) (496944206909/1000000000000 : ℝ) (124236051729/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33109/262144 : ℝ))) 2 (504015999489/1000000000000 : ℝ) (100803199899/200000000000 : ℝ) (496944206909/1000000000000 : ℝ) (124236051729/250000000000 : ℝ) (500480103199/1000000000000 : ℝ) (250240051603/500000000000 : ℝ) (250233806237/500000000000 : ℝ) (500467612481/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33109/262144 : ℝ))) 3 (500480103199/1000000000000 : ℝ) (250240051603/500000000000 : ℝ) (250233806237/500000000000 : ℝ) (500467612481/1000000000000 : ℝ) (125118464459/250000000000 : ℝ) (125118464461/250000000000 : ℝ) (500473857797/1000000000000 : ℝ) (100094771561/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33109/262144 : ℝ))) 4 (125118464459/250000000000 : ℝ) (125118464461/250000000000 : ℝ) (500473857797/1000000000000 : ℝ) (100094771561/200000000000 : ℝ) (62559232227/125000000000 : ℝ) (20018954313/40000000000 : ℝ) (62559232227/125000000000 : ℝ) (20018954313/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33109/262144 : ℝ))) 5 (62559232227/125000000000 : ℝ) (20018954313/40000000000 : ℝ) (62559232227/125000000000 : ℝ) (20018954313/40000000000 : ℝ) (62559232227/125000000000 : ℝ) (20018954313/40000000000 : ℝ) (62559232227/125000000000 : ℝ) (20018954313/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33109/262144 : ℝ))) 6 (62559232227/125000000000 : ℝ) (20018954313/40000000000 : ℝ) (62559232227/125000000000 : ℝ) (20018954313/40000000000 : ℝ) (62559232227/125000000000 : ℝ) (20018954313/40000000000 : ℝ) (62559232227/125000000000 : ℝ) (20018954313/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33109/262144 : ℝ))) 7 (62559232227/125000000000 : ℝ) (20018954313/40000000000 : ℝ) (62559232227/125000000000 : ℝ) (20018954313/40000000000 : ℝ) (62559232227/125000000000 : ℝ) (20018954313/40000000000 : ℝ) (62559232227/125000000000 : ℝ) (20018954313/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33109/262144 : ℝ)) hmem 8 (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ) (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33109/262144 : ℝ))) hcmem 8 (62559232227/125000000000 : ℝ) (20018954313/40000000000 : ℝ) (62559232227/125000000000 : ℝ) (20018954313/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33109/262144 : ℝ)) (496076364523/500000000000 : ℝ) (992152729049/1000000000000 : ℝ) (62559232227/125000000000 : ℝ) (20018954313/40000000000 : ℝ) (792360363981/1000000000000 : ℝ) (396180181999/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0328_exp_lower
  have heNumeric : (1027453913799/500000000000 : ℝ)/4 ≤ Real.exp (-10657013870843/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453913799/500000000000 : ℝ)/4 ≤ Real.exp ((8277/65536 : ℝ)-(396180181999/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8277/65536 : ℝ) (33109/262144 : ℝ) (396180181999/500000000000 : ℝ) (1027453913799/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0329; no trusted numerical premise.
theorem cover8_leaf0329_exp_radius : (62376777268844359/62500000000000000 : ℝ) ≤ Real.exp ((-16555/1048576 : ℝ)/8) ∧ Real.exp ((-16555/1048576 : ℝ)/8) ≤ (199605687260301949/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16555/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0329_exp_lower : (460056898430228711/500000000000000000 : ℝ) ≤ Real.exp ((-42628057266523/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628057266523/64000000000000 : ℝ)/8) ≤ (920113796860457423/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628057266523/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0329_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410981554069/200000000000 : ℝ) ≤ 4*Real.exp (33109/262144 : ℝ)*Real.exp (-mu (radius 8 (16555/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (410981554069/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16555/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0329_exp_radius
  have hrNumeric : (492167950041/500000000000 : ℝ) ≤ Real.exp (-16555/1048576 : ℝ) ∧ Real.exp (-16555/1048576 : ℝ) ≤ (984335900083/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492167950041/500000000000 : ℝ) ≤ (radius 8 (16555/131072 : ℝ)) ∧ (radius 8 (16555/131072 : ℝ)) ≤ (984335900083/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16555/131072 : ℝ)) (492167950041/500000000000 : ℝ) (984335900083/1000000000000 : ℝ) (88151624783/500000000000 : ℝ) (176303249573/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16555/131072 : ℝ)) (492167950041/500000000000 : ℝ) (984335900083/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16555/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492167950041/500000000000 : ℝ) (984335900083/1000000000000 : ℝ) (992167950041/1000000000000 : ℝ) (496083975021/500000000000 : ℝ) (992137036947/1000000000000 : ℝ) (248034259237/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16555/131072 : ℝ)) 1 (992167950041/1000000000000 : ℝ) (496083975021/500000000000 : ℝ) (992137036947/1000000000000 : ℝ) (248034259237/250000000000 : ℝ) (496076246747/500000000000 : ℝ) (198430498699/200000000000 : ℝ) (992152493373/1000000000000 : ℝ) (7937219947/8000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16555/131072 : ℝ)) 2 (496076246747/500000000000 : ℝ) (198430498699/200000000000 : ℝ) (992152493373/1000000000000 : ℝ) (7937219947/8000000000 : ℝ) (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ) (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16555/131072 : ℝ)) 3 (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ) (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ) (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ) (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16555/131072 : ℝ)) 4 (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ) (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ) (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ) (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16555/131072 : ℝ)) 5 (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ) (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ) (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ) (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16555/131072 : ℝ)) 6 (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ) (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ) (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ) (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16555/131072 : ℝ)) 7 (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ) (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ) (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ) (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16555/131072 : ℝ))) (88151624783/500000000000 : ℝ) (176303249573/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16555/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88151624783/500000000000 : ℝ) (176303249573/1000000000000 : ℝ) (588151624783/1000000000000 : ℝ) (588151624787/1000000000000 : ℝ) (209942402557/500000000000 : ℝ) (419884805123/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16555/131072 : ℝ))) 1 (588151624783/1000000000000 : ℝ) (588151624787/1000000000000 : ℝ) (209942402557/500000000000 : ℝ) (419884805123/1000000000000 : ℝ) (126004553737/250000000000 : ℝ) (100803642991/200000000000 : ℝ) (496946607141/1000000000000 : ℝ) (496946607149/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16555/131072 : ℝ))) 2 (126004553737/250000000000 : ℝ) (100803642991/200000000000 : ℝ) (496946607141/1000000000000 : ℝ) (496946607149/1000000000000 : ℝ) (125120602761/250000000000 : ℝ) (125120602763/250000000000 : ℝ) (500469921029/1000000000000 : ℝ) (250234960519/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16555/131072 : ℝ))) 3 (125120602761/250000000000 : ℝ) (125120602763/250000000000 : ℝ) (500469921029/1000000000000 : ℝ) (250234960519/500000000000 : ℝ) (125119041509/250000000000 : ℝ) (100095233209/200000000000 : ℝ) (500476165997/1000000000000 : ℝ) (500476166007/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16555/131072 : ℝ))) 4 (125119041509/250000000000 : ℝ) (100095233209/200000000000 : ℝ) (500476165997/1000000000000 : ℝ) (500476166007/1000000000000 : ℝ) (3909970047/7812500000 : ℝ) (250238083013/500000000000 : ℝ) (3909970047/7812500000 : ℝ) (250238083013/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16555/131072 : ℝ))) 5 (3909970047/7812500000 : ℝ) (250238083013/500000000000 : ℝ) (3909970047/7812500000 : ℝ) (250238083013/500000000000 : ℝ) (3909970047/7812500000 : ℝ) (250238083013/500000000000 : ℝ) (3909970047/7812500000 : ℝ) (250238083013/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16555/131072 : ℝ))) 6 (3909970047/7812500000 : ℝ) (250238083013/500000000000 : ℝ) (3909970047/7812500000 : ℝ) (250238083013/500000000000 : ℝ) (3909970047/7812500000 : ℝ) (250238083013/500000000000 : ℝ) (3909970047/7812500000 : ℝ) (250238083013/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16555/131072 : ℝ))) 7 (3909970047/7812500000 : ℝ) (250238083013/500000000000 : ℝ) (3909970047/7812500000 : ℝ) (250238083013/500000000000 : ℝ) (3909970047/7812500000 : ℝ) (250238083013/500000000000 : ℝ) (3909970047/7812500000 : ℝ) (250238083013/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16555/131072 : ℝ)) hmem 8 (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ) (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16555/131072 : ℝ))) hcmem 8 (3909970047/7812500000 : ℝ) (250238083013/500000000000 : ℝ) (3909970047/7812500000 : ℝ) (250238083013/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16555/131072 : ℝ)) (992152493433/1000000000000 : ℝ) (198430498687/200000000000 : ℝ) (3909970047/7812500000 : ℝ) (250238083013/500000000000 : ℝ) (792364206539/1000000000000 : ℝ) (792364206557/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0329_exp_lower
  have heNumeric : (410981554069/200000000000 : ℝ)/4 ≤ Real.exp (-42628057266523/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410981554069/200000000000 : ℝ)/4 ≤ Real.exp ((33109/262144 : ℝ)-(792364206557/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33109/262144 : ℝ) (16555/131072 : ℝ) (792364206557/1000000000000 : ℝ) (410981554069/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0330; no trusted numerical premise.
theorem cover8_leaf0330_exp_radius : (199605675362876219/200000000000000000 : ℝ) ≤ Real.exp ((-33111/2097152 : ℝ)/8) ∧ Real.exp ((-33111/2097152 : ℝ)/8) ≤ (124753547101797637/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33111/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0330_exp_lower : (920113793664587719/1000000000000000000 : ℝ) ≤ Real.exp ((-21314029522437/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314029522437/32000000000000 : ℝ)/8) ≤ (23002844841614693/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314029522437/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0330_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453856623/500000000000 : ℝ) ≤ 4*Real.exp (16555/131072 : ℝ)*Real.exp (-mu (radius 8 (33111/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453856623/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33111/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0330_exp_radius
  have hrNumeric : (492167715357/500000000000 : ℝ) ≤ Real.exp (-33111/2097152 : ℝ) ∧ Real.exp (-33111/2097152 : ℝ) ≤ (196867086143/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492167715357/500000000000 : ℝ) ≤ (radius 8 (33111/262144 : ℝ)) ∧ (radius 8 (33111/262144 : ℝ)) ≤ (196867086143/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33111/262144 : ℝ)) (492167715357/500000000000 : ℝ) (196867086143/200000000000 : ℝ) (4407646753/25000000000 : ℝ) (176305870127/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33111/262144 : ℝ)) (492167715357/500000000000 : ℝ) (196867086143/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33111/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492167715357/500000000000 : ℝ) (196867086143/200000000000 : ℝ) (992167715357/1000000000000 : ℝ) (496083857679/500000000000 : ℝ) (992136800403/1000000000000 : ℝ) (248034200101/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33111/262144 : ℝ)) 1 (992167715357/1000000000000 : ℝ) (496083857679/500000000000 : ℝ) (992136800403/1000000000000 : ℝ) (248034200101/250000000000 : ℝ) (24803806447/25000000000 : ℝ) (992152257881/1000000000000 : ℝ) (992152257759/1000000000000 : ℝ) (992152257761/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33111/262144 : ℝ)) 2 (24803806447/25000000000 : ℝ) (992152257881/1000000000000 : ℝ) (992152257759/1000000000000 : ℝ) (992152257761/1000000000000 : ℝ) (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ) (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33111/262144 : ℝ)) 3 (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ) (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ) (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ) (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33111/262144 : ℝ)) 4 (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ) (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ) (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ) (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33111/262144 : ℝ)) 5 (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ) (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ) (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ) (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33111/262144 : ℝ)) 6 (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ) (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ) (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ) (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33111/262144 : ℝ)) 7 (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ) (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ) (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ) (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33111/262144 : ℝ))) (4407646753/25000000000 : ℝ) (176305870127/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33111/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4407646753/25000000000 : ℝ) (176305870127/1000000000000 : ℝ) (29407646753/50000000000 : ℝ) (73519116883/125000000000 : ℝ) (83977585133/200000000000 : ℝ) (16795517027/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33111/262144 : ℝ))) 1 (29407646753/50000000000 : ℝ) (73519116883/125000000000 : ℝ) (83977585133/200000000000 : ℝ) (16795517027/40000000000 : ℝ) (252010215181/500000000000 : ℝ) (50402043037/100000000000 : ℝ) (496949007319/1000000000000 : ℝ) (15529656479/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33111/262144 : ℝ))) 2 (252010215181/500000000000 : ℝ) (50402043037/100000000000 : ℝ) (496949007319/1000000000000 : ℝ) (15529656479/31250000000 : ℝ) (12512117971/25000000000 : ℝ) (500484718849/1000000000000 : ℝ) (15639757173/31250000000 : ℝ) (100094445909/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33111/262144 : ℝ))) 3 (12512117971/25000000000 : ℝ) (500484718849/1000000000000 : ℝ) (15639757173/31250000000 : ℝ) (100094445909/200000000000 : ℝ) (125119618547/250000000000 : ℝ) (500478474197/1000000000000 : ℝ) (500478474149/1000000000000 : ℝ) (500478474159/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33111/262144 : ℝ))) 4 (125119618547/250000000000 : ℝ) (500478474197/1000000000000 : ℝ) (500478474149/1000000000000 : ℝ) (500478474159/1000000000000 : ℝ) (62559809271/125000000000 : ℝ) (250239237089/500000000000 : ℝ) (62559809271/125000000000 : ℝ) (250239237089/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33111/262144 : ℝ))) 5 (62559809271/125000000000 : ℝ) (250239237089/500000000000 : ℝ) (62559809271/125000000000 : ℝ) (250239237089/500000000000 : ℝ) (62559809271/125000000000 : ℝ) (250239237089/500000000000 : ℝ) (62559809271/125000000000 : ℝ) (250239237089/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33111/262144 : ℝ))) 6 (62559809271/125000000000 : ℝ) (250239237089/500000000000 : ℝ) (62559809271/125000000000 : ℝ) (250239237089/500000000000 : ℝ) (62559809271/125000000000 : ℝ) (250239237089/500000000000 : ℝ) (62559809271/125000000000 : ℝ) (250239237089/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33111/262144 : ℝ))) 7 (62559809271/125000000000 : ℝ) (250239237089/500000000000 : ℝ) (62559809271/125000000000 : ℝ) (250239237089/500000000000 : ℝ) (62559809271/125000000000 : ℝ) (250239237089/500000000000 : ℝ) (62559809271/125000000000 : ℝ) (250239237089/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33111/262144 : ℝ)) hmem 8 (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ) (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33111/262144 : ℝ))) hcmem 8 (62559809271/125000000000 : ℝ) (250239237089/500000000000 : ℝ) (62559809271/125000000000 : ℝ) (250239237089/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33111/262144 : ℝ)) (992152257819/1000000000000 : ℝ) (992152257821/1000000000000 : ℝ) (62559809271/125000000000 : ℝ) (250239237089/500000000000 : ℝ) (396184024511/500000000000 : ℝ) (792368049041/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0330_exp_lower
  have heNumeric : (1027453856623/500000000000 : ℝ)/4 ≤ Real.exp (-21314029522437/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453856623/500000000000 : ℝ)/4 ≤ Real.exp ((16555/131072 : ℝ)-(792368049041/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16555/131072 : ℝ) (33111/262144 : ℝ) (792368049041/1000000000000 : ℝ) (1027453856623/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0331; no trusted numerical premise.
theorem cover8_leaf0331_exp_radius : (124753539665906999/125000000000000000 : ℝ) ≤ Real.exp ((-4139/262144 : ℝ)/8) ∧ Real.exp ((-4139/262144 : ℝ)/8) ≤ (998028317327255993/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4139/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0331_exp_lower : (920113790478609251/1000000000000000000 : ℝ) ≤ Real.exp ((-42628060817721/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628060817721/64000000000000 : ℝ)/8) ≤ (230028447619652313/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628060817721/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0331_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907656323/1000000000000 : ℝ) ≤ 4*Real.exp (33111/262144 : ℝ)*Real.exp (-mu (radius 8 (4139/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907656323/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4139/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0331_exp_radius
  have hrNumeric : (984334961347/1000000000000 : ℝ) ≤ Real.exp (-4139/262144 : ℝ) ∧ Real.exp (-4139/262144 : ℝ) ≤ (246083740337/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984334961347/1000000000000 : ℝ) ≤ (radius 8 (4139/32768 : ℝ)) ∧ (radius 8 (4139/32768 : ℝ)) ≤ (246083740337/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4139/32768 : ℝ)) (984334961347/1000000000000 : ℝ) (246083740337/250000000000 : ℝ) (176308490629/1000000000000 : ℝ) (44077122659/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4139/32768 : ℝ)) (984334961347/1000000000000 : ℝ) (246083740337/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4139/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984334961347/1000000000000 : ℝ) (246083740337/250000000000 : ℝ) (992167480673/1000000000000 : ℝ) (496083740337/500000000000 : ℝ) (992136563859/1000000000000 : ℝ) (992136563861/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4139/32768 : ℝ)) 1 (992167480673/1000000000000 : ℝ) (496083740337/500000000000 : ℝ) (992136563859/1000000000000 : ℝ) (992136563861/1000000000000 : ℝ) (496076011133/500000000000 : ℝ) (248038005567/250000000000 : ℝ) (198430404429/200000000000 : ℝ) (248038005537/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4139/32768 : ℝ)) 2 (496076011133/500000000000 : ℝ) (248038005567/250000000000 : ℝ) (198430404429/200000000000 : ℝ) (248038005537/250000000000 : ℝ) (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ) (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4139/32768 : ℝ)) 3 (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ) (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ) (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ) (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4139/32768 : ℝ)) 4 (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ) (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ) (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ) (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4139/32768 : ℝ)) 5 (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ) (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ) (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ) (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4139/32768 : ℝ)) 6 (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ) (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ) (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ) (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4139/32768 : ℝ)) 7 (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ) (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ) (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ) (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4139/32768 : ℝ))) (176308490629/1000000000000 : ℝ) (44077122659/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4139/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176308490629/1000000000000 : ℝ) (44077122659/250000000000 : ℝ) (294077122657/500000000000 : ℝ) (294077122659/500000000000 : ℝ) (20994552307/50000000000 : ℝ) (419891046149/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4139/32768 : ℝ))) 1 (294077122657/500000000000 : ℝ) (294077122659/500000000000 : ℝ) (20994552307/50000000000 : ℝ) (419891046149/1000000000000 : ℝ) (504022645727/1000000000000 : ℝ) (252011322867/500000000000 : ℝ) (496951407439/1000000000000 : ℝ) (496951407447/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4139/32768 : ℝ))) 2 (504022645727/1000000000000 : ℝ) (252011322867/500000000000 : ℝ) (496951407439/1000000000000 : ℝ) (496951407447/1000000000000 : ℝ) (500487026583/1000000000000 : ℝ) (500487026591/1000000000000 : ℝ) (125118634497/250000000000 : ℝ) (500474537997/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4139/32768 : ℝ))) 3 (500487026583/1000000000000 : ℝ) (500487026591/1000000000000 : ℝ) (125118634497/250000000000 : ℝ) (500474537997/1000000000000 : ℝ) (100096156457/200000000000 : ℝ) (250240391147/500000000000 : ℝ) (250240391123/500000000000 : ℝ) (31280048891/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4139/32768 : ℝ))) 4 (100096156457/200000000000 : ℝ) (250240391147/500000000000 : ℝ) (250240391123/500000000000 : ℝ) (31280048891/62500000000 : ℝ) (100096156453/200000000000 : ℝ) (20019231291/40000000000 : ℝ) (100096156453/200000000000 : ℝ) (20019231291/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4139/32768 : ℝ))) 5 (100096156453/200000000000 : ℝ) (20019231291/40000000000 : ℝ) (100096156453/200000000000 : ℝ) (20019231291/40000000000 : ℝ) (100096156453/200000000000 : ℝ) (20019231291/40000000000 : ℝ) (100096156453/200000000000 : ℝ) (20019231291/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4139/32768 : ℝ))) 6 (100096156453/200000000000 : ℝ) (20019231291/40000000000 : ℝ) (100096156453/200000000000 : ℝ) (20019231291/40000000000 : ℝ) (100096156453/200000000000 : ℝ) (20019231291/40000000000 : ℝ) (100096156453/200000000000 : ℝ) (20019231291/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4139/32768 : ℝ))) 7 (100096156453/200000000000 : ℝ) (20019231291/40000000000 : ℝ) (100096156453/200000000000 : ℝ) (20019231291/40000000000 : ℝ) (100096156453/200000000000 : ℝ) (20019231291/40000000000 : ℝ) (100096156453/200000000000 : ℝ) (20019231291/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4139/32768 : ℝ)) hmem 8 (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ) (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4139/32768 : ℝ))) hcmem 8 (100096156453/200000000000 : ℝ) (20019231291/40000000000 : ℝ) (100096156453/200000000000 : ℝ) (20019231291/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4139/32768 : ℝ)) (198430404441/200000000000 : ℝ) (15502375347/15625000000 : ℝ) (100096156453/200000000000 : ℝ) (20019231291/40000000000 : ℝ) (39618594571/50000000000 : ℝ) (792371891439/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0331_exp_lower
  have heNumeric : (2054907656323/1000000000000 : ℝ)/4 ≤ Real.exp (-42628060817721/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907656323/1000000000000 : ℝ)/4 ≤ Real.exp ((33111/262144 : ℝ)-(792371891439/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33111/262144 : ℝ) (4139/32768 : ℝ) (792371891439/1000000000000 : ℝ) (2054907656323/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0332; no trusted numerical premise.
theorem cover8_leaf0332_exp_radius : (199605651568026887/200000000000000000 : ℝ) ≤ Real.exp ((-33113/2097152 : ℝ)/8) ∧ Real.exp ((-33113/2097152 : ℝ)/8) ≤ (249507064460033609/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33113/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0332_exp_lower : (36804551492022671/40000000000000000 : ℝ) ≤ Real.exp ((-5328507823269/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328507823269/8000000000000 : ℝ)/8) ≤ (115014223412570847/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328507823269/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0332_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907599543/1000000000000 : ℝ) ≤ 4*Real.exp (4139/32768 : ℝ)*Real.exp (-mu (radius 8 (33113/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907599543/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33113/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0332_exp_radius
  have hrNumeric : (984334491979/1000000000000 : ℝ) ≤ Real.exp (-33113/2097152 : ℝ) ∧ Real.exp (-33113/2097152 : ℝ) ≤ (49216724599/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984334491979/1000000000000 : ℝ) ≤ (radius 8 (33113/262144 : ℝ)) ∧ (radius 8 (33113/262144 : ℝ)) ≤ (49216724599/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33113/262144 : ℝ)) (984334491979/1000000000000 : ℝ) (49216724599/50000000000 : ℝ) (176311111103/1000000000000 : ℝ) (176311111109/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33113/262144 : ℝ)) (984334491979/1000000000000 : ℝ) (49216724599/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33113/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984334491979/1000000000000 : ℝ) (49216724599/50000000000 : ℝ) (992167245989/1000000000000 : ℝ) (99216724599/100000000000 : ℝ) (198427265463/200000000000 : ℝ) (248034081829/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33113/262144 : ℝ)) 1 (992167245989/1000000000000 : ℝ) (99216724599/100000000000 : ℝ) (198427265463/200000000000 : ℝ) (248034081829/250000000000 : ℝ) (248037946663/250000000000 : ℝ) (992151786653/1000000000000 : ℝ) (992151786531/1000000000000 : ℝ) (992151786533/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33113/262144 : ℝ)) 2 (248037946663/250000000000 : ℝ) (992151786653/1000000000000 : ℝ) (992151786531/1000000000000 : ℝ) (992151786533/1000000000000 : ℝ) (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ) (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33113/262144 : ℝ)) 3 (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ) (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ) (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ) (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33113/262144 : ℝ)) 4 (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ) (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ) (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ) (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33113/262144 : ℝ)) 5 (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ) (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ) (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ) (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33113/262144 : ℝ)) 6 (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ) (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ) (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ) (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33113/262144 : ℝ)) 7 (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ) (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ) (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ) (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33113/262144 : ℝ))) (176311111103/1000000000000 : ℝ) (176311111109/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33113/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176311111103/1000000000000 : ℝ) (176311111109/1000000000000 : ℝ) (588155555551/1000000000000 : ℝ) (117631111111/200000000000 : ℝ) (8397883331/20000000000 : ℝ) (209947083279/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33113/262144 : ℝ))) 1 (588155555551/1000000000000 : ℝ) (117631111111/200000000000 : ℝ) (8397883331/20000000000 : ℝ) (209947083279/500000000000 : ℝ) (10080497221/20000000000 : ℝ) (504024861057/1000000000000 : ℝ) (496953807511/1000000000000 : ℝ) (248476903759/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33113/262144 : ℝ))) 2 (10080497221/20000000000 : ℝ) (504024861057/1000000000000 : ℝ) (496953807511/1000000000000 : ℝ) (248476903759/500000000000 : ℝ) (12512233357/25000000000 : ℝ) (31280583393/62500000000 : ℝ) (125119211599/250000000000 : ℝ) (125119211601/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33113/262144 : ℝ))) 3 (12512233357/25000000000 : ℝ) (31280583393/62500000000 : ℝ) (125119211599/250000000000 : ℝ) (125119211601/250000000000 : ℝ) (250241545169/500000000000 : ℝ) (250241545173/500000000000 : ℝ) (500483090299/1000000000000 : ℝ) (125120772577/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33113/262144 : ℝ))) 4 (250241545169/500000000000 : ℝ) (250241545173/500000000000 : ℝ) (500483090299/1000000000000 : ℝ) (125120772577/250000000000 : ℝ) (250241545159/500000000000 : ℝ) (500483090327/1000000000000 : ℝ) (250241545159/500000000000 : ℝ) (500483090327/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33113/262144 : ℝ))) 5 (250241545159/500000000000 : ℝ) (500483090327/1000000000000 : ℝ) (250241545159/500000000000 : ℝ) (500483090327/1000000000000 : ℝ) (250241545159/500000000000 : ℝ) (500483090327/1000000000000 : ℝ) (250241545159/500000000000 : ℝ) (500483090327/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33113/262144 : ℝ))) 6 (250241545159/500000000000 : ℝ) (500483090327/1000000000000 : ℝ) (250241545159/500000000000 : ℝ) (500483090327/1000000000000 : ℝ) (250241545159/500000000000 : ℝ) (500483090327/1000000000000 : ℝ) (250241545159/500000000000 : ℝ) (500483090327/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33113/262144 : ℝ))) 7 (250241545159/500000000000 : ℝ) (500483090327/1000000000000 : ℝ) (250241545159/500000000000 : ℝ) (500483090327/1000000000000 : ℝ) (250241545159/500000000000 : ℝ) (500483090327/1000000000000 : ℝ) (250241545159/500000000000 : ℝ) (500483090327/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33113/262144 : ℝ)) hmem 8 (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ) (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33113/262144 : ℝ))) hcmem 8 (250241545159/500000000000 : ℝ) (500483090327/1000000000000 : ℝ) (250241545159/500000000000 : ℝ) (500483090327/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33113/262144 : ℝ)) (992151786591/1000000000000 : ℝ) (992151786593/1000000000000 : ℝ) (250241545159/500000000000 : ℝ) (500483090327/1000000000000 : ℝ) (792375733751/1000000000000 : ℝ) (99046966721/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0332_exp_lower
  have heNumeric : (2054907599543/1000000000000 : ℝ)/4 ≤ Real.exp (-5328507823269/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907599543/1000000000000 : ℝ)/4 ≤ Real.exp ((4139/32768 : ℝ)-(99046966721/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4139/32768 : ℝ) (33113/262144 : ℝ) (99046966721/125000000000 : ℝ) (2054907599543/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0333; no trusted numerical premise.
theorem cover8_leaf0333_exp_radius : (998028198353016423/1000000000000000000 : ℝ) ≤ Real.exp ((-16557/1048576 : ℝ)/8) ∧ Real.exp ((-16557/1048576 : ℝ)/8) ≤ (124753524794127053/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16557/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0333_exp_lower : (28753555754130797/31250000000000000 : ℝ) ≤ Real.exp ((-42628064349207/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628064349207/64000000000000 : ℝ)/8) ≤ (184022756826437101/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628064349207/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0333_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453771467/500000000000 : ℝ) ≤ 4*Real.exp (33113/262144 : ℝ)*Real.exp (-mu (radius 8 (16557/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453771467/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16557/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0333_exp_radius
  have hrNumeric : (246083505653/250000000000 : ℝ) ≤ Real.exp (-16557/1048576 : ℝ) ∧ Real.exp (-16557/1048576 : ℝ) ≤ (984334022613/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246083505653/250000000000 : ℝ) ≤ (radius 8 (16557/131072 : ℝ)) ∧ (radius 8 (16557/131072 : ℝ)) ≤ (984334022613/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16557/131072 : ℝ)) (246083505653/250000000000 : ℝ) (984334022613/1000000000000 : ℝ) (176313731531/1000000000000 : ℝ) (176313731537/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16557/131072 : ℝ)) (246083505653/250000000000 : ℝ) (984334022613/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16557/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246083505653/250000000000 : ℝ) (984334022613/1000000000000 : ℝ) (496083505653/500000000000 : ℝ) (992167011307/1000000000000 : ℝ) (992136090771/1000000000000 : ℝ) (992136090773/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16557/131072 : ℝ)) 1 (496083505653/500000000000 : ℝ) (992167011307/1000000000000 : ℝ) (992136090771/1000000000000 : ℝ) (992136090773/1000000000000 : ℝ) (496075775519/500000000000 : ℝ) (3100473597/3125000000 : ℝ) (496075775459/500000000000 : ℝ) (24803788773/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16557/131072 : ℝ)) 2 (496075775519/500000000000 : ℝ) (3100473597/3125000000 : ℝ) (496075775459/500000000000 : ℝ) (24803788773/25000000000 : ℝ) (496075775489/500000000000 : ℝ) (49607577549/50000000000 : ℝ) (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16557/131072 : ℝ)) 3 (496075775489/500000000000 : ℝ) (49607577549/50000000000 : ℝ) (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ) (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ) (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16557/131072 : ℝ)) 4 (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ) (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ) (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ) (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16557/131072 : ℝ)) 5 (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ) (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ) (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ) (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16557/131072 : ℝ)) 6 (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ) (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ) (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ) (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16557/131072 : ℝ)) 7 (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ) (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ) (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ) (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16557/131072 : ℝ))) (176313731531/1000000000000 : ℝ) (176313731537/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16557/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176313731531/1000000000000 : ℝ) (176313731537/1000000000000 : ℝ) (117631373153/200000000000 : ℝ) (588156865769/1000000000000 : ℝ) (209948643441/500000000000 : ℝ) (41989728689/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16557/131072 : ℝ))) 1 (117631373153/200000000000 : ℝ) (588156865769/1000000000000 : ℝ) (209948643441/500000000000 : ℝ) (41989728689/100000000000 : ℝ) (504027076323/1000000000000 : ℝ) (50402707633/100000000000 : ℝ) (496956207523/1000000000000 : ℝ) (49695620753/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16557/131072 : ℝ))) 2 (504027076323/1000000000000 : ℝ) (50402707633/100000000000 : ℝ) (496956207523/1000000000000 : ℝ) (49695620753/100000000000 : ℝ) (500491641923/1000000000000 : ℝ) (50049164193/100000000000 : ℝ) (500479154749/1000000000000 : ℝ) (500479154757/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16557/131072 : ℝ))) 3 (500491641923/1000000000000 : ℝ) (50049164193/100000000000 : ℝ) (500479154749/1000000000000 : ℝ) (500479154757/1000000000000 : ℝ) (7820084349/15625000000 : ℝ) (62560674793/125000000000 : ℝ) (500485398297/1000000000000 : ℝ) (100097079661/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16557/131072 : ℝ))) 4 (7820084349/15625000000 : ℝ) (62560674793/125000000000 : ℝ) (500485398297/1000000000000 : ℝ) (100097079661/200000000000 : ℝ) (125121349579/250000000000 : ℝ) (20019415933/40000000000 : ℝ) (125121349579/250000000000 : ℝ) (20019415933/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16557/131072 : ℝ))) 5 (125121349579/250000000000 : ℝ) (20019415933/40000000000 : ℝ) (125121349579/250000000000 : ℝ) (20019415933/40000000000 : ℝ) (125121349579/250000000000 : ℝ) (20019415933/40000000000 : ℝ) (125121349579/250000000000 : ℝ) (20019415933/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16557/131072 : ℝ))) 6 (125121349579/250000000000 : ℝ) (20019415933/40000000000 : ℝ) (125121349579/250000000000 : ℝ) (20019415933/40000000000 : ℝ) (125121349579/250000000000 : ℝ) (20019415933/40000000000 : ℝ) (125121349579/250000000000 : ℝ) (20019415933/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16557/131072 : ℝ))) 7 (125121349579/250000000000 : ℝ) (20019415933/40000000000 : ℝ) (125121349579/250000000000 : ℝ) (20019415933/40000000000 : ℝ) (125121349579/250000000000 : ℝ) (20019415933/40000000000 : ℝ) (125121349579/250000000000 : ℝ) (20019415933/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16557/131072 : ℝ)) hmem 8 (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ) (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16557/131072 : ℝ))) hcmem 8 (125121349579/250000000000 : ℝ) (20019415933/40000000000 : ℝ) (125121349579/250000000000 : ℝ) (20019415933/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16557/131072 : ℝ)) (992151550977/1000000000000 : ℝ) (49607577549/50000000000 : ℝ) (125121349579/250000000000 : ℝ) (20019415933/40000000000 : ℝ) (158475915199/200000000000 : ℝ) (792379576013/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0333_exp_lower
  have heNumeric : (1027453771467/500000000000 : ℝ)/4 ≤ Real.exp (-42628064349207/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453771467/500000000000 : ℝ)/4 ≤ Real.exp ((33113/262144 : ℝ)-(792379576013/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33113/262144 : ℝ) (16557/131072 : ℝ) (792379576013/1000000000000 : ℝ) (1027453771467/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0334; no trusted numerical premise.
theorem cover8_leaf0334_exp_radius : (499014069432950979/500000000000000000 : ℝ) ≤ Real.exp ((-33115/2097152 : ℝ)/8) ∧ Real.exp ((-33115/2097152 : ℝ)/8) ≤ (998028138865901959/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33115/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0334_exp_lower : (3594194456925353/3906250000000000 : ℝ) ≤ Real.exp ((-21314033053603/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314033053603/32000000000000 : ℝ)/8) ≤ (920113780972890369/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314033053603/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0334_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907486489/1000000000000 : ℝ) ≤ 4*Real.exp (16557/131072 : ℝ)*Real.exp (-mu (radius 8 (33115/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907486489/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33115/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0334_exp_radius
  have hrNumeric : (196866710649/200000000000 : ℝ) ≤ Real.exp (-33115/2097152 : ℝ) ∧ Real.exp (-33115/2097152 : ℝ) ≤ (492166776623/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196866710649/200000000000 : ℝ) ≤ (radius 8 (33115/262144 : ℝ)) ∧ (radius 8 (33115/262144 : ℝ)) ≤ (492166776623/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33115/262144 : ℝ)) (196866710649/200000000000 : ℝ) (492166776623/500000000000 : ℝ) (176316351919/1000000000000 : ℝ) (7052654077/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33115/262144 : ℝ)) (196866710649/200000000000 : ℝ) (492166776623/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33115/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196866710649/200000000000 : ℝ) (492166776623/500000000000 : ℝ) (496083388311/500000000000 : ℝ) (992166776623/1000000000000 : ℝ) (248033963557/250000000000 : ℝ) (992135854229/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33115/262144 : ℝ)) 1 (496083388311/500000000000 : ℝ) (992166776623/1000000000000 : ℝ) (248033963557/250000000000 : ℝ) (992135854229/1000000000000 : ℝ) (39686052617/40000000000 : ℝ) (496075657713/500000000000 : ℝ) (124018914413/125000000000 : ℝ) (496075657653/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33115/262144 : ℝ)) 2 (39686052617/40000000000 : ℝ) (496075657713/500000000000 : ℝ) (124018914413/125000000000 : ℝ) (496075657653/500000000000 : ℝ) (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ) (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33115/262144 : ℝ)) 3 (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ) (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ) (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ) (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33115/262144 : ℝ)) 4 (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ) (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ) (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ) (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33115/262144 : ℝ)) 5 (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ) (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ) (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ) (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33115/262144 : ℝ)) 6 (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ) (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ) (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ) (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33115/262144 : ℝ)) 7 (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ) (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ) (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ) (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33115/262144 : ℝ))) (176316351919/1000000000000 : ℝ) (7052654077/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33115/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176316351919/1000000000000 : ℝ) (7052654077/40000000000 : ℝ) (588158175959/1000000000000 : ℝ) (588158175963/1000000000000 : ℝ) (419900407143/1000000000000 : ℝ) (419900407151/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33115/262144 : ℝ))) 1 (588158175959/1000000000000 : ℝ) (588158175963/1000000000000 : ℝ) (419900407143/1000000000000 : ℝ) (419900407151/1000000000000 : ℝ) (504029291551/1000000000000 : ℝ) (504029291557/1000000000000 : ℝ) (496958607481/1000000000000 : ℝ) (3882489121/7812500000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33115/262144 : ℝ))) 2 (504029291551/1000000000000 : ℝ) (504029291557/1000000000000 : ℝ) (496958607481/1000000000000 : ℝ) (3882489121/7812500000 : ℝ) (125123487379/250000000000 : ℝ) (500493949523/1000000000000 : ℝ) (125120365763/250000000000 : ℝ) (500481463059/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33115/262144 : ℝ))) 3 (125123487379/250000000000 : ℝ) (500493949523/1000000000000 : ℝ) (125120365763/250000000000 : ℝ) (500481463059/1000000000000 : ℝ) (125121926571/250000000000 : ℝ) (500487706291/1000000000000 : ℝ) (100097541249/200000000000 : ℝ) (500487706253/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33115/262144 : ℝ))) 4 (125121926571/250000000000 : ℝ) (500487706291/1000000000000 : ℝ) (100097541249/200000000000 : ℝ) (500487706253/1000000000000 : ℝ) (62560963283/125000000000 : ℝ) (15640240821/31250000000 : ℝ) (62560963283/125000000000 : ℝ) (15640240821/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33115/262144 : ℝ))) 5 (62560963283/125000000000 : ℝ) (15640240821/31250000000 : ℝ) (62560963283/125000000000 : ℝ) (15640240821/31250000000 : ℝ) (62560963283/125000000000 : ℝ) (15640240821/31250000000 : ℝ) (62560963283/125000000000 : ℝ) (15640240821/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33115/262144 : ℝ))) 6 (62560963283/125000000000 : ℝ) (15640240821/31250000000 : ℝ) (62560963283/125000000000 : ℝ) (15640240821/31250000000 : ℝ) (62560963283/125000000000 : ℝ) (15640240821/31250000000 : ℝ) (62560963283/125000000000 : ℝ) (15640240821/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33115/262144 : ℝ))) 7 (62560963283/125000000000 : ℝ) (15640240821/31250000000 : ℝ) (62560963283/125000000000 : ℝ) (15640240821/31250000000 : ℝ) (62560963283/125000000000 : ℝ) (15640240821/31250000000 : ℝ) (62560963283/125000000000 : ℝ) (15640240821/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33115/262144 : ℝ)) hmem 8 (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ) (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33115/262144 : ℝ))) hcmem 8 (62560963283/125000000000 : ℝ) (15640240821/31250000000 : ℝ) (62560963283/125000000000 : ℝ) (15640240821/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33115/262144 : ℝ)) (248037828841/250000000000 : ℝ) (496075657683/500000000000 : ℝ) (62560963283/125000000000 : ℝ) (15640240821/31250000000 : ℝ) (792383418163/1000000000000 : ℝ) (792383418179/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0334_exp_lower
  have heNumeric : (2054907486489/1000000000000 : ℝ)/4 ≤ Real.exp (-21314033053603/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907486489/1000000000000 : ℝ)/4 ≤ Real.exp ((16557/131072 : ℝ)-(792383418179/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16557/131072 : ℝ) (33115/262144 : ℝ) (792383418179/1000000000000 : ℝ) (2054907486489/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0335; no trusted numerical premise.
theorem cover8_leaf0335_exp_radius : (998028079378791037/1000000000000000000 : ℝ) ≤ Real.exp ((-8279/524288 : ℝ)/8) ∧ Real.exp ((-8279/524288 : ℝ)/8) ≤ (499014039689395519/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8279/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0335_exp_lower : (230028444455584081/250000000000000000 : ℝ) ≤ Real.exp ((-42628067860341/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628067860341/64000000000000 : ℝ)/8) ≤ (36804551112893453/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628067860341/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0335_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907430199/1000000000000 : ℝ) ≤ 4*Real.exp (33115/262144 : ℝ)*Real.exp (-mu (radius 8 (8279/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907430199/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8279/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0335_exp_radius
  have hrNumeric : (492166541939/500000000000 : ℝ) ≤ Real.exp (-8279/524288 : ℝ) ∧ Real.exp (-8279/524288 : ℝ) ≤ (984333083879/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492166541939/500000000000 : ℝ) ≤ (radius 8 (8279/65536 : ℝ)) ∧ (radius 8 (8279/65536 : ℝ)) ≤ (984333083879/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8279/65536 : ℝ)) (492166541939/500000000000 : ℝ) (984333083879/1000000000000 : ℝ) (88159486133/500000000000 : ℝ) (176318972273/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8279/65536 : ℝ)) (492166541939/500000000000 : ℝ) (984333083879/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8279/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492166541939/500000000000 : ℝ) (984333083879/1000000000000 : ℝ) (992166541939/1000000000000 : ℝ) (49608327097/50000000000 : ℝ) (248033904421/250000000000 : ℝ) (198427123537/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8279/65536 : ℝ)) 1 (992166541939/1000000000000 : ℝ) (49608327097/50000000000 : ℝ) (248033904421/250000000000 : ℝ) (198427123537/200000000000 : ℝ) (992151079811/1000000000000 : ℝ) (992151079813/1000000000000 : ℝ) (992151079691/1000000000000 : ℝ) (992151079693/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8279/65536 : ℝ)) 2 (992151079811/1000000000000 : ℝ) (992151079813/1000000000000 : ℝ) (992151079691/1000000000000 : ℝ) (992151079693/1000000000000 : ℝ) (992151079751/1000000000000 : ℝ) (992151079753/1000000000000 : ℝ) (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8279/65536 : ℝ)) 3 (992151079751/1000000000000 : ℝ) (992151079753/1000000000000 : ℝ) (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ) (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ) (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8279/65536 : ℝ)) 4 (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ) (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ) (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ) (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8279/65536 : ℝ)) 5 (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ) (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ) (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ) (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8279/65536 : ℝ)) 6 (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ) (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ) (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ) (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8279/65536 : ℝ)) 7 (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ) (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ) (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ) (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8279/65536 : ℝ))) (88159486133/500000000000 : ℝ) (176318972273/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8279/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88159486133/500000000000 : ℝ) (176318972273/1000000000000 : ℝ) (588159486133/1000000000000 : ℝ) (588159486137/1000000000000 : ℝ) (104975881833/250000000000 : ℝ) (419903527341/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8279/65536 : ℝ))) 1 (588159486133/1000000000000 : ℝ) (588159486137/1000000000000 : ℝ) (104975881833/250000000000 : ℝ) (419903527341/1000000000000 : ℝ) (126007876683/250000000000 : ℝ) (504031506739/1000000000000 : ℝ) (62120125923/125000000000 : ℝ) (15530031481/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8279/65536 : ℝ))) 2 (126007876683/250000000000 : ℝ) (504031506739/1000000000000 : ℝ) (62120125923/125000000000 : ℝ) (15530031481/31250000000 : ℝ) (250248128529/500000000000 : ℝ) (250248128533/500000000000 : ℝ) (62560471413/125000000000 : ℝ) (31280235707/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8279/65536 : ℝ))) 3 (250248128529/500000000000 : ℝ) (250248128533/500000000000 : ℝ) (62560471413/125000000000 : ℝ) (31280235707/62500000000 : ℝ) (500490014181/1000000000000 : ℝ) (500490014189/1000000000000 : ℝ) (250245007071/500000000000 : ℝ) (500490014151/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8279/65536 : ℝ))) 4 (500490014181/1000000000000 : ℝ) (500490014189/1000000000000 : ℝ) (250245007071/500000000000 : ℝ) (500490014151/1000000000000 : ℝ) (500490014161/1000000000000 : ℝ) (50049001417/100000000000 : ℝ) (500490014161/1000000000000 : ℝ) (50049001417/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8279/65536 : ℝ))) 5 (500490014161/1000000000000 : ℝ) (50049001417/100000000000 : ℝ) (500490014161/1000000000000 : ℝ) (50049001417/100000000000 : ℝ) (500490014161/1000000000000 : ℝ) (50049001417/100000000000 : ℝ) (500490014161/1000000000000 : ℝ) (50049001417/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8279/65536 : ℝ))) 6 (500490014161/1000000000000 : ℝ) (50049001417/100000000000 : ℝ) (500490014161/1000000000000 : ℝ) (50049001417/100000000000 : ℝ) (500490014161/1000000000000 : ℝ) (50049001417/100000000000 : ℝ) (500490014161/1000000000000 : ℝ) (50049001417/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8279/65536 : ℝ))) 7 (500490014161/1000000000000 : ℝ) (50049001417/100000000000 : ℝ) (500490014161/1000000000000 : ℝ) (50049001417/100000000000 : ℝ) (500490014161/1000000000000 : ℝ) (50049001417/100000000000 : ℝ) (500490014161/1000000000000 : ℝ) (50049001417/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8279/65536 : ℝ)) hmem 8 (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ) (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8279/65536 : ℝ))) hcmem 8 (500490014161/1000000000000 : ℝ) (50049001417/100000000000 : ℝ) (500490014161/1000000000000 : ℝ) (50049001417/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8279/65536 : ℝ)) (3968604319/4000000000 : ℝ) (992151079753/1000000000000 : ℝ) (500490014161/1000000000000 : ℝ) (50049001417/100000000000 : ℝ) (198096815063/250000000000 : ℝ) (792387260269/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0335_exp_lower
  have heNumeric : (2054907430199/1000000000000 : ℝ)/4 ≤ Real.exp (-42628067860341/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907430199/1000000000000 : ℝ)/4 ≤ Real.exp ((33115/262144 : ℝ)-(792387260269/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33115/262144 : ℝ) (8279/65536 : ℝ) (792387260269/1000000000000 : ℝ) (2054907430199/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0336; no trusted numerical premise.
theorem cover8_leaf0336_exp_radius : (998028019891683663/1000000000000000000 : ℝ) ≤ Real.exp ((-33117/2097152 : ℝ)/8) ∧ Real.exp ((-33117/2097152 : ℝ)/8) ≤ (62376751243230229/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33117/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0336_exp_lower : (184022754936288697/200000000000000000 : ℝ) ≤ Real.exp ((-426280696081/640000000000 : ℝ)/8) ∧ Real.exp ((-426280696081/640000000000 : ℝ)/8) ≤ (460056887340721743/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-426280696081/640000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0336_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453687041/500000000000 : ℝ) ≤ 4*Real.exp (8279/65536 : ℝ)*Real.exp (-mu (radius 8 (33117/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453687041/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33117/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0336_exp_radius
  have hrNumeric : (61520788407/62500000000 : ℝ) ≤ Real.exp (-33117/2097152 : ℝ) ∧ Real.exp (-33117/2097152 : ℝ) ≤ (984332614513/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61520788407/62500000000 : ℝ) ≤ (radius 8 (33117/262144 : ℝ)) ∧ (radius 8 (33117/262144 : ℝ)) ≤ (984332614513/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33117/262144 : ℝ)) (61520788407/62500000000 : ℝ) (984332614513/1000000000000 : ℝ) (22040199071/125000000000 : ℝ) (7052863703/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33117/262144 : ℝ)) (61520788407/62500000000 : ℝ) (984332614513/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33117/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61520788407/62500000000 : ℝ) (984332614513/1000000000000 : ℝ) (124020788407/125000000000 : ℝ) (992166307257/1000000000000 : ℝ) (992135381141/1000000000000 : ℝ) (496067690571/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33117/262144 : ℝ)) 1 (124020788407/125000000000 : ℝ) (992166307257/1000000000000 : ℝ) (992135381141/1000000000000 : ℝ) (496067690571/500000000000 : ℝ) (496075422099/500000000000 : ℝ) (4960754221/5000000000 : ℝ) (496075422039/500000000000 : ℝ) (12401885551/12500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33117/262144 : ℝ)) 2 (496075422099/500000000000 : ℝ) (4960754221/5000000000 : ℝ) (496075422039/500000000000 : ℝ) (12401885551/12500000000 : ℝ) (496075422069/500000000000 : ℝ) (49607542207/50000000000 : ℝ) (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33117/262144 : ℝ)) 3 (496075422069/500000000000 : ℝ) (49607542207/50000000000 : ℝ) (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ) (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ) (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33117/262144 : ℝ)) 4 (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ) (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ) (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ) (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33117/262144 : ℝ)) 5 (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ) (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ) (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ) (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33117/262144 : ℝ)) 6 (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ) (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ) (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ) (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33117/262144 : ℝ)) 7 (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ) (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ) (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ) (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33117/262144 : ℝ))) (22040199071/125000000000 : ℝ) (7052863703/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33117/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22040199071/125000000000 : ℝ) (7052863703/40000000000 : ℝ) (147040199071/250000000000 : ℝ) (4595006221/7812500000 : ℝ) (104976661861/250000000000 : ℝ) (419906647453/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33117/262144 : ℝ))) 1 (147040199071/250000000000 : ℝ) (4595006221/7812500000 : ℝ) (104976661861/250000000000 : ℝ) (419906647453/1000000000000 : ℝ) (63004215233/125000000000 : ℝ) (504033721871/1000000000000 : ℝ) (496963407229/1000000000000 : ℝ) (496963407237/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33117/262144 : ℝ))) 2 (63004215233/125000000000 : ℝ) (504033721871/1000000000000 : ℝ) (496963407229/1000000000000 : ℝ) (496963407237/1000000000000 : ℝ) (250249282273/500000000000 : ℝ) (250249282277/500000000000 : ℝ) (250243039751/500000000000 : ℝ) (500486079511/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33117/262144 : ℝ))) 3 (250249282273/500000000000 : ℝ) (250249282277/500000000000 : ℝ) (250243039751/500000000000 : ℝ) (500486079511/1000000000000 : ℝ) (62561540253/125000000000 : ℝ) (500492322033/1000000000000 : ℝ) (100098464397/200000000000 : ℝ) (250246160997/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33117/262144 : ℝ))) 4 (62561540253/125000000000 : ℝ) (500492322033/1000000000000 : ℝ) (100098464397/200000000000 : ℝ) (250246160997/500000000000 : ℝ) (125123080501/250000000000 : ℝ) (250246161007/500000000000 : ℝ) (125123080501/250000000000 : ℝ) (250246161007/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33117/262144 : ℝ))) 5 (125123080501/250000000000 : ℝ) (250246161007/500000000000 : ℝ) (125123080501/250000000000 : ℝ) (250246161007/500000000000 : ℝ) (125123080501/250000000000 : ℝ) (250246161007/500000000000 : ℝ) (125123080501/250000000000 : ℝ) (250246161007/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33117/262144 : ℝ))) 6 (125123080501/250000000000 : ℝ) (250246161007/500000000000 : ℝ) (125123080501/250000000000 : ℝ) (250246161007/500000000000 : ℝ) (125123080501/250000000000 : ℝ) (250246161007/500000000000 : ℝ) (125123080501/250000000000 : ℝ) (250246161007/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33117/262144 : ℝ))) 7 (125123080501/250000000000 : ℝ) (250246161007/500000000000 : ℝ) (125123080501/250000000000 : ℝ) (250246161007/500000000000 : ℝ) (125123080501/250000000000 : ℝ) (250246161007/500000000000 : ℝ) (125123080501/250000000000 : ℝ) (250246161007/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33117/262144 : ℝ)) hmem 8 (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ) (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33117/262144 : ℝ))) hcmem 8 (125123080501/250000000000 : ℝ) (250246161007/500000000000 : ℝ) (125123080501/250000000000 : ℝ) (250246161007/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33117/262144 : ℝ)) (992150844137/1000000000000 : ℝ) (49607542207/50000000000 : ℝ) (125123080501/250000000000 : ℝ) (250246161007/500000000000 : ℝ) (49524443891/62500000000 : ℝ) (31695644091/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0336_exp_lower
  have heNumeric : (1027453687041/500000000000 : ℝ)/4 ≤ Real.exp (-426280696081/640000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453687041/500000000000 : ℝ)/4 ≤ Real.exp ((8279/65536 : ℝ)-(31695644091/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8279/65536 : ℝ) (33117/262144 : ℝ) (31695644091/40000000000 : ℝ) (1027453687041/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0337; no trusted numerical premise.
theorem cover8_leaf0337_exp_radius : (499013980202289917/500000000000000000 : ℝ) ≤ Real.exp ((-16559/1048576 : ℝ)/8) ∧ Real.exp ((-16559/1048576 : ℝ)/8) ≤ (199605592080915967/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16559/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0337_exp_lower : (460056885774760883/500000000000000000 : ℝ) ≤ Real.exp ((-42628071350867/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628071350867/64000000000000 : ℝ)/8) ≤ (920113771549521767/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628071350867/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0337_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453659063/500000000000 : ℝ) ≤ 4*Real.exp (33117/262144 : ℝ)*Real.exp (-mu (radius 8 (16559/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453659063/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16559/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0337_exp_radius
  have hrNumeric : (492166072573/500000000000 : ℝ) ≤ Real.exp (-16559/1048576 : ℝ) ∧ Real.exp (-16559/1048576 : ℝ) ≤ (984332145147/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492166072573/500000000000 : ℝ) ≤ (radius 8 (16559/131072 : ℝ)) ∧ (radius 8 (16559/131072 : ℝ)) ≤ (984332145147/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16559/131072 : ℝ)) (492166072573/500000000000 : ℝ) (984332145147/1000000000000 : ℝ) (17632421283/100000000000 : ℝ) (176324212837/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16559/131072 : ℝ)) (492166072573/500000000000 : ℝ) (984332145147/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16559/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492166072573/500000000000 : ℝ) (984332145147/1000000000000 : ℝ) (992166072573/1000000000000 : ℝ) (496083036287/500000000000 : ℝ) (992135144597/1000000000000 : ℝ) (992135144599/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16559/131072 : ℝ)) 1 (992166072573/1000000000000 : ℝ) (496083036287/500000000000 : ℝ) (992135144597/1000000000000 : ℝ) (992135144599/1000000000000 : ℝ) (198430121717/200000000000 : ℝ) (992150608587/1000000000000 : ℝ) (62009413029/62500000000 : ℝ) (496075304233/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16559/131072 : ℝ)) 2 (198430121717/200000000000 : ℝ) (992150608587/1000000000000 : ℝ) (62009413029/62500000000 : ℝ) (496075304233/500000000000 : ℝ) (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ) (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16559/131072 : ℝ)) 3 (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ) (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ) (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ) (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16559/131072 : ℝ)) 4 (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ) (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ) (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ) (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16559/131072 : ℝ)) 5 (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ) (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ) (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ) (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16559/131072 : ℝ)) 6 (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ) (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ) (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ) (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16559/131072 : ℝ)) 7 (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ) (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ) (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ) (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16559/131072 : ℝ))) (17632421283/100000000000 : ℝ) (176324212837/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16559/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17632421283/100000000000 : ℝ) (176324212837/1000000000000 : ℝ) (117632421283/200000000000 : ℝ) (588162106419/1000000000000 : ℝ) (83981953497/200000000000 : ℝ) (83981953499/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16559/131072 : ℝ))) 1 (117632421283/200000000000 : ℝ) (588162106419/1000000000000 : ℝ) (83981953497/200000000000 : ℝ) (83981953499/200000000000 : ℝ) (10080718739/20000000000 : ℝ) (504035936957/1000000000000 : ℝ) (496965807021/1000000000000 : ℝ) (496965807029/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16559/131072 : ℝ))) 2 (10080718739/20000000000 : ℝ) (504035936957/1000000000000 : ℝ) (496965807021/1000000000000 : ℝ) (496965807029/1000000000000 : ℝ) (100100174397/200000000000 : ℝ) (500500871993/1000000000000 : ℝ) (500488387651/1000000000000 : ℝ) (500488387659/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16559/131072 : ℝ))) 3 (100100174397/200000000000 : ℝ) (500500871993/1000000000000 : ℝ) (500488387651/1000000000000 : ℝ) (500488387659/1000000000000 : ℝ) (250247314909/500000000000 : ℝ) (250247314913/500000000000 : ℝ) (500494629779/1000000000000 : ℝ) (125123657447/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16559/131072 : ℝ))) 4 (250247314909/500000000000 : ℝ) (250247314913/500000000000 : ℝ) (500494629779/1000000000000 : ℝ) (125123657447/250000000000 : ℝ) (250247314899/500000000000 : ℝ) (500494629807/1000000000000 : ℝ) (250247314899/500000000000 : ℝ) (500494629807/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16559/131072 : ℝ))) 5 (250247314899/500000000000 : ℝ) (500494629807/1000000000000 : ℝ) (250247314899/500000000000 : ℝ) (500494629807/1000000000000 : ℝ) (250247314899/500000000000 : ℝ) (500494629807/1000000000000 : ℝ) (250247314899/500000000000 : ℝ) (500494629807/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16559/131072 : ℝ))) 6 (250247314899/500000000000 : ℝ) (500494629807/1000000000000 : ℝ) (250247314899/500000000000 : ℝ) (500494629807/1000000000000 : ℝ) (250247314899/500000000000 : ℝ) (500494629807/1000000000000 : ℝ) (250247314899/500000000000 : ℝ) (500494629807/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16559/131072 : ℝ))) 7 (250247314899/500000000000 : ℝ) (500494629807/1000000000000 : ℝ) (250247314899/500000000000 : ℝ) (500494629807/1000000000000 : ℝ) (250247314899/500000000000 : ℝ) (500494629807/1000000000000 : ℝ) (250247314899/500000000000 : ℝ) (500494629807/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16559/131072 : ℝ)) hmem 8 (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ) (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16559/131072 : ℝ))) hcmem 8 (250247314899/500000000000 : ℝ) (500494629807/1000000000000 : ℝ) (250247314899/500000000000 : ℝ) (500494629807/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16559/131072 : ℝ)) (248037652131/250000000000 : ℝ) (992150608527/1000000000000 : ℝ) (250247314899/500000000000 : ℝ) (500494629807/1000000000000 : ℝ) (158478988837/200000000000 : ℝ) (792394944203/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0337_exp_lower
  have heNumeric : (1027453659063/500000000000 : ℝ)/4 ≤ Real.exp (-42628071350867/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453659063/500000000000 : ℝ)/4 ≤ Real.exp ((33117/262144 : ℝ)-(792394944203/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33117/262144 : ℝ) (16559/131072 : ℝ) (792394944203/1000000000000 : ℝ) (1027453659063/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0338; no trusted numerical premise.
theorem cover8_leaf0338_exp_radius : (998027900917479551/1000000000000000000 : ℝ) ≤ Real.exp ((-33119/2097152 : ℝ)/8) ∧ Real.exp ((-33119/2097152 : ℝ)/8) ≤ (7797092975917809/7812500000000000 : ℝ) := by
  have h := exp_small_bounds ((-33119/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0338_exp_lower : (920113768426456153/1000000000000000000 : ℝ) ≤ Real.exp ((-21314036544353/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314036544353/32000000000000 : ℝ)/8) ≤ (460056884213228077/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314036544353/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0338_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907262327/1000000000000 : ℝ) ≤ 4*Real.exp (16559/131072 : ℝ)*Real.exp (-mu (radius 8 (33119/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907262327/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33119/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0338_exp_radius
  have hrNumeric : (49216583789/50000000000 : ℝ) ≤ Real.exp (-33119/2097152 : ℝ) ∧ Real.exp (-33119/2097152 : ℝ) ≤ (984331675781/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49216583789/50000000000 : ℝ) ≤ (radius 8 (33119/262144 : ℝ)) ∧ (radius 8 (33119/262144 : ℝ)) ≤ (984331675781/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33119/262144 : ℝ)) (49216583789/50000000000 : ℝ) (984331675781/1000000000000 : ℝ) (44081708263/250000000000 : ℝ) (88163416529/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33119/262144 : ℝ)) (49216583789/50000000000 : ℝ) (984331675781/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33119/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49216583789/50000000000 : ℝ) (984331675781/1000000000000 : ℝ) (99216583789/100000000000 : ℝ) (992165837891/1000000000000 : ℝ) (496067454027/500000000000 : ℝ) (198426981611/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33119/262144 : ℝ)) 1 (99216583789/100000000000 : ℝ) (992165837891/1000000000000 : ℝ) (496067454027/500000000000 : ℝ) (198426981611/200000000000 : ℝ) (248037593243/250000000000 : ℝ) (992150372973/1000000000000 : ℝ) (992150372851/1000000000000 : ℝ) (992150372853/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33119/262144 : ℝ)) 2 (248037593243/250000000000 : ℝ) (992150372973/1000000000000 : ℝ) (992150372851/1000000000000 : ℝ) (992150372853/1000000000000 : ℝ) (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ) (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33119/262144 : ℝ)) 3 (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ) (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ) (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ) (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33119/262144 : ℝ)) 4 (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ) (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ) (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ) (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33119/262144 : ℝ)) 5 (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ) (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ) (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ) (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33119/262144 : ℝ)) 6 (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ) (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ) (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ) (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33119/262144 : ℝ)) 7 (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ) (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ) (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ) (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33119/262144 : ℝ))) (44081708263/250000000000 : ℝ) (88163416529/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33119/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44081708263/250000000000 : ℝ) (88163416529/500000000000 : ℝ) (294081708263/500000000000 : ℝ) (588163416529/1000000000000 : ℝ) (13122277733/31250000000 : ℝ) (52489110933/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33119/262144 : ℝ))) 1 (294081708263/500000000000 : ℝ) (588163416529/1000000000000 : ℝ) (13122277733/31250000000 : ℝ) (52489110933/125000000000 : ℝ) (504038151991/1000000000000 : ℝ) (504038151997/1000000000000 : ℝ) (496968206759/1000000000000 : ℝ) (248484103383/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33119/262144 : ℝ))) 2 (504038151991/1000000000000 : ℝ) (504038151997/1000000000000 : ℝ) (496968206759/1000000000000 : ℝ) (248484103383/500000000000 : ℝ) (800805087/1600000000 : ℝ) (250251589691/500000000000 : ℝ) (2001962783/4000000000 : ℝ) (250245347879/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33119/262144 : ℝ))) 3 (800805087/1600000000 : ℝ) (250251589691/500000000000 : ℝ) (2001962783/4000000000 : ℝ) (250245347879/500000000000 : ℝ) (250248468781/500000000000 : ℝ) (50049693757/100000000000 : ℝ) (500496937523/1000000000000 : ℝ) (125124234383/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33119/262144 : ℝ))) 4 (250248468781/500000000000 : ℝ) (50049693757/100000000000 : ℝ) (500496937523/1000000000000 : ℝ) (125124234383/250000000000 : ℝ) (250248468771/500000000000 : ℝ) (500496937551/1000000000000 : ℝ) (250248468771/500000000000 : ℝ) (500496937551/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33119/262144 : ℝ))) 5 (250248468771/500000000000 : ℝ) (500496937551/1000000000000 : ℝ) (250248468771/500000000000 : ℝ) (500496937551/1000000000000 : ℝ) (250248468771/500000000000 : ℝ) (500496937551/1000000000000 : ℝ) (250248468771/500000000000 : ℝ) (500496937551/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33119/262144 : ℝ))) 6 (250248468771/500000000000 : ℝ) (500496937551/1000000000000 : ℝ) (250248468771/500000000000 : ℝ) (500496937551/1000000000000 : ℝ) (250248468771/500000000000 : ℝ) (500496937551/1000000000000 : ℝ) (250248468771/500000000000 : ℝ) (500496937551/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33119/262144 : ℝ))) 7 (250248468771/500000000000 : ℝ) (500496937551/1000000000000 : ℝ) (250248468771/500000000000 : ℝ) (500496937551/1000000000000 : ℝ) (250248468771/500000000000 : ℝ) (500496937551/1000000000000 : ℝ) (250248468771/500000000000 : ℝ) (500496937551/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33119/262144 : ℝ)) hmem 8 (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ) (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33119/262144 : ℝ))) hcmem 8 (250248468771/500000000000 : ℝ) (500496937551/1000000000000 : ℝ) (250248468771/500000000000 : ℝ) (500496937551/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33119/262144 : ℝ)) (992150372911/1000000000000 : ℝ) (992150372913/1000000000000 : ℝ) (250248468771/500000000000 : ℝ) (500496937551/1000000000000 : ℝ) (792398786037/1000000000000 : ℝ) (396199393027/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0338_exp_lower
  have heNumeric : (2054907262327/1000000000000 : ℝ)/4 ≤ Real.exp (-21314036544353/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907262327/1000000000000 : ℝ)/4 ≤ Real.exp ((16559/131072 : ℝ)-(396199393027/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16559/131072 : ℝ) (33119/262144 : ℝ) (396199393027/500000000000 : ℝ) (2054907262327/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0339; no trusted numerical premise.
theorem cover8_leaf0339_exp_radius : (499013920715191407/500000000000000000 : ℝ) ≤ Real.exp ((-1035/65536 : ℝ)/8) ∧ Real.exp ((-1035/65536 : ℝ)/8) ≤ (199605568286076563/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1035/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0339_exp_lower : (57507110332008227/62500000000000000 : ℝ) ≤ Real.exp ((-42628074821681/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628074821681/64000000000000 : ℝ)/8) ≤ (920113765312131633/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628074821681/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0339_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410981441337/200000000000 : ℝ) ≤ 4*Real.exp (33119/262144 : ℝ)*Real.exp (-mu (radius 8 (1035/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (410981441337/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1035/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0339_exp_radius
  have hrNumeric : (492165603207/500000000000 : ℝ) ≤ Real.exp (-1035/65536 : ℝ) ∧ Real.exp (-1035/65536 : ℝ) ≤ (196866241283/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492165603207/500000000000 : ℝ) ≤ (radius 8 (1035/8192 : ℝ)) ∧ (radius 8 (1035/8192 : ℝ)) ≤ (196866241283/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1035/8192 : ℝ)) (492165603207/500000000000 : ℝ) (196866241283/200000000000 : ℝ) (176329453233/1000000000000 : ℝ) (176329453239/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1035/8192 : ℝ)) (492165603207/500000000000 : ℝ) (196866241283/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1035/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492165603207/500000000000 : ℝ) (196866241283/200000000000 : ℝ) (992165603207/1000000000000 : ℝ) (124020700401/125000000000 : ℝ) (99213467151/100000000000 : ℝ) (124016833939/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1035/8192 : ℝ)) 1 (992165603207/1000000000000 : ℝ) (124020700401/125000000000 : ℝ) (99213467151/100000000000 : ℝ) (124016833939/125000000000 : ℝ) (496075068679/500000000000 : ℝ) (12401876717/12500000000 : ℝ) (992150137237/1000000000000 : ℝ) (24803753431/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1035/8192 : ℝ)) 2 (496075068679/500000000000 : ℝ) (12401876717/12500000000 : ℝ) (992150137237/1000000000000 : ℝ) (24803753431/25000000000 : ℝ) (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ) (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1035/8192 : ℝ)) 3 (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ) (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ) (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ) (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1035/8192 : ℝ)) 4 (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ) (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ) (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ) (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1035/8192 : ℝ)) 5 (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ) (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ) (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ) (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1035/8192 : ℝ)) 6 (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ) (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ) (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ) (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1035/8192 : ℝ)) 7 (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ) (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ) (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ) (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1035/8192 : ℝ))) (176329453233/1000000000000 : ℝ) (176329453239/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1035/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176329453233/1000000000000 : ℝ) (176329453239/1000000000000 : ℝ) (73520590827/125000000000 : ℝ) (29408236331/50000000000 : ℝ) (83983201471/200000000000 : ℝ) (419916007363/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1035/8192 : ℝ))) 1 (73520590827/125000000000 : ℝ) (29408236331/50000000000 : ℝ) (83983201471/200000000000 : ℝ) (419916007363/1000000000000 : ℝ) (100808073397/200000000000 : ℝ) (31502522937/62500000000 : ℝ) (248485303221/500000000000 : ℝ) (496970606449/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1035/8192 : ℝ))) 2 (100808073397/200000000000 : ℝ) (31502522937/62500000000 : ℝ) (248485303221/500000000000 : ℝ) (496970606449/1000000000000 : ℝ) (500505486713/1000000000000 : ℝ) (500505486721/1000000000000 : ℝ) (500493003799/1000000000000 : ℝ) (500493003807/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1035/8192 : ℝ))) 3 (500505486713/1000000000000 : ℝ) (500505486721/1000000000000 : ℝ) (500493003799/1000000000000 : ℝ) (500493003807/1000000000000 : ℝ) (62562405657/125000000000 : ℝ) (31281202829/62500000000 : ℝ) (500499245217/1000000000000 : ℝ) (250249622613/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1035/8192 : ℝ))) 4 (62562405657/125000000000 : ℝ) (31281202829/62500000000 : ℝ) (500499245217/1000000000000 : ℝ) (250249622613/500000000000 : ℝ) (125124811309/250000000000 : ℝ) (100099849049/200000000000 : ℝ) (125124811309/250000000000 : ℝ) (100099849049/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1035/8192 : ℝ))) 5 (125124811309/250000000000 : ℝ) (100099849049/200000000000 : ℝ) (125124811309/250000000000 : ℝ) (100099849049/200000000000 : ℝ) (125124811309/250000000000 : ℝ) (100099849049/200000000000 : ℝ) (125124811309/250000000000 : ℝ) (100099849049/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1035/8192 : ℝ))) 6 (125124811309/250000000000 : ℝ) (100099849049/200000000000 : ℝ) (125124811309/250000000000 : ℝ) (100099849049/200000000000 : ℝ) (125124811309/250000000000 : ℝ) (100099849049/200000000000 : ℝ) (125124811309/250000000000 : ℝ) (100099849049/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1035/8192 : ℝ))) 7 (125124811309/250000000000 : ℝ) (100099849049/200000000000 : ℝ) (125124811309/250000000000 : ℝ) (100099849049/200000000000 : ℝ) (125124811309/250000000000 : ℝ) (100099849049/200000000000 : ℝ) (125124811309/250000000000 : ℝ) (100099849049/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1035/8192 : ℝ)) hmem 8 (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ) (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1035/8192 : ℝ))) hcmem 8 (125124811309/250000000000 : ℝ) (100099849049/200000000000 : ℝ) (125124811309/250000000000 : ℝ) (100099849049/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1035/8192 : ℝ)) (992150137297/1000000000000 : ℝ) (9921501373/10000000000 : ℝ) (125124811309/250000000000 : ℝ) (100099849049/200000000000 : ℝ) (792402627811/1000000000000 : ℝ) (792402627829/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0339_exp_lower
  have heNumeric : (410981441337/200000000000 : ℝ)/4 ≤ Real.exp (-42628074821681/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410981441337/200000000000 : ℝ)/4 ≤ Real.exp ((33119/262144 : ℝ)-(792402627829/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33119/262144 : ℝ) (1035/8192 : ℝ) (792402627829/1000000000000 : ℝ) (410981441337/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0340; no trusted numerical premise.
theorem cover8_leaf0340_exp_radius : (998027781943289623/1000000000000000000 : ℝ) ≤ Real.exp ((-33121/2097152 : ℝ)/8) ∧ Real.exp ((-33121/2097152 : ℝ)/8) ≤ (124753472742911203/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33121/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0340_exp_lower : (184022752441332643/200000000000000000 : ℝ) ≤ Real.exp ((-1332127392179/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332127392179/2000000000000 : ℝ)/8) ≤ (57507110137916451/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332127392179/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0340_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907151201/1000000000000 : ℝ) ≤ 4*Real.exp (1035/8192 : ℝ)*Real.exp (-mu (radius 8 (33121/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907151201/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33121/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0340_exp_radius
  have hrNumeric : (123041342131/125000000000 : ℝ) ≤ Real.exp (-33121/2097152 : ℝ) ∧ Real.exp (-33121/2097152 : ℝ) ≤ (984330737049/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123041342131/125000000000 : ℝ) ≤ (radius 8 (33121/262144 : ℝ)) ∧ (radius 8 (33121/262144 : ℝ)) ≤ (984330737049/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33121/262144 : ℝ)) (123041342131/125000000000 : ℝ) (984330737049/1000000000000 : ℝ) (88166036687/500000000000 : ℝ) (176332073381/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33121/262144 : ℝ)) (123041342131/125000000000 : ℝ) (984330737049/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33121/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123041342131/125000000000 : ℝ) (984330737049/1000000000000 : ℝ) (248041342131/250000000000 : ℝ) (39686614741/40000000000 : ℝ) (992134434967/1000000000000 : ℝ) (124016804371/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33121/262144 : ℝ)) 1 (248041342131/250000000000 : ℝ) (39686614741/40000000000 : ℝ) (992134434967/1000000000000 : ℝ) (124016804371/125000000000 : ℝ) (198429980349/200000000000 : ℝ) (992149901747/1000000000000 : ℝ) (124018737703/125000000000 : ℝ) (496074950813/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33121/262144 : ℝ)) 2 (198429980349/200000000000 : ℝ) (992149901747/1000000000000 : ℝ) (124018737703/125000000000 : ℝ) (496074950813/500000000000 : ℝ) (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ) (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33121/262144 : ℝ)) 3 (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ) (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ) (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ) (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33121/262144 : ℝ)) 4 (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ) (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ) (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ) (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33121/262144 : ℝ)) 5 (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ) (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ) (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ) (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33121/262144 : ℝ)) 6 (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ) (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ) (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ) (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33121/262144 : ℝ)) 7 (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ) (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ) (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ) (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33121/262144 : ℝ))) (88166036687/500000000000 : ℝ) (176332073381/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33121/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88166036687/500000000000 : ℝ) (176332073381/1000000000000 : ℝ) (588166036687/1000000000000 : ℝ) (588166036691/1000000000000 : ℝ) (209959563591/500000000000 : ℝ) (52489890899/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33121/262144 : ℝ))) 1 (588166036687/1000000000000 : ℝ) (588166036691/1000000000000 : ℝ) (209959563591/500000000000 : ℝ) (52489890899/125000000000 : ℝ) (252021290967/500000000000 : ℝ) (252021290971/500000000000 : ℝ) (496973006071/1000000000000 : ℝ) (388260161/781250000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33121/262144 : ℝ))) 2 (252021290967/500000000000 : ℝ) (252021290971/500000000000 : ℝ) (496973006071/1000000000000 : ℝ) (388260161/781250000 : ℝ) (250253897001/500000000000 : ℝ) (500507794011/1000000000000 : ℝ) (500495311797/1000000000000 : ℝ) (500495311807/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33121/262144 : ℝ))) 3 (250253897001/500000000000 : ℝ) (500507794011/1000000000000 : ℝ) (500495311797/1000000000000 : ℝ) (500495311807/1000000000000 : ℝ) (500501552899/1000000000000 : ℝ) (500501552909/1000000000000 : ℝ) (25025077643/50000000000 : ℝ) (500501552871/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33121/262144 : ℝ))) 4 (500501552899/1000000000000 : ℝ) (500501552909/1000000000000 : ℝ) (25025077643/50000000000 : ℝ) (500501552871/1000000000000 : ℝ) (500501552879/1000000000000 : ℝ) (50050155289/100000000000 : ℝ) (500501552879/1000000000000 : ℝ) (50050155289/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33121/262144 : ℝ))) 5 (500501552879/1000000000000 : ℝ) (50050155289/100000000000 : ℝ) (500501552879/1000000000000 : ℝ) (50050155289/100000000000 : ℝ) (500501552879/1000000000000 : ℝ) (50050155289/100000000000 : ℝ) (500501552879/1000000000000 : ℝ) (50050155289/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33121/262144 : ℝ))) 6 (500501552879/1000000000000 : ℝ) (50050155289/100000000000 : ℝ) (500501552879/1000000000000 : ℝ) (50050155289/100000000000 : ℝ) (500501552879/1000000000000 : ℝ) (50050155289/100000000000 : ℝ) (500501552879/1000000000000 : ℝ) (50050155289/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33121/262144 : ℝ))) 7 (500501552879/1000000000000 : ℝ) (50050155289/100000000000 : ℝ) (500501552879/1000000000000 : ℝ) (50050155289/100000000000 : ℝ) (500501552879/1000000000000 : ℝ) (50050155289/100000000000 : ℝ) (500501552879/1000000000000 : ℝ) (50050155289/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33121/262144 : ℝ)) hmem 8 (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ) (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33121/262144 : ℝ))) hcmem 8 (500501552879/1000000000000 : ℝ) (50050155289/100000000000 : ℝ) (500501552879/1000000000000 : ℝ) (50050155289/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33121/262144 : ℝ)) (248037475421/250000000000 : ℝ) (992149901687/1000000000000 : ℝ) (500501552879/1000000000000 : ℝ) (50050155289/100000000000 : ℝ) (396203234753/500000000000 : ℝ) (792406469527/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0340_exp_lower
  have heNumeric : (2054907151201/1000000000000 : ℝ)/4 ≤ Real.exp (-1332127392179/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907151201/1000000000000 : ℝ)/4 ≤ Real.exp ((1035/8192 : ℝ)-(792406469527/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1035/8192 : ℝ) (33121/262144 : ℝ) (792406469527/1000000000000 : ℝ) (2054907151201/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0341; no trusted numerical premise.
theorem cover8_leaf0341_exp_radius : (998027722456199977/1000000000000000000 : ℝ) ≤ Real.exp ((-16561/1048576 : ℝ)/8) ∧ Real.exp ((-16561/1048576 : ℝ)/8) ≤ (499013861228099989/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16561/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0341_exp_lower : (57507109944442877/62500000000000000 : ℝ) ≤ Real.exp ((-42628078272271/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628078272271/64000000000000 : ℝ)/8) ≤ (920113759111086033/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628078272271/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0341_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453547947/500000000000 : ℝ) ≤ 4*Real.exp (33121/262144 : ℝ)*Real.exp (-mu (radius 8 (16561/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453547947/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16561/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0341_exp_radius
  have hrNumeric : (984330267683/1000000000000 : ℝ) ≤ Real.exp (-16561/1048576 : ℝ) ∧ Real.exp (-16561/1048576 : ℝ) ≤ (246082566921/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984330267683/1000000000000 : ℝ) ≤ (radius 8 (16561/131072 : ℝ)) ∧ (radius 8 (16561/131072 : ℝ)) ≤ (246082566921/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16561/131072 : ℝ)) (984330267683/1000000000000 : ℝ) (246082566921/250000000000 : ℝ) (176334693469/1000000000000 : ℝ) (44083673369/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16561/131072 : ℝ)) (984330267683/1000000000000 : ℝ) (246082566921/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16561/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984330267683/1000000000000 : ℝ) (246082566921/250000000000 : ℝ) (992165133841/1000000000000 : ℝ) (496082566921/500000000000 : ℝ) (124016774803/125000000000 : ℝ) (39685367937/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16561/131072 : ℝ)) 1 (992165133841/1000000000000 : ℝ) (496082566921/500000000000 : ℝ) (124016774803/125000000000 : ℝ) (39685367937/40000000000 : ℝ) (248037416533/250000000000 : ℝ) (496074833067/500000000000 : ℝ) (992149666011/1000000000000 : ℝ) (992149666013/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16561/131072 : ℝ)) 2 (248037416533/250000000000 : ℝ) (496074833067/500000000000 : ℝ) (992149666011/1000000000000 : ℝ) (992149666013/1000000000000 : ℝ) (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ) (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16561/131072 : ℝ)) 3 (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ) (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ) (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ) (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16561/131072 : ℝ)) 4 (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ) (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ) (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ) (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16561/131072 : ℝ)) 5 (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ) (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ) (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ) (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16561/131072 : ℝ)) 6 (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ) (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ) (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ) (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16561/131072 : ℝ)) 7 (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ) (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ) (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ) (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16561/131072 : ℝ))) (176334693469/1000000000000 : ℝ) (44083673369/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16561/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176334693469/1000000000000 : ℝ) (44083673369/250000000000 : ℝ) (294083673367/500000000000 : ℝ) (294083673369/500000000000 : ℝ) (104980561733/250000000000 : ℝ) (209961123471/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16561/131072 : ℝ))) 1 (294083673367/500000000000 : ℝ) (294083673369/500000000000 : ℝ) (104980561733/250000000000 : ℝ) (209961123471/500000000000 : ℝ) (504044796833/1000000000000 : ℝ) (12601119921/25000000000 : ℝ) (496975405641/1000000000000 : ℝ) (9939508113/20000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16561/131072 : ℝ))) 2 (504044796833/1000000000000 : ℝ) (12601119921/25000000000 : ℝ) (496975405641/1000000000000 : ℝ) (9939508113/20000000000 : ℝ) (500510101237/1000000000000 : ℝ) (100102020249/200000000000 : ℝ) (500497619741/1000000000000 : ℝ) (2001990479/4000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16561/131072 : ℝ))) 3 (500510101237/1000000000000 : ℝ) (100102020249/200000000000 : ℝ) (500497619741/1000000000000 : ℝ) (2001990479/4000000000 : ℝ) (500503860489/1000000000000 : ℝ) (250251930249/500000000000 : ℝ) (10010077209/20000000000 : ℝ) (500503860459/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16561/131072 : ℝ))) 4 (500503860489/1000000000000 : ℝ) (250251930249/500000000000 : ℝ) (10010077209/20000000000 : ℝ) (500503860459/1000000000000 : ℝ) (500503860469/1000000000000 : ℝ) (500503860479/1000000000000 : ℝ) (500503860469/1000000000000 : ℝ) (500503860479/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16561/131072 : ℝ))) 5 (500503860469/1000000000000 : ℝ) (500503860479/1000000000000 : ℝ) (500503860469/1000000000000 : ℝ) (500503860479/1000000000000 : ℝ) (500503860469/1000000000000 : ℝ) (500503860479/1000000000000 : ℝ) (500503860469/1000000000000 : ℝ) (500503860479/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16561/131072 : ℝ))) 6 (500503860469/1000000000000 : ℝ) (500503860479/1000000000000 : ℝ) (500503860469/1000000000000 : ℝ) (500503860479/1000000000000 : ℝ) (500503860469/1000000000000 : ℝ) (500503860479/1000000000000 : ℝ) (500503860469/1000000000000 : ℝ) (500503860479/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16561/131072 : ℝ))) 7 (500503860469/1000000000000 : ℝ) (500503860479/1000000000000 : ℝ) (500503860469/1000000000000 : ℝ) (500503860479/1000000000000 : ℝ) (500503860469/1000000000000 : ℝ) (500503860479/1000000000000 : ℝ) (500503860469/1000000000000 : ℝ) (500503860479/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16561/131072 : ℝ)) hmem 8 (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ) (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16561/131072 : ℝ))) hcmem 8 (500503860469/1000000000000 : ℝ) (500503860479/1000000000000 : ℝ) (500503860469/1000000000000 : ℝ) (500503860479/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16561/131072 : ℝ)) (992149666071/1000000000000 : ℝ) (496074833037/500000000000 : ℝ) (500503860469/1000000000000 : ℝ) (500503860479/1000000000000 : ℝ) (9905128889/12500000000 : ℝ) (792410311139/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0341_exp_lower
  have heNumeric : (1027453547947/500000000000 : ℝ)/4 ≤ Real.exp (-42628078272271/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453547947/500000000000 : ℝ)/4 ≤ Real.exp ((33121/262144 : ℝ)-(792410311139/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33121/262144 : ℝ) (16561/131072 : ℝ) (792410311139/1000000000000 : ℝ) (1027453547947/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0342; no trusted numerical premise.
theorem cover8_leaf0342_exp_radius : (998027662969113877/1000000000000000000 : ℝ) ≤ Real.exp ((-33123/2097152 : ℝ)/8) ∧ Real.exp ((-33123/2097152 : ℝ)/8) ≤ (499013831484556939/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33123/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0342_exp_lower : (184022751204872991/200000000000000000 : ℝ) ≤ Real.exp ((-21314039994943/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314039994943/32000000000000 : ℝ)/8) ≤ (230028439006091239/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314039994943/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0342_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410981408149/200000000000 : ℝ) ≤ 4*Real.exp (16561/131072 : ℝ)*Real.exp (-mu (radius 8 (33123/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410981408149/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33123/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0342_exp_radius
  have hrNumeric : (492164899159/500000000000 : ℝ) ≤ Real.exp (-33123/2097152 : ℝ) ∧ Real.exp (-33123/2097152 : ℝ) ≤ (984329798319/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492164899159/500000000000 : ℝ) ≤ (radius 8 (33123/262144 : ℝ)) ∧ (radius 8 (33123/262144 : ℝ)) ≤ (984329798319/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33123/262144 : ℝ)) (492164899159/500000000000 : ℝ) (984329798319/1000000000000 : ℝ) (7053492541/40000000000 : ℝ) (176337313531/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33123/262144 : ℝ)) (492164899159/500000000000 : ℝ) (984329798319/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33123/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492164899159/500000000000 : ℝ) (984329798319/1000000000000 : ℝ) (992164899159/1000000000000 : ℝ) (24804122479/25000000000 : ℝ) (992133961881/1000000000000 : ℝ) (496066980941/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33123/262144 : ℝ)) 1 (992164899159/1000000000000 : ℝ) (24804122479/25000000000 : ℝ) (992133961881/1000000000000 : ℝ) (496066980941/500000000000 : ℝ) (24803735763/25000000000 : ℝ) (992149430521/1000000000000 : ℝ) (992149430399/1000000000000 : ℝ) (992149430401/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33123/262144 : ℝ)) 2 (24803735763/25000000000 : ℝ) (992149430521/1000000000000 : ℝ) (992149430399/1000000000000 : ℝ) (992149430401/1000000000000 : ℝ) (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ) (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33123/262144 : ℝ)) 3 (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ) (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ) (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ) (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33123/262144 : ℝ)) 4 (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ) (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ) (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ) (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33123/262144 : ℝ)) 5 (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ) (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ) (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ) (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33123/262144 : ℝ)) 6 (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ) (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ) (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ) (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33123/262144 : ℝ)) 7 (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ) (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ) (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ) (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33123/262144 : ℝ))) (7053492541/40000000000 : ℝ) (176337313531/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33123/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7053492541/40000000000 : ℝ) (176337313531/1000000000000 : ℝ) (294084328381/500000000000 : ℝ) (294084328383/500000000000 : ℝ) (104981341653/250000000000 : ℝ) (419925366621/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33123/262144 : ℝ))) 1 (294084328381/500000000000 : ℝ) (294084328383/500000000000 : ℝ) (104981341653/250000000000 : ℝ) (419925366621/1000000000000 : ℝ) (504047011687/1000000000000 : ℝ) (252023505847/500000000000 : ℝ) (248488902579/500000000000 : ℝ) (248488902583/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33123/262144 : ℝ))) 2 (504047011687/1000000000000 : ℝ) (252023505847/500000000000 : ℝ) (248488902579/500000000000 : ℝ) (248488902583/500000000000 : ℝ) (250256204211/500000000000 : ℝ) (50051240843/100000000000 : ℝ) (500499927637/1000000000000 : ℝ) (100099985529/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33123/262144 : ℝ))) 3 (250256204211/500000000000 : ℝ) (50051240843/100000000000 : ℝ) (500499927637/1000000000000 : ℝ) (100099985529/200000000000 : ℝ) (500506168029/1000000000000 : ℝ) (250253084019/500000000000 : ℝ) (50050616799/100000000000 : ℝ) (500506167999/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33123/262144 : ℝ))) 4 (500506168029/1000000000000 : ℝ) (250253084019/500000000000 : ℝ) (50050616799/100000000000 : ℝ) (500506167999/1000000000000 : ℝ) (500506168009/1000000000000 : ℝ) (500506168019/1000000000000 : ℝ) (500506168009/1000000000000 : ℝ) (500506168019/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33123/262144 : ℝ))) 5 (500506168009/1000000000000 : ℝ) (500506168019/1000000000000 : ℝ) (500506168009/1000000000000 : ℝ) (500506168019/1000000000000 : ℝ) (500506168009/1000000000000 : ℝ) (500506168019/1000000000000 : ℝ) (500506168009/1000000000000 : ℝ) (500506168019/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33123/262144 : ℝ))) 6 (500506168009/1000000000000 : ℝ) (500506168019/1000000000000 : ℝ) (500506168009/1000000000000 : ℝ) (500506168019/1000000000000 : ℝ) (500506168009/1000000000000 : ℝ) (500506168019/1000000000000 : ℝ) (500506168009/1000000000000 : ℝ) (500506168019/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33123/262144 : ℝ))) 7 (500506168009/1000000000000 : ℝ) (500506168019/1000000000000 : ℝ) (500506168009/1000000000000 : ℝ) (500506168019/1000000000000 : ℝ) (500506168009/1000000000000 : ℝ) (500506168019/1000000000000 : ℝ) (500506168009/1000000000000 : ℝ) (500506168019/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33123/262144 : ℝ)) hmem 8 (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ) (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33123/262144 : ℝ))) hcmem 8 (500506168009/1000000000000 : ℝ) (500506168019/1000000000000 : ℝ) (500506168009/1000000000000 : ℝ) (500506168019/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33123/262144 : ℝ)) (992149430459/1000000000000 : ℝ) (992149430461/1000000000000 : ℝ) (500506168009/1000000000000 : ℝ) (500506168019/1000000000000 : ℝ) (158482830531/200000000000 : ℝ) (396207076337/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0342_exp_lower
  have heNumeric : (410981408149/200000000000 : ℝ)/4 ≤ Real.exp (-21314039994943/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410981408149/200000000000 : ℝ)/4 ≤ Real.exp ((16561/131072 : ℝ)-(396207076337/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16561/131072 : ℝ) (33123/262144 : ℝ) (396207076337/500000000000 : ℝ) (410981408149/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0343; no trusted numerical premise.
theorem cover8_leaf0343_exp_radius : (499013801741015661/500000000000000000 : ℝ) ≤ Real.exp ((-8281/524288 : ℝ)/8) ∧ Real.exp ((-8281/524288 : ℝ)/8) ≤ (998027603482031323/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8281/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0343_exp_lower : (115014219118298121/125000000000000000 : ℝ) ≤ Real.exp ((-42628081702637/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628081702637/64000000000000 : ℝ)/8) ≤ (920113752946384969/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628081702637/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0343_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256863373219/125000000000 : ℝ) ≤ 4*Real.exp (33123/262144 : ℝ)*Real.exp (-mu (radius 8 (8281/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (256863373219/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8281/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0343_exp_radius
  have hrNumeric : (984329328953/1000000000000 : ℝ) ≤ Real.exp (-8281/524288 : ℝ) ∧ Real.exp (-8281/524288 : ℝ) ≤ (492164664477/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984329328953/1000000000000 : ℝ) ≤ (radius 8 (8281/65536 : ℝ)) ∧ (radius 8 (8281/65536 : ℝ)) ≤ (492164664477/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8281/65536 : ℝ)) (984329328953/1000000000000 : ℝ) (492164664477/500000000000 : ℝ) (8816996677/50000000000 : ℝ) (88169966773/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8281/65536 : ℝ)) (984329328953/1000000000000 : ℝ) (492164664477/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8281/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984329328953/1000000000000 : ℝ) (492164664477/500000000000 : ℝ) (248041166119/250000000000 : ℝ) (992164664477/1000000000000 : ℝ) (992133725337/1000000000000 : ℝ) (992133725339/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8281/65536 : ℝ)) 1 (248041166119/250000000000 : ℝ) (992164664477/1000000000000 : ℝ) (992133725337/1000000000000 : ℝ) (992133725339/1000000000000 : ℝ) (496074597453/500000000000 : ℝ) (248037298727/250000000000 : ℝ) (198429838957/200000000000 : ℝ) (248037298697/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8281/65536 : ℝ)) 2 (496074597453/500000000000 : ℝ) (248037298727/250000000000 : ℝ) (198429838957/200000000000 : ℝ) (248037298697/250000000000 : ℝ) (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ) (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8281/65536 : ℝ)) 3 (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ) (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ) (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ) (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8281/65536 : ℝ)) 4 (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ) (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ) (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ) (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8281/65536 : ℝ)) 5 (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ) (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ) (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ) (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8281/65536 : ℝ)) 6 (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ) (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ) (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ) (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8281/65536 : ℝ)) 7 (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ) (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ) (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ) (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8281/65536 : ℝ))) (8816996677/50000000000 : ℝ) (88169966773/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8281/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8816996677/50000000000 : ℝ) (88169966773/500000000000 : ℝ) (58816996677/100000000000 : ℝ) (588169966773/1000000000000 : ℝ) (419928486221/1000000000000 : ℝ) (419928486229/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8281/65536 : ℝ))) 1 (58816996677/100000000000 : ℝ) (588169966773/1000000000000 : ℝ) (419928486221/1000000000000 : ℝ) (419928486229/1000000000000 : ℝ) (100809845299/200000000000 : ℝ) (504049226501/1000000000000 : ℝ) (248490102311/500000000000 : ℝ) (496980204629/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8281/65536 : ℝ))) 2 (100809845299/200000000000 : ℝ) (504049226501/1000000000000 : ℝ) (248490102311/500000000000 : ℝ) (496980204629/1000000000000 : ℝ) (250257357779/500000000000 : ℝ) (100102943113/200000000000 : ℝ) (250251117741/500000000000 : ℝ) (50050223549/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8281/65536 : ℝ))) 3 (250257357779/500000000000 : ℝ) (100102943113/200000000000 : ℝ) (250251117741/500000000000 : ℝ) (50050223549/100000000000 : ℝ) (782044493/1562500000 : ℝ) (62563559441/125000000000 : ℝ) (500508475481/1000000000000 : ℝ) (500508475489/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8281/65536 : ℝ))) 4 (782044493/1562500000 : ℝ) (62563559441/125000000000 : ℝ) (500508475481/1000000000000 : ℝ) (500508475489/1000000000000 : ℝ) (1001016951/2000000000 : ℝ) (500508475509/1000000000000 : ℝ) (1001016951/2000000000 : ℝ) (500508475509/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8281/65536 : ℝ))) 5 (1001016951/2000000000 : ℝ) (500508475509/1000000000000 : ℝ) (1001016951/2000000000 : ℝ) (500508475509/1000000000000 : ℝ) (1001016951/2000000000 : ℝ) (500508475509/1000000000000 : ℝ) (1001016951/2000000000 : ℝ) (500508475509/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8281/65536 : ℝ))) 6 (1001016951/2000000000 : ℝ) (500508475509/1000000000000 : ℝ) (1001016951/2000000000 : ℝ) (500508475509/1000000000000 : ℝ) (1001016951/2000000000 : ℝ) (500508475509/1000000000000 : ℝ) (1001016951/2000000000 : ℝ) (500508475509/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8281/65536 : ℝ))) 7 (1001016951/2000000000 : ℝ) (500508475509/1000000000000 : ℝ) (1001016951/2000000000 : ℝ) (500508475509/1000000000000 : ℝ) (1001016951/2000000000 : ℝ) (500508475509/1000000000000 : ℝ) (1001016951/2000000000 : ℝ) (500508475509/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8281/65536 : ℝ)) hmem 8 (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ) (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8281/65536 : ℝ))) hcmem 8 (1001016951/2000000000 : ℝ) (500508475509/1000000000000 : ℝ) (1001016951/2000000000 : ℝ) (500508475509/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8281/65536 : ℝ)) (198429838969/200000000000 : ℝ) (31004662339/31250000000 : ℝ) (1001016951/2000000000 : ℝ) (500508475509/1000000000000 : ℝ) (158483598823/200000000000 : ℝ) (792417994133/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0343_exp_lower
  have heNumeric : (256863373219/125000000000 : ℝ)/4 ≤ Real.exp (-42628081702637/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256863373219/125000000000 : ℝ)/4 ≤ Real.exp ((33123/262144 : ℝ)-(792417994133/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33123/262144 : ℝ) (8281/65536 : ℝ) (792417994133/1000000000000 : ℝ) (256863373219/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0344; no trusted numerical premise.
theorem cover8_leaf0344_exp_radius : (998027543994952313/1000000000000000000 : ℝ) ≤ Real.exp ((-33125/2097152 : ℝ)/8) ∧ Real.exp ((-33125/2097152 : ℝ)/8) ≤ (499013771997476157/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33125/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0344_exp_lower : (184022749975498223/200000000000000000 : ℝ) ≤ Real.exp ((-10657020852583/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657020852583/16000000000000 : ℝ)/8) ≤ (230028437469372779/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657020852583/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0344_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906930921/1000000000000 : ℝ) ≤ 4*Real.exp (8281/65536 : ℝ)*Real.exp (-mu (radius 8 (33125/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906930921/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33125/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0344_exp_radius
  have hrNumeric : (246082214897/250000000000 : ℝ) ≤ Real.exp (-33125/2097152 : ℝ) ∧ Real.exp (-33125/2097152 : ℝ) ≤ (984328859589/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246082214897/250000000000 : ℝ) ≤ (radius 8 (33125/262144 : ℝ)) ∧ (radius 8 (33125/262144 : ℝ)) ≤ (984328859589/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33125/262144 : ℝ)) (246082214897/250000000000 : ℝ) (984328859589/1000000000000 : ℝ) (35268510703/200000000000 : ℝ) (176342553521/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33125/262144 : ℝ)) (246082214897/250000000000 : ℝ) (984328859589/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33125/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246082214897/250000000000 : ℝ) (984328859589/1000000000000 : ℝ) (496082214897/500000000000 : ℝ) (198432885959/200000000000 : ℝ) (496066744397/500000000000 : ℝ) (248033372199/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33125/262144 : ℝ)) 1 (496082214897/500000000000 : ℝ) (198432885959/200000000000 : ℝ) (496066744397/500000000000 : ℝ) (248033372199/250000000000 : ℝ) (496074479647/500000000000 : ℝ) (15502327489/15625000000 : ℝ) (992148959173/1000000000000 : ℝ) (39685958367/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33125/262144 : ℝ)) 2 (496074479647/500000000000 : ℝ) (15502327489/15625000000 : ℝ) (992148959173/1000000000000 : ℝ) (39685958367/40000000000 : ℝ) (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ) (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33125/262144 : ℝ)) 3 (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ) (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ) (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ) (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33125/262144 : ℝ)) 4 (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ) (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ) (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ) (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33125/262144 : ℝ)) 5 (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ) (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ) (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ) (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33125/262144 : ℝ)) 6 (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ) (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ) (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ) (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33125/262144 : ℝ)) 7 (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ) (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ) (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ) (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33125/262144 : ℝ))) (35268510703/200000000000 : ℝ) (176342553521/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33125/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35268510703/200000000000 : ℝ) (176342553521/1000000000000 : ℝ) (588171276757/1000000000000 : ℝ) (588171276761/1000000000000 : ℝ) (209965802879/500000000000 : ℝ) (209965802883/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33125/262144 : ℝ))) 1 (588171276757/1000000000000 : ℝ) (588171276761/1000000000000 : ℝ) (209965802879/500000000000 : ℝ) (209965802883/500000000000 : ℝ) (504051441257/1000000000000 : ℝ) (31503215079/62500000000 : ℝ) (49698260403/100000000000 : ℝ) (248491302019/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33125/262144 : ℝ))) 2 (504051441257/1000000000000 : ℝ) (31503215079/62500000000 : ℝ) (49698260403/100000000000 : ℝ) (248491302019/500000000000 : ℝ) (500517022643/1000000000000 : ℝ) (500517022651/1000000000000 : ℝ) (500504543277/1000000000000 : ℝ) (100100908657/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33125/262144 : ℝ))) 3 (500517022643/1000000000000 : ℝ) (500517022651/1000000000000 : ℝ) (500504543277/1000000000000 : ℝ) (100100908657/200000000000 : ℝ) (6256384787/12500000000 : ℝ) (62563847871/125000000000 : ℝ) (500510782921/1000000000000 : ℝ) (50051078293/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33125/262144 : ℝ))) 4 (6256384787/12500000000 : ℝ) (62563847871/125000000000 : ℝ) (500510782921/1000000000000 : ℝ) (50051078293/100000000000 : ℝ) (25025539147/50000000000 : ℝ) (500510782949/1000000000000 : ℝ) (25025539147/50000000000 : ℝ) (500510782949/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33125/262144 : ℝ))) 5 (25025539147/50000000000 : ℝ) (500510782949/1000000000000 : ℝ) (25025539147/50000000000 : ℝ) (500510782949/1000000000000 : ℝ) (25025539147/50000000000 : ℝ) (500510782949/1000000000000 : ℝ) (25025539147/50000000000 : ℝ) (500510782949/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33125/262144 : ℝ))) 6 (25025539147/50000000000 : ℝ) (500510782949/1000000000000 : ℝ) (25025539147/50000000000 : ℝ) (500510782949/1000000000000 : ℝ) (25025539147/50000000000 : ℝ) (500510782949/1000000000000 : ℝ) (25025539147/50000000000 : ℝ) (500510782949/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33125/262144 : ℝ))) 7 (25025539147/50000000000 : ℝ) (500510782949/1000000000000 : ℝ) (25025539147/50000000000 : ℝ) (500510782949/1000000000000 : ℝ) (25025539147/50000000000 : ℝ) (500510782949/1000000000000 : ℝ) (25025539147/50000000000 : ℝ) (500510782949/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33125/262144 : ℝ)) hmem 8 (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ) (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33125/262144 : ℝ))) hcmem 8 (25025539147/50000000000 : ℝ) (500510782949/1000000000000 : ℝ) (25025539147/50000000000 : ℝ) (500510782949/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33125/262144 : ℝ)) (992148959233/1000000000000 : ℝ) (248037239809/250000000000 : ℝ) (25025539147/50000000000 : ℝ) (500510782949/1000000000000 : ℝ) (99052729437/125000000000 : ℝ) (792421835513/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0344_exp_lower
  have heNumeric : (2054906930921/1000000000000 : ℝ)/4 ≤ Real.exp (-10657020852583/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906930921/1000000000000 : ℝ)/4 ≤ Real.exp ((8281/65536 : ℝ)-(792421835513/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8281/65536 : ℝ) (33125/262144 : ℝ) (792421835513/1000000000000 : ℝ) (2054906930921/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0345; no trusted numerical premise.
theorem cover8_leaf0345_exp_radius : (19960549690157537/20000000000000000 : ℝ) ≤ Real.exp ((-16563/1048576 : ℝ)/8) ∧ Real.exp ((-16563/1048576 : ℝ)/8) ≤ (998027484507876851/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16563/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0345_exp_lower : (920113746818028439/1000000000000000000 : ℝ) ≤ Real.exp ((-42628085112779/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628085112779/64000000000000 : ℝ)/8) ≤ (23002843670450711/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628085112779/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0345_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906876259/1000000000000 : ℝ) ≤ 4*Real.exp (33125/262144 : ℝ)*Real.exp (-mu (radius 8 (16563/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906876259/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16563/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0345_exp_radius
  have hrNumeric : (61520524389/62500000000 : ℝ) ≤ Real.exp (-16563/1048576 : ℝ) ∧ Real.exp (-16563/1048576 : ℝ) ≤ (39373135609/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61520524389/62500000000 : ℝ) ≤ (radius 8 (16563/131072 : ℝ)) ∧ (radius 8 (16563/131072 : ℝ)) ≤ (39373135609/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16563/131072 : ℝ)) (61520524389/62500000000 : ℝ) (39373135609/40000000000 : ℝ) (44086293361/250000000000 : ℝ) (3526903469/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16563/131072 : ℝ)) (61520524389/62500000000 : ℝ) (39373135609/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16563/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61520524389/62500000000 : ℝ) (39373135609/40000000000 : ℝ) (124020524389/125000000000 : ℝ) (992164195113/1000000000000 : ℝ) (992133252251/1000000000000 : ℝ) (992133252253/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16563/131072 : ℝ)) 1 (124020524389/125000000000 : ℝ) (992164195113/1000000000000 : ℝ) (992133252251/1000000000000 : ℝ) (992133252253/1000000000000 : ℝ) (992148723681/1000000000000 : ℝ) (992148723683/1000000000000 : ℝ) (24803718089/25000000000 : ℝ) (992148723563/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16563/131072 : ℝ)) 2 (992148723681/1000000000000 : ℝ) (992148723683/1000000000000 : ℝ) (24803718089/25000000000 : ℝ) (992148723563/1000000000000 : ℝ) (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ) (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16563/131072 : ℝ)) 3 (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ) (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ) (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ) (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16563/131072 : ℝ)) 4 (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ) (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ) (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ) (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16563/131072 : ℝ)) 5 (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ) (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ) (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ) (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16563/131072 : ℝ)) 6 (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ) (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ) (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ) (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16563/131072 : ℝ)) 7 (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ) (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ) (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ) (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16563/131072 : ℝ))) (44086293361/250000000000 : ℝ) (3526903469/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16563/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44086293361/250000000000 : ℝ) (3526903469/20000000000 : ℝ) (294086293361/500000000000 : ℝ) (23526903469/40000000000 : ℝ) (209967362609/500000000000 : ℝ) (209967362613/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16563/131072 : ℝ))) 1 (294086293361/500000000000 : ℝ) (23526903469/40000000000 : ℝ) (209967362609/500000000000 : ℝ) (209967362613/500000000000 : ℝ) (50405365597/100000000000 : ℝ) (63006706997/125000000000 : ℝ) (496985003381/1000000000000 : ℝ) (124246250847/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16563/131072 : ℝ))) 2 (50405365597/100000000000 : ℝ) (63006706997/125000000000 : ℝ) (496985003381/1000000000000 : ℝ) (124246250847/250000000000 : ℝ) (20020773187/40000000000 : ℝ) (250259664841/500000000000 : ℝ) (250253425509/500000000000 : ℝ) (250253425513/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16563/131072 : ℝ))) 3 (20020773187/40000000000 : ℝ) (250259664841/500000000000 : ℝ) (250253425509/500000000000 : ℝ) (250253425513/500000000000 : ℝ) (250256545173/500000000000 : ℝ) (250256545177/500000000000 : ℝ) (500513090307/1000000000000 : ℝ) (125128272579/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16563/131072 : ℝ))) 4 (250256545173/500000000000 : ℝ) (250256545177/500000000000 : ℝ) (500513090307/1000000000000 : ℝ) (125128272579/250000000000 : ℝ) (250256545163/500000000000 : ℝ) (100102618067/200000000000 : ℝ) (250256545163/500000000000 : ℝ) (100102618067/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16563/131072 : ℝ))) 5 (250256545163/500000000000 : ℝ) (100102618067/200000000000 : ℝ) (250256545163/500000000000 : ℝ) (100102618067/200000000000 : ℝ) (250256545163/500000000000 : ℝ) (100102618067/200000000000 : ℝ) (250256545163/500000000000 : ℝ) (100102618067/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16563/131072 : ℝ))) 6 (250256545163/500000000000 : ℝ) (100102618067/200000000000 : ℝ) (250256545163/500000000000 : ℝ) (100102618067/200000000000 : ℝ) (250256545163/500000000000 : ℝ) (100102618067/200000000000 : ℝ) (250256545163/500000000000 : ℝ) (100102618067/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16563/131072 : ℝ))) 7 (250256545163/500000000000 : ℝ) (100102618067/200000000000 : ℝ) (250256545163/500000000000 : ℝ) (100102618067/200000000000 : ℝ) (250256545163/500000000000 : ℝ) (100102618067/200000000000 : ℝ) (250256545163/500000000000 : ℝ) (100102618067/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16563/131072 : ℝ)) hmem 8 (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ) (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16563/131072 : ℝ))) hcmem 8 (250256545163/500000000000 : ℝ) (100102618067/200000000000 : ℝ) (250256545163/500000000000 : ℝ) (100102618067/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16563/131072 : ℝ)) (49607436181/50000000000 : ℝ) (992148723623/1000000000000 : ℝ) (250256545163/500000000000 : ℝ) (100102618067/200000000000 : ℝ) (792425676793/1000000000000 : ℝ) (792425676811/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0345_exp_lower
  have heNumeric : (2054906876259/1000000000000 : ℝ)/4 ≤ Real.exp (-42628085112779/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906876259/1000000000000 : ℝ)/4 ≤ Real.exp ((33125/262144 : ℝ)-(792425676811/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33125/262144 : ℝ) (16563/131072 : ℝ) (792425676811/1000000000000 : ℝ) (2054906876259/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0346; no trusted numerical premise.
theorem cover8_leaf0346_exp_radius : (998027425020804933/1000000000000000000 : ℝ) ≤ Real.exp ((-33127/2097152 : ℝ)/8) ∧ Real.exp ((-33127/2097152 : ℝ)/8) ≤ (499013712510402467/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33127/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0346_exp_lower : (184022748753530379/200000000000000000 : ℝ) ≤ Real.exp ((-4262808681017/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262808681017/6400000000000 : ℝ)/8) ≤ (115014217970956487/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262808681017/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0346_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (3210791909/1562500000 : ℝ) ≤ 4*Real.exp (16563/131072 : ℝ)*Real.exp (-mu (radius 8 (33127/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (3210791909/1562500000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33127/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0346_exp_radius
  have hrNumeric : (49216396043/50000000000 : ℝ) ≤ Real.exp (-33127/2097152 : ℝ) ∧ Real.exp (-33127/2097152 : ℝ) ≤ (984327920861/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49216396043/50000000000 : ℝ) ≤ (radius 8 (33127/262144 : ℝ)) ∧ (radius 8 (33127/262144 : ℝ)) ≤ (984327920861/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33127/262144 : ℝ)) (49216396043/50000000000 : ℝ) (984327920861/1000000000000 : ℝ) (176347793333/1000000000000 : ℝ) (176347793339/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33127/262144 : ℝ)) (49216396043/50000000000 : ℝ) (984327920861/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33127/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49216396043/50000000000 : ℝ) (984327920861/1000000000000 : ℝ) (99216396043/100000000000 : ℝ) (992163960431/1000000000000 : ℝ) (992133015709/1000000000000 : ℝ) (99213301571/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33127/262144 : ℝ)) 1 (99216396043/100000000000 : ℝ) (992163960431/1000000000000 : ℝ) (992133015709/1000000000000 : ℝ) (99213301571/100000000000 : ℝ) (992148488069/1000000000000 : ℝ) (992148488071/1000000000000 : ℝ) (248037121987/250000000000 : ℝ) (19842969759/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33127/262144 : ℝ)) 2 (992148488069/1000000000000 : ℝ) (992148488071/1000000000000 : ℝ) (248037121987/250000000000 : ℝ) (19842969759/20000000000 : ℝ) (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ) (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33127/262144 : ℝ)) 3 (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ) (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ) (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ) (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33127/262144 : ℝ)) 4 (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ) (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ) (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ) (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33127/262144 : ℝ)) 5 (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ) (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ) (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ) (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33127/262144 : ℝ)) 6 (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ) (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ) (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ) (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33127/262144 : ℝ)) 7 (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ) (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ) (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ) (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33127/262144 : ℝ))) (176347793333/1000000000000 : ℝ) (176347793339/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33127/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176347793333/1000000000000 : ℝ) (176347793339/1000000000000 : ℝ) (294086948333/500000000000 : ℝ) (58817389667/100000000000 : ℝ) (209968922303/500000000000 : ℝ) (209968922307/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33127/262144 : ℝ))) 1 (294086948333/500000000000 : ℝ) (58817389667/100000000000 : ℝ) (209968922303/500000000000 : ℝ) (209968922307/500000000000 : ℝ) (126013967659/250000000000 : ℝ) (252027935321/500000000000 : ℝ) (124246850669/250000000000 : ℝ) (124246850671/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33127/262144 : ℝ))) 2 (126013967659/250000000000 : ℝ) (252027935321/500000000000 : ℝ) (124246850669/250000000000 : ℝ) (124246850671/250000000000 : ℝ) (31282602291/62500000000 : ℝ) (500521636663/1000000000000 : ℝ) (125127289677/250000000000 : ℝ) (125127289679/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33127/262144 : ℝ))) 3 (31282602291/62500000000 : ℝ) (500521636663/1000000000000 : ℝ) (125127289677/250000000000 : ℝ) (125127289679/250000000000 : ℝ) (250257698841/500000000000 : ℝ) (50051539769/100000000000 : ℝ) (500515397643/1000000000000 : ℝ) (500515397651/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33127/262144 : ℝ))) 4 (250257698841/500000000000 : ℝ) (50051539769/100000000000 : ℝ) (500515397643/1000000000000 : ℝ) (500515397651/1000000000000 : ℝ) (250257698831/500000000000 : ℝ) (500515397671/1000000000000 : ℝ) (250257698831/500000000000 : ℝ) (500515397671/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33127/262144 : ℝ))) 5 (250257698831/500000000000 : ℝ) (500515397671/1000000000000 : ℝ) (250257698831/500000000000 : ℝ) (500515397671/1000000000000 : ℝ) (250257698831/500000000000 : ℝ) (500515397671/1000000000000 : ℝ) (250257698831/500000000000 : ℝ) (500515397671/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33127/262144 : ℝ))) 6 (250257698831/500000000000 : ℝ) (500515397671/1000000000000 : ℝ) (250257698831/500000000000 : ℝ) (500515397671/1000000000000 : ℝ) (250257698831/500000000000 : ℝ) (500515397671/1000000000000 : ℝ) (250257698831/500000000000 : ℝ) (500515397671/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33127/262144 : ℝ))) 7 (250257698831/500000000000 : ℝ) (500515397671/1000000000000 : ℝ) (250257698831/500000000000 : ℝ) (500515397671/1000000000000 : ℝ) (250257698831/500000000000 : ℝ) (500515397671/1000000000000 : ℝ) (250257698831/500000000000 : ℝ) (500515397671/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33127/262144 : ℝ)) hmem 8 (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ) (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33127/262144 : ℝ))) hcmem 8 (250257698831/500000000000 : ℝ) (500515397671/1000000000000 : ℝ) (250257698831/500000000000 : ℝ) (500515397671/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33127/262144 : ℝ)) (124018561001/125000000000 : ℝ) (992148488011/1000000000000 : ℝ) (250257698831/500000000000 : ℝ) (500515397671/1000000000000 : ℝ) (198107379503/250000000000 : ℝ) (79242951803/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0346_exp_lower
  have heNumeric : (3210791909/1562500000 : ℝ)/4 ≤ Real.exp (-4262808681017/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (3210791909/1562500000 : ℝ)/4 ≤ Real.exp ((16563/131072 : ℝ)-(79242951803/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16563/131072 : ℝ) (33127/262144 : ℝ) (79242951803/100000000000 : ℝ) (3210791909/1562500000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0347; no trusted numerical premise.
theorem cover8_leaf0347_exp_radius : (499013682766868281/500000000000000000 : ℝ) ≤ Real.exp ((-4141/262144 : ℝ)/8) ∧ Real.exp ((-4141/262144 : ℝ)/8) ≤ (998027365533736563/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4141/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0347_exp_lower : (920113740725096329/1000000000000000000 : ℝ) ≤ Real.exp ((-42628088503209/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628088503209/64000000000000 : ℝ)/8) ≤ (92011374072509633/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628088503209/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0347_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (10274533837/5000000000 : ℝ) ≤ 4*Real.exp (33127/262144 : ℝ)*Real.exp (-mu (radius 8 (4141/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (10274533837/5000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4141/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0347_exp_radius
  have hrNumeric : (196865490299/200000000000 : ℝ) ≤ Real.exp (-4141/262144 : ℝ) ∧ Real.exp (-4141/262144 : ℝ) ≤ (123040931437/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196865490299/200000000000 : ℝ) ≤ (radius 8 (4141/32768 : ℝ)) ∧ (radius 8 (4141/32768 : ℝ)) ≤ (123040931437/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4141/32768 : ℝ)) (196865490299/200000000000 : ℝ) (123040931437/125000000000 : ℝ) (176350413187/1000000000000 : ℝ) (88175206597/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4141/32768 : ℝ)) (196865490299/200000000000 : ℝ) (123040931437/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4141/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196865490299/200000000000 : ℝ) (123040931437/125000000000 : ℝ) (992163725747/1000000000000 : ℝ) (248040931437/250000000000 : ℝ) (198426555833/200000000000 : ℝ) (992132779167/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4141/32768 : ℝ)) 1 (992163725747/1000000000000 : ℝ) (248040931437/250000000000 : ℝ) (198426555833/200000000000 : ℝ) (992132779167/1000000000000 : ℝ) (124018531557/125000000000 : ℝ) (496074126229/500000000000 : ℝ) (198429650467/200000000000 : ℝ) (992148252337/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4141/32768 : ℝ)) 2 (124018531557/125000000000 : ℝ) (496074126229/500000000000 : ℝ) (198429650467/200000000000 : ℝ) (992148252337/1000000000000 : ℝ) (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ) (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4141/32768 : ℝ)) 3 (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ) (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ) (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ) (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4141/32768 : ℝ)) 4 (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ) (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ) (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ) (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4141/32768 : ℝ)) 5 (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ) (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ) (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ) (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4141/32768 : ℝ)) 6 (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ) (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ) (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ) (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4141/32768 : ℝ)) 7 (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ) (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ) (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ) (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4141/32768 : ℝ))) (176350413187/1000000000000 : ℝ) (88175206597/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4141/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176350413187/1000000000000 : ℝ) (88175206597/500000000000 : ℝ) (588175206593/1000000000000 : ℝ) (588175206597/1000000000000 : ℝ) (41994096393/100000000000 : ℝ) (419940963939/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4141/32768 : ℝ))) 1 (588175206593/1000000000000 : ℝ) (588175206597/1000000000000 : ℝ) (41994096393/100000000000 : ℝ) (419940963939/1000000000000 : ℝ) (504058085261/1000000000000 : ℝ) (126014521317/250000000000 : ℝ) (496989801923/1000000000000 : ℝ) (496989801931/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4141/32768 : ℝ))) 2 (504058085261/1000000000000 : ℝ) (126014521317/250000000000 : ℝ) (496989801923/1000000000000 : ℝ) (496989801931/1000000000000 : ℝ) (62565492949/125000000000 : ℝ) (1251309859/2500000000 : ℝ) (500511466353/1000000000000 : ℝ) (250255733181/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4141/32768 : ℝ))) 3 (62565492949/125000000000 : ℝ) (1251309859/2500000000 : ℝ) (500511466353/1000000000000 : ℝ) (250255733181/500000000000 : ℝ) (125129426243/250000000000 : ℝ) (500517704981/1000000000000 : ℝ) (500517704933/1000000000000 : ℝ) (500517704943/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4141/32768 : ℝ))) 4 (125129426243/250000000000 : ℝ) (500517704981/1000000000000 : ℝ) (500517704933/1000000000000 : ℝ) (500517704943/1000000000000 : ℝ) (62564713119/125000000000 : ℝ) (250258852481/500000000000 : ℝ) (62564713119/125000000000 : ℝ) (250258852481/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4141/32768 : ℝ))) 5 (62564713119/125000000000 : ℝ) (250258852481/500000000000 : ℝ) (62564713119/125000000000 : ℝ) (250258852481/500000000000 : ℝ) (62564713119/125000000000 : ℝ) (250258852481/500000000000 : ℝ) (62564713119/125000000000 : ℝ) (250258852481/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4141/32768 : ℝ))) 6 (62564713119/125000000000 : ℝ) (250258852481/500000000000 : ℝ) (62564713119/125000000000 : ℝ) (250258852481/500000000000 : ℝ) (62564713119/125000000000 : ℝ) (250258852481/500000000000 : ℝ) (62564713119/125000000000 : ℝ) (250258852481/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4141/32768 : ℝ))) 7 (62564713119/125000000000 : ℝ) (250258852481/500000000000 : ℝ) (62564713119/125000000000 : ℝ) (250258852481/500000000000 : ℝ) (62564713119/125000000000 : ℝ) (250258852481/500000000000 : ℝ) (62564713119/125000000000 : ℝ) (250258852481/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4141/32768 : ℝ)) hmem 8 (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ) (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4141/32768 : ℝ))) hcmem 8 (62564713119/125000000000 : ℝ) (250258852481/500000000000 : ℝ) (62564713119/125000000000 : ℝ) (250258852481/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4141/32768 : ℝ)) (198429650479/200000000000 : ℝ) (496074126199/500000000000 : ℝ) (62564713119/125000000000 : ℝ) (250258852481/500000000000 : ℝ) (792433359161/1000000000000 : ℝ) (792433359181/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0347_exp_lower
  have heNumeric : (10274533837/5000000000 : ℝ)/4 ≤ Real.exp (-42628088503209/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (10274533837/5000000000 : ℝ)/4 ≤ Real.exp ((33127/262144 : ℝ)-(792433359181/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33127/262144 : ℝ) (4141/32768 : ℝ) (792433359181/1000000000000 : ℝ) (10274533837/5000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0348; no trusted numerical premise.
theorem cover8_leaf0348_exp_radius : (124753413255833967/125000000000000000 : ℝ) ≤ Real.exp ((-33129/2097152 : ℝ)/8) ∧ Real.exp ((-33129/2097152 : ℝ)/8) ≤ (998027306046671737/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33129/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0348_exp_lower : (460056868846618547/500000000000000000 : ℝ) ≤ Real.exp ((-5328511273787/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328511273787/8000000000000 : ℝ)/8) ≤ (184022747538647419/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328511273787/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0348_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906713231/1000000000000 : ℝ) ≤ 4*Real.exp (4141/32768 : ℝ)*Real.exp (-mu (radius 8 (33129/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906713231/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33129/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0348_exp_radius
  have hrNumeric : (246081745533/250000000000 : ℝ) ≤ Real.exp (-33129/2097152 : ℝ) ∧ Real.exp (-33129/2097152 : ℝ) ≤ (984326982133/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246081745533/250000000000 : ℝ) ≤ (radius 8 (33129/262144 : ℝ)) ∧ (radius 8 (33129/262144 : ℝ)) ≤ (984326982133/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33129/262144 : ℝ)) (246081745533/250000000000 : ℝ) (984326982133/1000000000000 : ℝ) (17635303299/100000000000 : ℝ) (176353032997/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33129/262144 : ℝ)) (246081745533/250000000000 : ℝ) (984326982133/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33129/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246081745533/250000000000 : ℝ) (984326982133/1000000000000 : ℝ) (496081745533/500000000000 : ℝ) (992163491067/1000000000000 : ℝ) (992132542623/1000000000000 : ℝ) (31004141957/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33129/262144 : ℝ)) 1 (496081745533/500000000000 : ℝ) (992163491067/1000000000000 : ℝ) (992132542623/1000000000000 : ℝ) (31004141957/31250000000 : ℝ) (248037004211/250000000000 : ℝ) (496074008423/500000000000 : ℝ) (992148016723/1000000000000 : ℝ) (39685920669/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33129/262144 : ℝ)) 2 (248037004211/250000000000 : ℝ) (496074008423/500000000000 : ℝ) (992148016723/1000000000000 : ℝ) (39685920669/40000000000 : ℝ) (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ) (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33129/262144 : ℝ)) 3 (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ) (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ) (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ) (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33129/262144 : ℝ)) 4 (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ) (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ) (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ) (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33129/262144 : ℝ)) 5 (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ) (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ) (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ) (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33129/262144 : ℝ)) 6 (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ) (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ) (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ) (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33129/262144 : ℝ)) 7 (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ) (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ) (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ) (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33129/262144 : ℝ))) (17635303299/100000000000 : ℝ) (176353032997/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33129/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17635303299/100000000000 : ℝ) (176353032997/1000000000000 : ℝ) (117635303299/200000000000 : ℝ) (588176516499/1000000000000 : ℝ) (41994408317/100000000000 : ℝ) (419944083179/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33129/262144 : ℝ))) 1 (117635303299/200000000000 : ℝ) (588176516499/1000000000000 : ℝ) (41994408317/100000000000 : ℝ) (419944083179/1000000000000 : ℝ) (63007537479/125000000000 : ℝ) (504060299839/1000000000000 : ℝ) (496992201107/1000000000000 : ℝ) (99398440223/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33129/262144 : ℝ))) 2 (63007537479/125000000000 : ℝ) (504060299839/1000000000000 : ℝ) (496992201107/1000000000000 : ℝ) (99398440223/200000000000 : ℝ) (500526250469/1000000000000 : ℝ) (500526250477/1000000000000 : ℝ) (25025688697/50000000000 : ℝ) (500513773949/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33129/262144 : ℝ))) 3 (500526250469/1000000000000 : ℝ) (500526250477/1000000000000 : ℝ) (25025688697/50000000000 : ℝ) (500513773949/1000000000000 : ℝ) (125130003051/250000000000 : ℝ) (500520012213/1000000000000 : ℝ) (100104002433/200000000000 : ℝ) (20020800487/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33129/262144 : ℝ))) 4 (125130003051/250000000000 : ℝ) (500520012213/1000000000000 : ℝ) (100104002433/200000000000 : ℝ) (20020800487/40000000000 : ℝ) (62565001523/125000000000 : ℝ) (250260006097/500000000000 : ℝ) (62565001523/125000000000 : ℝ) (250260006097/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33129/262144 : ℝ))) 5 (62565001523/125000000000 : ℝ) (250260006097/500000000000 : ℝ) (62565001523/125000000000 : ℝ) (250260006097/500000000000 : ℝ) (62565001523/125000000000 : ℝ) (250260006097/500000000000 : ℝ) (62565001523/125000000000 : ℝ) (250260006097/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33129/262144 : ℝ))) 6 (62565001523/125000000000 : ℝ) (250260006097/500000000000 : ℝ) (62565001523/125000000000 : ℝ) (250260006097/500000000000 : ℝ) (62565001523/125000000000 : ℝ) (250260006097/500000000000 : ℝ) (62565001523/125000000000 : ℝ) (250260006097/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33129/262144 : ℝ))) 7 (62565001523/125000000000 : ℝ) (250260006097/500000000000 : ℝ) (62565001523/125000000000 : ℝ) (250260006097/500000000000 : ℝ) (62565001523/125000000000 : ℝ) (250260006097/500000000000 : ℝ) (62565001523/125000000000 : ℝ) (250260006097/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33129/262144 : ℝ)) hmem 8 (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ) (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33129/262144 : ℝ))) hcmem 8 (62565001523/125000000000 : ℝ) (250260006097/500000000000 : ℝ) (62565001523/125000000000 : ℝ) (250260006097/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33129/262144 : ℝ)) (992148016783/1000000000000 : ℝ) (496074008393/500000000000 : ℝ) (62565001523/125000000000 : ℝ) (250260006097/500000000000 : ℝ) (39621860011/50000000000 : ℝ) (792437200239/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0348_exp_lower
  have heNumeric : (2054906713231/1000000000000 : ℝ)/4 ≤ Real.exp (-5328511273787/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906713231/1000000000000 : ℝ)/4 ≤ Real.exp ((4141/32768 : ℝ)-(792437200239/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4141/32768 : ℝ) (33129/262144 : ℝ) (792437200239/1000000000000 : ℝ) (2054906713231/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0349; no trusted numerical premise.
theorem cover8_leaf0349_exp_radius : (199605449311922091/200000000000000000 : ℝ) ≤ Real.exp ((-16565/1048576 : ℝ)/8) ∧ Real.exp ((-16565/1048576 : ℝ)/8) ≤ (124753405819951307/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16565/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0349_exp_lower : (920113734669313851/1000000000000000000 : ℝ) ≤ Real.exp ((-42628091872967/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628091872967/64000000000000 : ℝ)/8) ≤ (230028433667328463/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628091872967/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0349_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726664801/250000000000 : ℝ) ≤ 4*Real.exp (33129/262144 : ℝ)*Real.exp (-mu (radius 8 (16565/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513726664801/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16565/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0349_exp_radius
  have hrNumeric : (7690050881/7812500000 : ℝ) ≤ Real.exp (-16565/1048576 : ℝ) ∧ Real.exp (-16565/1048576 : ℝ) ≤ (984326512769/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (7690050881/7812500000 : ℝ) ≤ (radius 8 (16565/131072 : ℝ)) ∧ (radius 8 (16565/131072 : ℝ)) ≤ (984326512769/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16565/131072 : ℝ)) (7690050881/7812500000 : ℝ) (984326512769/1000000000000 : ℝ) (88177826379/500000000000 : ℝ) (35271130553/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16565/131072 : ℝ)) (7690050881/7812500000 : ℝ) (984326512769/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16565/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (7690050881/7812500000 : ℝ) (984326512769/1000000000000 : ℝ) (15502550881/15625000000 : ℝ) (198432651277/200000000000 : ℝ) (6200826913/6250000000 : ℝ) (992132306081/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16565/131072 : ℝ)) 1 (15502550881/15625000000 : ℝ) (198432651277/200000000000 : ℝ) (6200826913/6250000000 : ℝ) (992132306081/1000000000000 : ℝ) (62009236327/62500000000 : ℝ) (992147781233/1000000000000 : ℝ) (992147781111/1000000000000 : ℝ) (992147781113/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16565/131072 : ℝ)) 2 (62009236327/62500000000 : ℝ) (992147781233/1000000000000 : ℝ) (992147781111/1000000000000 : ℝ) (992147781113/1000000000000 : ℝ) (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ) (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16565/131072 : ℝ)) 3 (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ) (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ) (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ) (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16565/131072 : ℝ)) 4 (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ) (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ) (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ) (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16565/131072 : ℝ)) 5 (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ) (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ) (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ) (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16565/131072 : ℝ)) 6 (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ) (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ) (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ) (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16565/131072 : ℝ)) 7 (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ) (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ) (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ) (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16565/131072 : ℝ))) (88177826379/500000000000 : ℝ) (35271130553/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16565/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88177826379/500000000000 : ℝ) (35271130553/200000000000 : ℝ) (588177826379/1000000000000 : ℝ) (588177826383/1000000000000 : ℝ) (83989440469/200000000000 : ℝ) (83989440471/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16565/131072 : ℝ))) 1 (588177826379/1000000000000 : ℝ) (588177826383/1000000000000 : ℝ) (83989440469/200000000000 : ℝ) (83989440471/200000000000 : ℝ) (252031257181/500000000000 : ℝ) (504062514369/1000000000000 : ℝ) (496994600241/1000000000000 : ℝ) (1987978401/4000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16565/131072 : ℝ))) 2 (252031257181/500000000000 : ℝ) (504062514369/1000000000000 : ℝ) (496994600241/1000000000000 : ℝ) (1987978401/4000000000 : ℝ) (500528557301/1000000000000 : ℝ) (50052855731/100000000000 : ℝ) (500516081481/1000000000000 : ℝ) (50051608149/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16565/131072 : ℝ))) 3 (500528557301/1000000000000 : ℝ) (50052855731/100000000000 : ℝ) (500516081481/1000000000000 : ℝ) (50051608149/100000000000 : ℝ) (500522319391/1000000000000 : ℝ) (2502611597/5000000000 : ℝ) (62565289919/125000000000 : ℝ) (250261159681/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16565/131072 : ℝ))) 4 (500522319391/1000000000000 : ℝ) (2502611597/5000000000 : ℝ) (62565289919/125000000000 : ℝ) (250261159681/500000000000 : ℝ) (500522319371/1000000000000 : ℝ) (500522319381/1000000000000 : ℝ) (500522319371/1000000000000 : ℝ) (500522319381/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16565/131072 : ℝ))) 5 (500522319371/1000000000000 : ℝ) (500522319381/1000000000000 : ℝ) (500522319371/1000000000000 : ℝ) (500522319381/1000000000000 : ℝ) (500522319371/1000000000000 : ℝ) (500522319381/1000000000000 : ℝ) (500522319371/1000000000000 : ℝ) (500522319381/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16565/131072 : ℝ))) 6 (500522319371/1000000000000 : ℝ) (500522319381/1000000000000 : ℝ) (500522319371/1000000000000 : ℝ) (500522319381/1000000000000 : ℝ) (500522319371/1000000000000 : ℝ) (500522319381/1000000000000 : ℝ) (500522319371/1000000000000 : ℝ) (500522319381/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16565/131072 : ℝ))) 7 (500522319371/1000000000000 : ℝ) (500522319381/1000000000000 : ℝ) (500522319371/1000000000000 : ℝ) (500522319381/1000000000000 : ℝ) (500522319371/1000000000000 : ℝ) (500522319381/1000000000000 : ℝ) (500522319371/1000000000000 : ℝ) (500522319381/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16565/131072 : ℝ)) hmem 8 (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ) (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16565/131072 : ℝ))) hcmem 8 (500522319371/1000000000000 : ℝ) (500522319381/1000000000000 : ℝ) (500522319371/1000000000000 : ℝ) (500522319381/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16565/131072 : ℝ)) (992147781171/1000000000000 : ℝ) (992147781173/1000000000000 : ℝ) (500522319371/1000000000000 : ℝ) (500522319381/1000000000000 : ℝ) (792441041209/1000000000000 : ℝ) (198110260307/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0349_exp_lower
  have heNumeric : (513726664801/250000000000 : ℝ)/4 ≤ Real.exp (-42628091872967/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726664801/250000000000 : ℝ)/4 ≤ Real.exp ((33129/262144 : ℝ)-(198110260307/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33129/262144 : ℝ) (16565/131072 : ℝ) (198110260307/250000000000 : ℝ) (513726664801/250000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0325_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0325_certificate
#check SmaleRate.Proofs.cover8_leaf0326_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0326_certificate
#check SmaleRate.Proofs.cover8_leaf0327_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0327_certificate
#check SmaleRate.Proofs.cover8_leaf0328_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0328_certificate
#check SmaleRate.Proofs.cover8_leaf0329_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0329_certificate
#check SmaleRate.Proofs.cover8_leaf0330_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0330_certificate
#check SmaleRate.Proofs.cover8_leaf0331_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0331_certificate
#check SmaleRate.Proofs.cover8_leaf0332_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0332_certificate
#check SmaleRate.Proofs.cover8_leaf0333_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0333_certificate
#check SmaleRate.Proofs.cover8_leaf0334_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0334_certificate
#check SmaleRate.Proofs.cover8_leaf0335_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0335_certificate
#check SmaleRate.Proofs.cover8_leaf0336_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0336_certificate
#check SmaleRate.Proofs.cover8_leaf0337_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0337_certificate
#check SmaleRate.Proofs.cover8_leaf0338_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0338_certificate
#check SmaleRate.Proofs.cover8_leaf0339_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0339_certificate
#check SmaleRate.Proofs.cover8_leaf0340_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0340_certificate
#check SmaleRate.Proofs.cover8_leaf0341_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0341_certificate
#check SmaleRate.Proofs.cover8_leaf0342_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0342_certificate
#check SmaleRate.Proofs.cover8_leaf0343_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0343_certificate
#check SmaleRate.Proofs.cover8_leaf0344_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0344_certificate
#check SmaleRate.Proofs.cover8_leaf0345_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0345_certificate
#check SmaleRate.Proofs.cover8_leaf0346_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0346_certificate
#check SmaleRate.Proofs.cover8_leaf0347_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0347_certificate
#check SmaleRate.Proofs.cover8_leaf0348_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0348_certificate
#check SmaleRate.Proofs.cover8_leaf0349_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0349_certificate
