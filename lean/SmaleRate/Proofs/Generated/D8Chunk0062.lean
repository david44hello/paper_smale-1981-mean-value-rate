/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1550; no trusted numerical premise.
theorem cover8_leaf1550_exp_radius : (39918448724313629/40000000000000000 : ℝ) ≤ Real.exp ((-535/32768 : ℝ)/8) ∧ Real.exp ((-535/32768 : ℝ)/8) ≤ (498980609053920363/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-535/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1550_exp_lower : (11501431713408483/12500000000000000 : ℝ) ≤ Real.exp ((-10656911343361/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656911343361/16000000000000 : ℝ)/8) ≤ (920114537072678641/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656911343361/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1550_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054920995423/1000000000000 : ℝ) ≤ 4*Real.exp (8559/65536 : ℝ)*Real.exp (-mu (radius 8 (535/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2054920995423/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (535/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1550_exp_radius
  have hrNumeric : (196761131437/200000000000 : ℝ) ≤ Real.exp (-535/32768 : ℝ) ∧ Real.exp (-535/32768 : ℝ) ≤ (491902828593/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196761131437/200000000000 : ℝ) ≤ (radius 8 (535/4096 : ℝ)) ∧ (radius 8 (535/4096 : ℝ)) ≤ (491902828593/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (535/4096 : ℝ)) (196761131437/200000000000 : ℝ) (491902828593/500000000000 : ℝ) (44809617333/250000000000 : ℝ) (179238469339/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (535/4096 : ℝ)) (196761131437/200000000000 : ℝ) (491902828593/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (535/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196761131437/200000000000 : ℝ) (491902828593/500000000000 : ℝ) (61993926787/62500000000 : ℝ) (991902828593/1000000000000 : ℝ) (49593488917/50000000000 : ℝ) (991869778341/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (535/4096 : ℝ)) 1 (61993926787/62500000000 : ℝ) (991902828593/1000000000000 : ℝ) (49593488917/50000000000 : ℝ) (991869778341/1000000000000 : ℝ) (495943151733/500000000000 : ℝ) (991886303467/1000000000000 : ℝ) (30996446979/31250000000 : ℝ) (99188630333/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (535/4096 : ℝ)) 2 (495943151733/500000000000 : ℝ) (991886303467/1000000000000 : ℝ) (30996446979/31250000000 : ℝ) (99188630333/100000000000 : ℝ) (991886303397/1000000000000 : ℝ) (991886303399/1000000000000 : ℝ) (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (535/4096 : ℝ)) 3 (991886303397/1000000000000 : ℝ) (991886303399/1000000000000 : ℝ) (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ) (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ) (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (535/4096 : ℝ)) 4 (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ) (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ) (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ) (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (535/4096 : ℝ)) 5 (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ) (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ) (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ) (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (535/4096 : ℝ)) 6 (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ) (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ) (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ) (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (535/4096 : ℝ)) 7 (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ) (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ) (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ) (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (535/4096 : ℝ))) (44809617333/250000000000 : ℝ) (179238469339/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (535/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44809617333/250000000000 : ℝ) (179238469339/1000000000000 : ℝ) (294809617333/500000000000 : ℝ) (58961923467/100000000000 : ℝ) (423365644959/1000000000000 : ℝ) (52920705621/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (535/4096 : ℝ))) 1 (294809617333/500000000000 : ℝ) (58961923467/100000000000 : ℝ) (423365644959/1000000000000 : ℝ) (52920705621/125000000000 : ℝ) (126623109953/250000000000 : ℝ) (506492439819/1000000000000 : ℝ) (499624386479/1000000000000 : ℝ) (499624386487/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (535/4096 : ℝ))) 2 (126623109953/250000000000 : ℝ) (506492439819/1000000000000 : ℝ) (499624386479/1000000000000 : ℝ) (499624386487/1000000000000 : ℝ) (100611682629/200000000000 : ℝ) (503058413153/1000000000000 : ℝ) (125761673041/250000000000 : ℝ) (125761673043/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (535/4096 : ℝ))) 3 (100611682629/200000000000 : ℝ) (503058413153/1000000000000 : ℝ) (125761673041/250000000000 : ℝ) (125761673043/250000000000 : ℝ) (251526276327/500000000000 : ℝ) (503052552663/1000000000000 : ℝ) (25152627631/50000000000 : ℝ) (503052552629/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (535/4096 : ℝ))) 4 (251526276327/500000000000 : ℝ) (503052552663/1000000000000 : ℝ) (25152627631/50000000000 : ℝ) (503052552629/1000000000000 : ℝ) (503052552637/1000000000000 : ℝ) (251526276323/500000000000 : ℝ) (125763138159/250000000000 : ℝ) (251526276323/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (535/4096 : ℝ))) 5 (503052552637/1000000000000 : ℝ) (251526276323/500000000000 : ℝ) (125763138159/250000000000 : ℝ) (251526276323/500000000000 : ℝ) (125763138159/250000000000 : ℝ) (251526276323/500000000000 : ℝ) (125763138159/250000000000 : ℝ) (251526276323/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (535/4096 : ℝ))) 6 (125763138159/250000000000 : ℝ) (251526276323/500000000000 : ℝ) (125763138159/250000000000 : ℝ) (251526276323/500000000000 : ℝ) (125763138159/250000000000 : ℝ) (251526276323/500000000000 : ℝ) (125763138159/250000000000 : ℝ) (251526276323/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (535/4096 : ℝ))) 7 (125763138159/250000000000 : ℝ) (251526276323/500000000000 : ℝ) (125763138159/250000000000 : ℝ) (251526276323/500000000000 : ℝ) (125763138159/250000000000 : ℝ) (251526276323/500000000000 : ℝ) (125763138159/250000000000 : ℝ) (251526276323/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (535/4096 : ℝ)) hmem 8 (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ) (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (535/4096 : ℝ))) hcmem 8 (125763138159/250000000000 : ℝ) (251526276323/500000000000 : ℝ) (125763138159/250000000000 : ℝ) (251526276323/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (535/4096 : ℝ)) (247971575849/250000000000 : ℝ) (991886303399/1000000000000 : ℝ) (125763138159/250000000000 : ℝ) (251526276323/500000000000 : ℝ) (796656934527/1000000000000 : ℝ) (398328467273/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1550_exp_lower
  have heNumeric : (2054920995423/1000000000000 : ℝ)/4 ≤ Real.exp (-10656911343361/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054920995423/1000000000000 : ℝ)/4 ≤ Real.exp ((8559/65536 : ℝ)-(398328467273/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8559/65536 : ℝ) (535/4096 : ℝ) (398328467273/500000000000 : ℝ) (2054920995423/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1551; no trusted numerical premise.
theorem cover8_leaf1551_exp_radius : (997960980175373469/1000000000000000000 : ℝ) ≤ Real.exp ((-8561/524288 : ℝ)/8) ∧ Real.exp ((-8561/524288 : ℝ)/8) ≤ (99796098017537347/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8561/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1551_exp_lower : (5750716025686199/6250000000000000 : ℝ) ≤ Real.exp ((-166514180971/250000000000 : ℝ)/8) ∧ Real.exp ((-166514180971/250000000000 : ℝ)/8) ≤ (920114564109791841/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-166514180971/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1551_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027460739243/500000000000 : ℝ) ≤ 4*Real.exp (535/4096 : ℝ)*Real.exp (-mu (radius 8 (8561/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027460739243/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8561/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1551_exp_radius
  have hrNumeric : (491901890363/500000000000 : ℝ) ≤ Real.exp (-8561/524288 : ℝ) ∧ Real.exp (-8561/524288 : ℝ) ≤ (983803780727/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491901890363/500000000000 : ℝ) ≤ (radius 8 (8561/65536 : ℝ)) ∧ (radius 8 (8561/65536 : ℝ)) ≤ (983803780727/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8561/65536 : ℝ)) (491901890363/500000000000 : ℝ) (983803780727/1000000000000 : ℝ) (179248768551/1000000000000 : ℝ) (89624384279/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8561/65536 : ℝ)) (491901890363/500000000000 : ℝ) (983803780727/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8561/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491901890363/500000000000 : ℝ) (983803780727/1000000000000 : ℝ) (991901890363/1000000000000 : ℝ) (247975472591/250000000000 : ℝ) (991868832419/1000000000000 : ℝ) (991868832421/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8561/65536 : ℝ)) 1 (991901890363/1000000000000 : ℝ) (247975472591/250000000000 : ℝ) (991868832419/1000000000000 : ℝ) (991868832421/1000000000000 : ℝ) (991885361391/1000000000000 : ℝ) (991885361393/1000000000000 : ℝ) (991885361253/1000000000000 : ℝ) (198377072251/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8561/65536 : ℝ)) 2 (991885361391/1000000000000 : ℝ) (991885361393/1000000000000 : ℝ) (991885361253/1000000000000 : ℝ) (198377072251/200000000000 : ℝ) (495942680661/500000000000 : ℝ) (247971340331/250000000000 : ℝ) (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8561/65536 : ℝ)) 3 (495942680661/500000000000 : ℝ) (247971340331/250000000000 : ℝ) (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ) (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ) (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8561/65536 : ℝ)) 4 (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ) (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ) (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ) (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8561/65536 : ℝ)) 5 (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ) (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ) (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ) (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8561/65536 : ℝ)) 6 (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ) (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ) (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ) (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8561/65536 : ℝ)) 7 (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ) (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ) (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ) (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8561/65536 : ℝ))) (179248768551/1000000000000 : ℝ) (89624384279/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8561/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179248768551/1000000000000 : ℝ) (89624384279/500000000000 : ℝ) (23584975371/40000000000 : ℝ) (589624384279/1000000000000 : ℝ) (13230556509/31250000000 : ℝ) (423377808297/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8561/65536 : ℝ))) 1 (23584975371/40000000000 : ℝ) (589624384279/1000000000000 : ℝ) (13230556509/31250000000 : ℝ) (423377808297/1000000000000 : ℝ) (506501096281/1000000000000 : ℝ) (15828159259/31250000000 : ℝ) (99926749077/200000000000 : ℝ) (499633745393/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8561/65536 : ℝ))) 2 (506501096281/1000000000000 : ℝ) (15828159259/31250000000 : ℝ) (99926749077/200000000000 : ℝ) (499633745393/1000000000000 : ℝ) (503067420833/1000000000000 : ℝ) (503067420841/1000000000000 : ℝ) (251527851229/500000000000 : ℝ) (503055702467/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8561/65536 : ℝ))) 3 (503067420833/1000000000000 : ℝ) (503067420841/1000000000000 : ℝ) (251527851229/500000000000 : ℝ) (503055702467/1000000000000 : ℝ) (100612312329/200000000000 : ℝ) (251530780827/500000000000 : ℝ) (503061561611/1000000000000 : ℝ) (25153078081/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8561/65536 : ℝ))) 4 (100612312329/200000000000 : ℝ) (251530780827/500000000000 : ℝ) (503061561611/1000000000000 : ℝ) (25153078081/50000000000 : ℝ) (125765390407/250000000000 : ℝ) (503061561637/1000000000000 : ℝ) (503061561627/1000000000000 : ℝ) (503061561637/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8561/65536 : ℝ))) 5 (125765390407/250000000000 : ℝ) (503061561637/1000000000000 : ℝ) (503061561627/1000000000000 : ℝ) (503061561637/1000000000000 : ℝ) (503061561627/1000000000000 : ℝ) (503061561637/1000000000000 : ℝ) (503061561627/1000000000000 : ℝ) (503061561637/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8561/65536 : ℝ))) 6 (503061561627/1000000000000 : ℝ) (503061561637/1000000000000 : ℝ) (503061561627/1000000000000 : ℝ) (503061561637/1000000000000 : ℝ) (503061561627/1000000000000 : ℝ) (503061561637/1000000000000 : ℝ) (503061561627/1000000000000 : ℝ) (503061561637/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8561/65536 : ℝ))) 7 (503061561627/1000000000000 : ℝ) (503061561637/1000000000000 : ℝ) (503061561627/1000000000000 : ℝ) (503061561637/1000000000000 : ℝ) (503061561627/1000000000000 : ℝ) (503061561637/1000000000000 : ℝ) (503061561627/1000000000000 : ℝ) (503061561637/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8561/65536 : ℝ)) hmem 8 (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ) (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8561/65536 : ℝ))) hcmem 8 (503061561627/1000000000000 : ℝ) (503061561637/1000000000000 : ℝ) (503061561627/1000000000000 : ℝ) (503061561637/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8561/65536 : ℝ)) (991885361321/1000000000000 : ℝ) (247971340331/250000000000 : ℝ) (503061561627/1000000000000 : ℝ) (503061561637/1000000000000 : ℝ) (796671958239/1000000000000 : ℝ) (796671958259/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1551_exp_lower
  have heNumeric : (1027460739243/500000000000 : ℝ)/4 ≤ Real.exp (-166514180971/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027460739243/500000000000 : ℝ)/4 ≤ Real.exp ((535/4096 : ℝ)-(796671958259/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (535/4096 : ℝ) (8561/65536 : ℝ) (796671958259/1000000000000 : ℝ) (1027460739243/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1552; no trusted numerical premise.
theorem cover8_leaf1552_exp_radius : (997960742242962941/1000000000000000000 : ℝ) ≤ Real.exp ((-4281/262144 : ℝ)/8) ∧ Real.exp ((-4281/262144 : ℝ)/8) ≤ (498980371121481471/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4281/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1552_exp_lower : (920114591284117923/1000000000000000000 : ℝ) ≤ Real.exp ((-10656903801839/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656903801839/16000000000000 : ℝ)/8) ≤ (230028647821029481/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656903801839/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1552_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513730491/250000000 : ℝ) ≤ 4*Real.exp (8561/65536 : ℝ)*Real.exp (-mu (radius 8 (4281/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513730491/250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4281/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1552_exp_radius
  have hrNumeric : (983801904271/1000000000000 : ℝ) ≤ Real.exp (-4281/262144 : ℝ) ∧ Real.exp (-4281/262144 : ℝ) ≤ (61487619017/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983801904271/1000000000000 : ℝ) ≤ (radius 8 (4281/32768 : ℝ)) ∧ (radius 8 (4281/32768 : ℝ)) ≤ (61487619017/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4281/32768 : ℝ)) (983801904271/1000000000000 : ℝ) (61487619017/62500000000 : ℝ) (700230731/3906250000 : ℝ) (179259067143/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4281/32768 : ℝ)) (983801904271/1000000000000 : ℝ) (61487619017/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4281/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983801904271/1000000000000 : ℝ) (61487619017/62500000000 : ℝ) (198380190427/200000000000 : ℝ) (123987619017/125000000000 : ℝ) (1983735773/2000000000 : ℝ) (495933943251/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4281/32768 : ℝ)) 1 (198380190427/200000000000 : ℝ) (123987619017/125000000000 : ℝ) (1983735773/2000000000 : ℝ) (495933943251/500000000000 : ℝ) (991884419317/1000000000000 : ℝ) (991884419319/1000000000000 : ℝ) (991884419179/1000000000000 : ℝ) (495942209591/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4281/32768 : ℝ)) 2 (991884419317/1000000000000 : ℝ) (991884419319/1000000000000 : ℝ) (991884419179/1000000000000 : ℝ) (495942209591/500000000000 : ℝ) (61992776203/62500000000 : ℝ) (991884419251/1000000000000 : ℝ) (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4281/32768 : ℝ)) 3 (61992776203/62500000000 : ℝ) (991884419251/1000000000000 : ℝ) (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ) (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ) (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4281/32768 : ℝ)) 4 (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ) (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ) (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ) (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4281/32768 : ℝ)) 5 (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ) (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ) (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ) (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4281/32768 : ℝ)) 6 (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ) (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ) (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ) (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4281/32768 : ℝ)) 7 (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ) (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ) (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ) (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4281/32768 : ℝ))) (700230731/3906250000 : ℝ) (179259067143/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4281/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (700230731/3906250000 : ℝ) (179259067143/1000000000000 : ℝ) (4606480731/7812500000 : ℝ) (147407383393/250000000000 : ℝ) (211694985259/500000000000 : ℝ) (13230936579/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4281/32768 : ℝ))) 1 (4606480731/7812500000 : ℝ) (147407383393/250000000000 : ℝ) (211694985259/500000000000 : ℝ) (13230936579/31250000000 : ℝ) (506509752043/1000000000000 : ℝ) (10130195041/20000000000 : ℝ) (249821551729/500000000000 : ℝ) (499643103467/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4281/32768 : ℝ))) 2 (506509752043/1000000000000 : ℝ) (10130195041/20000000000 : ℝ) (249821551729/500000000000 : ℝ) (499643103467/1000000000000 : ℝ) (2012305711/4000000000 : ℝ) (503076427759/1000000000000 : ℝ) (251532355991/500000000000 : ℝ) (503064711991/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4281/32768 : ℝ))) 3 (2012305711/4000000000 : ℝ) (503076427759/1000000000000 : ℝ) (251532355991/500000000000 : ℝ) (503064711991/1000000000000 : ℝ) (251535284933/500000000000 : ℝ) (4024564559/8000000000 : ℝ) (503070569831/1000000000000 : ℝ) (503070569841/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4281/32768 : ℝ))) 4 (251535284933/500000000000 : ℝ) (4024564559/8000000000 : ℝ) (503070569831/1000000000000 : ℝ) (503070569841/1000000000000 : ℝ) (62883821231/125000000000 : ℝ) (251535284929/500000000000 : ℝ) (62883821231/125000000000 : ℝ) (251535284929/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4281/32768 : ℝ))) 5 (62883821231/125000000000 : ℝ) (251535284929/500000000000 : ℝ) (62883821231/125000000000 : ℝ) (251535284929/500000000000 : ℝ) (62883821231/125000000000 : ℝ) (251535284929/500000000000 : ℝ) (62883821231/125000000000 : ℝ) (251535284929/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4281/32768 : ℝ))) 6 (62883821231/125000000000 : ℝ) (251535284929/500000000000 : ℝ) (62883821231/125000000000 : ℝ) (251535284929/500000000000 : ℝ) (62883821231/125000000000 : ℝ) (251535284929/500000000000 : ℝ) (62883821231/125000000000 : ℝ) (251535284929/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4281/32768 : ℝ))) 7 (62883821231/125000000000 : ℝ) (251535284929/500000000000 : ℝ) (62883821231/125000000000 : ℝ) (251535284929/500000000000 : ℝ) (62883821231/125000000000 : ℝ) (251535284929/500000000000 : ℝ) (62883821231/125000000000 : ℝ) (251535284929/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4281/32768 : ℝ)) hmem 8 (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ) (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4281/32768 : ℝ))) hcmem 8 (62883821231/125000000000 : ℝ) (251535284929/500000000000 : ℝ) (62883821231/125000000000 : ℝ) (251535284929/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4281/32768 : ℝ)) (991884419247/1000000000000 : ℝ) (991884419251/1000000000000 : ℝ) (62883821231/125000000000 : ℝ) (251535284929/500000000000 : ℝ) (796686980759/1000000000000 : ℝ) (796686980779/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1552_exp_lower
  have heNumeric : (513730491/250000000 : ℝ)/4 ≤ Real.exp (-10656903801839/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513730491/250000000 : ℝ)/4 ≤ Real.exp ((8561/65536 : ℝ)-(796686980779/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8561/65536 : ℝ) (4281/32768 : ℝ) (796686980779/1000000000000 : ℝ) (513730491/250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1553; no trusted numerical premise.
theorem cover8_leaf1553_exp_radius : (49898025215530457/50000000000000000 : ℝ) ≤ Real.exp ((-8563/524288 : ℝ)/8) ∧ Real.exp ((-8563/524288 : ℝ)/8) ≤ (997960504310609141/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8563/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1553_exp_lower : (920114618595311859/1000000000000000000 : ℝ) ≤ Real.exp ((-5328450001247/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328450001247/8000000000000 : ℝ)/8) ≤ (46005730929765593/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328450001247/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1553_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (51373061299/25000000000 : ℝ) ≤ 4*Real.exp (4281/32768 : ℝ)*Real.exp (-mu (radius 8 (8563/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (51373061299/25000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8563/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1553_exp_radius
  have hrNumeric : (49190001391/50000000000 : ℝ) ≤ Real.exp (-8563/524288 : ℝ) ∧ Real.exp (-8563/524288 : ℝ) ≤ (983800027821/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49190001391/50000000000 : ℝ) ≤ (radius 8 (8563/65536 : ℝ)) ∧ (radius 8 (8563/65536 : ℝ)) ≤ (983800027821/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8563/65536 : ℝ)) (49190001391/50000000000 : ℝ) (983800027821/1000000000000 : ℝ) (5602167659/31250000000 : ℝ) (35853873019/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8563/65536 : ℝ)) (49190001391/50000000000 : ℝ) (983800027821/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8563/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49190001391/50000000000 : ℝ) (983800027821/1000000000000 : ℝ) (99190001391/100000000000 : ℝ) (991900013911/1000000000000 : ℝ) (495933470291/500000000000 : ℝ) (991866940583/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8563/65536 : ℝ)) 1 (99190001391/100000000000 : ℝ) (991900013911/1000000000000 : ℝ) (495933470291/500000000000 : ℝ) (991866940583/1000000000000 : ℝ) (495941738623/500000000000 : ℝ) (991883477247/1000000000000 : ℝ) (247970869277/250000000000 : ℝ) (99188347711/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8563/65536 : ℝ)) 2 (495941738623/500000000000 : ℝ) (991883477247/1000000000000 : ℝ) (247970869277/250000000000 : ℝ) (99188347711/100000000000 : ℝ) (991883477177/1000000000000 : ℝ) (991883477179/1000000000000 : ℝ) (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8563/65536 : ℝ)) 3 (991883477177/1000000000000 : ℝ) (991883477179/1000000000000 : ℝ) (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ) (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ) (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8563/65536 : ℝ)) 4 (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ) (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ) (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ) (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8563/65536 : ℝ)) 5 (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ) (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ) (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ) (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8563/65536 : ℝ)) 6 (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ) (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ) (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ) (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8563/65536 : ℝ)) 7 (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ) (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ) (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ) (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8563/65536 : ℝ))) (5602167659/31250000000 : ℝ) (35853873019/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8563/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5602167659/31250000000 : ℝ) (35853873019/200000000000 : ℝ) (36852167659/62500000000 : ℝ) (147408670637/250000000000 : ℝ) (105850532913/250000000000 : ℝ) (423402131661/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8563/65536 : ℝ))) 1 (36852167659/62500000000 : ℝ) (147408670637/250000000000 : ℝ) (105850532913/250000000000 : ℝ) (423402131661/1000000000000 : ℝ) (253259203549/500000000000 : ℝ) (101303681421/200000000000 : ℝ) (499652460701/1000000000000 : ℝ) (499652460709/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8563/65536 : ℝ))) 2 (253259203549/500000000000 : ℝ) (101303681421/200000000000 : ℝ) (499652460701/1000000000000 : ℝ) (499652460709/1000000000000 : ℝ) (503085433899/1000000000000 : ℝ) (503085433907/1000000000000 : ℝ) (503073720737/1000000000000 : ℝ) (251536860373/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8563/65536 : ℝ))) 3 (503085433899/1000000000000 : ℝ) (503085433907/1000000000000 : ℝ) (503073720737/1000000000000 : ℝ) (251536860373/500000000000 : ℝ) (251539788659/500000000000 : ℝ) (503079577327/1000000000000 : ℝ) (503079577283/1000000000000 : ℝ) (503079577293/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8563/65536 : ℝ))) 4 (251539788659/500000000000 : ℝ) (503079577327/1000000000000 : ℝ) (503079577283/1000000000000 : ℝ) (503079577293/1000000000000 : ℝ) (5030795773/10000000000 : ℝ) (50307957731/100000000000 : ℝ) (5030795773/10000000000 : ℝ) (50307957731/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8563/65536 : ℝ))) 5 (5030795773/10000000000 : ℝ) (50307957731/100000000000 : ℝ) (5030795773/10000000000 : ℝ) (50307957731/100000000000 : ℝ) (5030795773/10000000000 : ℝ) (50307957731/100000000000 : ℝ) (5030795773/10000000000 : ℝ) (50307957731/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8563/65536 : ℝ))) 6 (5030795773/10000000000 : ℝ) (50307957731/100000000000 : ℝ) (5030795773/10000000000 : ℝ) (50307957731/100000000000 : ℝ) (5030795773/10000000000 : ℝ) (50307957731/100000000000 : ℝ) (5030795773/10000000000 : ℝ) (50307957731/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8563/65536 : ℝ))) 7 (5030795773/10000000000 : ℝ) (50307957731/100000000000 : ℝ) (5030795773/10000000000 : ℝ) (50307957731/100000000000 : ℝ) (5030795773/10000000000 : ℝ) (50307957731/100000000000 : ℝ) (5030795773/10000000000 : ℝ) (50307957731/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8563/65536 : ℝ)) hmem 8 (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ) (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8563/65536 : ℝ))) hcmem 8 (5030795773/10000000000 : ℝ) (50307957731/100000000000 : ℝ) (5030795773/10000000000 : ℝ) (50307957731/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8563/65536 : ℝ)) (123985434647/125000000000 : ℝ) (991883477179/1000000000000 : ℝ) (5030795773/10000000000 : ℝ) (50307957731/100000000000 : ℝ) (796702002089/1000000000000 : ℝ) (796702002109/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1553_exp_lower
  have heNumeric : (51373061299/25000000000 : ℝ)/4 ≤ Real.exp (-5328450001247/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (51373061299/25000000000 : ℝ)/4 ≤ Real.exp ((4281/32768 : ℝ)-(796702002109/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4281/32768 : ℝ) (8563/65536 : ℝ) (796702002109/1000000000000 : ℝ) (51373061299/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1554; no trusted numerical premise.
theorem cover8_leaf1554_exp_radius : (498980133189156033/500000000000000000 : ℝ) ≤ Real.exp ((-2141/131072 : ℝ)/8) ∧ Real.exp ((-2141/131072 : ℝ)/8) ≤ (997960266378312067/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2141/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1554_exp_lower : (920114646042913601/1000000000000000000 : ℝ) ≤ Real.exp ((-10656896184173/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656896184173/16000000000000 : ℝ)/8) ≤ (460057323021456801/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656896184173/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1554_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054922942357/1000000000000 : ℝ) ≤ 4*Real.exp (8563/65536 : ℝ)*Real.exp (-mu (radius 8 (2141/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054922942357/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2141/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1554_exp_radius
  have hrNumeric : (245949537843/250000000000 : ℝ) ≤ Real.exp (-2141/131072 : ℝ) ∧ Real.exp (-2141/131072 : ℝ) ≤ (983798151373/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245949537843/250000000000 : ℝ) ≤ (radius 8 (2141/16384 : ℝ)) ∧ (radius 8 (2141/16384 : ℝ)) ≤ (983798151373/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2141/16384 : ℝ)) (245949537843/250000000000 : ℝ) (983798151373/1000000000000 : ℝ) (179279662413/1000000000000 : ℝ) (179279662419/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2141/16384 : ℝ)) (245949537843/250000000000 : ℝ) (983798151373/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2141/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245949537843/250000000000 : ℝ) (983798151373/1000000000000 : ℝ) (495949537843/500000000000 : ℝ) (991899075687/1000000000000 : ℝ) (123983249333/125000000000 : ℝ) (495932997333/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2141/16384 : ℝ)) 1 (495949537843/500000000000 : ℝ) (991899075687/1000000000000 : ℝ) (123983249333/125000000000 : ℝ) (495932997333/500000000000 : ℝ) (39675301407/40000000000 : ℝ) (991882535177/1000000000000 : ℝ) (991882535037/1000000000000 : ℝ) (991882535039/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2141/16384 : ℝ)) 2 (39675301407/40000000000 : ℝ) (991882535177/1000000000000 : ℝ) (991882535037/1000000000000 : ℝ) (991882535039/1000000000000 : ℝ) (495941267553/500000000000 : ℝ) (247970633777/250000000000 : ℝ) (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2141/16384 : ℝ)) 3 (495941267553/500000000000 : ℝ) (247970633777/250000000000 : ℝ) (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ) (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ) (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2141/16384 : ℝ)) 4 (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ) (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ) (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ) (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2141/16384 : ℝ)) 5 (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ) (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ) (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ) (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2141/16384 : ℝ)) 6 (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ) (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ) (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ) (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2141/16384 : ℝ)) 7 (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ) (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ) (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ) (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2141/16384 : ℝ))) (179279662413/1000000000000 : ℝ) (179279662419/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2141/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179279662413/1000000000000 : ℝ) (179279662419/1000000000000 : ℝ) (294819915603/500000000000 : ℝ) (58963983121/100000000000 : ℝ) (26463393231/62500000000 : ℝ) (52926786463/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2141/16384 : ℝ))) 1 (294819915603/500000000000 : ℝ) (58963983121/100000000000 : ℝ) (26463393231/62500000000 : ℝ) (52926786463/125000000000 : ℝ) (506527061451/1000000000000 : ℝ) (506527061457/1000000000000 : ℝ) (249830908559/500000000000 : ℝ) (3997294537/8000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2141/16384 : ℝ))) 2 (506527061451/1000000000000 : ℝ) (506527061457/1000000000000 : ℝ) (249830908559/500000000000 : ℝ) (3997294537/8000000000 : ℝ) (125773609821/250000000000 : ℝ) (503094439291/1000000000000 : ℝ) (503082728727/1000000000000 : ℝ) (100616545747/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2141/16384 : ℝ))) 3 (125773609821/250000000000 : ℝ) (503094439291/1000000000000 : ℝ) (503082728727/1000000000000 : ℝ) (100616545747/200000000000 : ℝ) (100617716801/200000000000 : ℝ) (503088584013/1000000000000 : ℝ) (503088583971/1000000000000 : ℝ) (503088583979/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2141/16384 : ℝ))) 4 (100617716801/200000000000 : ℝ) (503088584013/1000000000000 : ℝ) (503088583971/1000000000000 : ℝ) (503088583979/1000000000000 : ℝ) (125772145997/250000000000 : ℝ) (125772145999/250000000000 : ℝ) (503088583987/1000000000000 : ℝ) (125772145999/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2141/16384 : ℝ))) 5 (125772145997/250000000000 : ℝ) (125772145999/250000000000 : ℝ) (503088583987/1000000000000 : ℝ) (125772145999/250000000000 : ℝ) (503088583987/1000000000000 : ℝ) (125772145999/250000000000 : ℝ) (503088583987/1000000000000 : ℝ) (125772145999/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2141/16384 : ℝ))) 6 (503088583987/1000000000000 : ℝ) (125772145999/250000000000 : ℝ) (503088583987/1000000000000 : ℝ) (125772145999/250000000000 : ℝ) (503088583987/1000000000000 : ℝ) (125772145999/250000000000 : ℝ) (503088583987/1000000000000 : ℝ) (125772145999/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2141/16384 : ℝ))) 7 (503088583987/1000000000000 : ℝ) (125772145999/250000000000 : ℝ) (503088583987/1000000000000 : ℝ) (125772145999/250000000000 : ℝ) (503088583987/1000000000000 : ℝ) (125772145999/250000000000 : ℝ) (503088583987/1000000000000 : ℝ) (125772145999/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2141/16384 : ℝ)) hmem 8 (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ) (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2141/16384 : ℝ))) hcmem 8 (503088583987/1000000000000 : ℝ) (125772145999/250000000000 : ℝ) (503088583987/1000000000000 : ℝ) (125772145999/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2141/16384 : ℝ)) (198376507021/200000000000 : ℝ) (247970633777/250000000000 : ℝ) (503088583987/1000000000000 : ℝ) (125772145999/250000000000 : ℝ) (199179255559/250000000000 : ℝ) (796717022253/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1554_exp_lower
  have heNumeric : (2054922942357/1000000000000 : ℝ)/4 ≤ Real.exp (-10656896184173/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054922942357/1000000000000 : ℝ)/4 ≤ Real.exp ((8563/65536 : ℝ)-(796717022253/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8563/65536 : ℝ) (2141/16384 : ℝ) (796717022253/1000000000000 : ℝ) (2054922942357/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1555; no trusted numerical premise.
theorem cover8_leaf1555_exp_radius : (24949000711151793/25000000000000000 : ℝ) ≤ Real.exp ((-8565/524288 : ℝ)/8) ∧ Real.exp ((-8565/524288 : ℝ)/8) ≤ (997960028446071721/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8565/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1555_exp_lower : (230028668406558269/250000000000000000 : ℝ) ≤ Real.exp ((-2664223086743/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664223086743/4000000000000 : ℝ)/8) ≤ (920114673626233077/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664223086743/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1555_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054923435179/1000000000000 : ℝ) ≤ 4*Real.exp (2141/16384 : ℝ)*Real.exp (-mu (radius 8 (8565/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054923435179/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8565/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1555_exp_radius
  have hrNumeric : (983796274927/1000000000000 : ℝ) ≤ Real.exp (-8565/524288 : ℝ) ∧ Real.exp (-8565/524288 : ℝ) ≤ (61487267183/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983796274927/1000000000000 : ℝ) ≤ (radius 8 (8565/65536 : ℝ)) ∧ (radius 8 (8565/65536 : ℝ)) ≤ (61487267183/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8565/65536 : ℝ)) (983796274927/1000000000000 : ℝ) (61487267183/62500000000 : ℝ) (17928995911/100000000000 : ℝ) (44822489779/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8565/65536 : ℝ)) (983796274927/1000000000000 : ℝ) (61487267183/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8565/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983796274927/1000000000000 : ℝ) (61487267183/62500000000 : ℝ) (991898137463/1000000000000 : ℝ) (123987267183/125000000000 : ℝ) (991865048747/1000000000000 : ℝ) (991865048749/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8565/65536 : ℝ)) 1 (991898137463/1000000000000 : ℝ) (123987267183/125000000000 : ℝ) (991865048747/1000000000000 : ℝ) (991865048749/1000000000000 : ℝ) (198376318621/200000000000 : ℝ) (991881593107/1000000000000 : ℝ) (991881592967/1000000000000 : ℝ) (991881592969/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8565/65536 : ℝ)) 2 (198376318621/200000000000 : ℝ) (991881593107/1000000000000 : ℝ) (991881592967/1000000000000 : ℝ) (991881592969/1000000000000 : ℝ) (247970398259/250000000000 : ℝ) (495940796519/500000000000 : ℝ) (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8565/65536 : ℝ)) 3 (247970398259/250000000000 : ℝ) (495940796519/500000000000 : ℝ) (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ) (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ) (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8565/65536 : ℝ)) 4 (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ) (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ) (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ) (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8565/65536 : ℝ)) 5 (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ) (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ) (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ) (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8565/65536 : ℝ)) 6 (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ) (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ) (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ) (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8565/65536 : ℝ)) 7 (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ) (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ) (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ) (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8565/65536 : ℝ))) (17928995911/100000000000 : ℝ) (44822489779/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8565/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17928995911/100000000000 : ℝ) (44822489779/250000000000 : ℝ) (117928995911/200000000000 : ℝ) (294822489779/500000000000 : ℝ) (423426450649/1000000000000 : ℝ) (211713225329/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8565/65536 : ℝ))) 1 (117928995911/200000000000 : ℝ) (294822489779/500000000000 : ℝ) (423426450649/1000000000000 : ℝ) (211713225329/500000000000 : ℝ) (253267857551/500000000000 : ℝ) (126633928777/250000000000 : ℝ) (124917793177/250000000000 : ℝ) (124917793179/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8565/65536 : ℝ))) 2 (253267857551/500000000000 : ℝ) (126633928777/250000000000 : ℝ) (124917793177/250000000000 : ℝ) (124917793179/250000000000 : ℝ) (100620688781/200000000000 : ℝ) (62887930489/125000000000 : ℝ) (31443233497/62500000000 : ℝ) (12577293399/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8565/65536 : ℝ))) 3 (100620688781/200000000000 : ℝ) (62887930489/125000000000 : ℝ) (31443233497/62500000000 : ℝ) (12577293399/25000000000 : ℝ) (62887198741/125000000000 : ℝ) (31443599371/62500000000 : ℝ) (251548794947/500000000000 : ℝ) (251548794951/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8565/65536 : ℝ))) 4 (62887198741/125000000000 : ℝ) (31443599371/62500000000 : ℝ) (251548794947/500000000000 : ℝ) (251548794951/500000000000 : ℝ) (503097589911/1000000000000 : ℝ) (503097589919/1000000000000 : ℝ) (50309758991/100000000000 : ℝ) (503097589919/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8565/65536 : ℝ))) 5 (503097589911/1000000000000 : ℝ) (503097589919/1000000000000 : ℝ) (50309758991/100000000000 : ℝ) (503097589919/1000000000000 : ℝ) (50309758991/100000000000 : ℝ) (503097589919/1000000000000 : ℝ) (50309758991/100000000000 : ℝ) (503097589919/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8565/65536 : ℝ))) 6 (50309758991/100000000000 : ℝ) (503097589919/1000000000000 : ℝ) (50309758991/100000000000 : ℝ) (503097589919/1000000000000 : ℝ) (50309758991/100000000000 : ℝ) (503097589919/1000000000000 : ℝ) (50309758991/100000000000 : ℝ) (503097589919/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8565/65536 : ℝ))) 7 (50309758991/100000000000 : ℝ) (503097589919/1000000000000 : ℝ) (50309758991/100000000000 : ℝ) (503097589919/1000000000000 : ℝ) (50309758991/100000000000 : ℝ) (503097589919/1000000000000 : ℝ) (50309758991/100000000000 : ℝ) (503097589919/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8565/65536 : ℝ)) hmem 8 (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ) (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8565/65536 : ℝ))) hcmem 8 (50309758991/100000000000 : ℝ) (503097589919/1000000000000 : ℝ) (50309758991/100000000000 : ℝ) (503097589919/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8565/65536 : ℝ)) (198376318607/200000000000 : ℝ) (495940796519/500000000000 : ℝ) (50309758991/100000000000 : ℝ) (503097589919/1000000000000 : ℝ) (1991830103/2500000000 : ℝ) (796732041217/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1555_exp_lower
  have heNumeric : (2054923435179/1000000000000 : ℝ)/4 ≤ Real.exp (-2664223086743/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054923435179/1000000000000 : ℝ)/4 ≤ Real.exp ((2141/16384 : ℝ)-(796732041217/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2141/16384 : ℝ) (8565/65536 : ℝ) (796732041217/1000000000000 : ℝ) (2054923435179/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1556; no trusted numerical premise.
theorem cover8_leaf1556_exp_radius : (498979895256944051/500000000000000000 : ℝ) ≤ Real.exp ((-4283/262144 : ℝ)/8) ∧ Real.exp ((-4283/262144 : ℝ)/8) ≤ (997959790513888103/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4283/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1556_exp_lower : (920114701347455569/1000000000000000000 : ℝ) ≤ Real.exp ((-10656888490587/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656888490587/16000000000000 : ℝ)/8) ≤ (92011470134745557/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656888490587/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1556_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027461965233/500000000000 : ℝ) ≤ 4*Real.exp (8565/65536 : ℝ)*Real.exp (-mu (radius 8 (4283/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027461965233/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4283/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1556_exp_radius
  have hrNumeric : (983794398487/1000000000000 : ℝ) ≤ Real.exp (-4283/262144 : ℝ) ∧ Real.exp (-4283/262144 : ℝ) ≤ (122974299811/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983794398487/1000000000000 : ℝ) ≤ (radius 8 (4283/32768 : ℝ)) ∧ (radius 8 (4283/32768 : ℝ)) ≤ (122974299811/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4283/32768 : ℝ)) (983794398487/1000000000000 : ℝ) (122974299811/125000000000 : ℝ) (2801566487/15625000000 : ℝ) (7172010207/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4283/32768 : ℝ)) (983794398487/1000000000000 : ℝ) (122974299811/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4283/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983794398487/1000000000000 : ℝ) (122974299811/125000000000 : ℝ) (991897199243/1000000000000 : ℝ) (247974299811/250000000000 : ℝ) (61991506427/62500000000 : ℝ) (991864102833/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4283/32768 : ℝ)) 1 (991897199243/1000000000000 : ℝ) (247974299811/250000000000 : ℝ) (61991506427/62500000000 : ℝ) (991864102833/1000000000000 : ℝ) (991880651037/1000000000000 : ℝ) (991880651039/1000000000000 : ℝ) (991880650899/1000000000000 : ℝ) (991880650901/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4283/32768 : ℝ)) 2 (991880651037/1000000000000 : ℝ) (991880651039/1000000000000 : ℝ) (991880650899/1000000000000 : ℝ) (991880650901/1000000000000 : ℝ) (123985081371/125000000000 : ℝ) (99188065097/100000000000 : ℝ) (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4283/32768 : ℝ)) 3 (123985081371/125000000000 : ℝ) (99188065097/100000000000 : ℝ) (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ) (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ) (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4283/32768 : ℝ)) 4 (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ) (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ) (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ) (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4283/32768 : ℝ)) 5 (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ) (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ) (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ) (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4283/32768 : ℝ)) 6 (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ) (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ) (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ) (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4283/32768 : ℝ)) 7 (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ) (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ) (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ) (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4283/32768 : ℝ))) (2801566487/15625000000 : ℝ) (7172010207/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4283/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2801566487/15625000000 : ℝ) (7172010207/40000000000 : ℝ) (18426566487/31250000000 : ℝ) (147412531897/250000000000 : ℝ) (423438608499/1000000000000 : ℝ) (105859652127/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4283/32768 : ℝ))) 1 (18426566487/31250000000 : ℝ) (147412531897/250000000000 : ℝ) (423438608499/1000000000000 : ℝ) (105859652127/250000000000 : ℝ) (506544368041/1000000000000 : ℝ) (31659023003/62500000000 : ℝ) (249840263731/500000000000 : ℝ) (49968052747/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4283/32768 : ℝ))) 2 (506544368041/1000000000000 : ℝ) (31659023003/62500000000 : ℝ) (249840263731/500000000000 : ℝ) (49968052747/100000000000 : ℝ) (503112447751/1000000000000 : ℝ) (503112447759/1000000000000 : ℝ) (251550371201/500000000000 : ℝ) (50310074241/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4283/32768 : ℝ))) 3 (503112447751/1000000000000 : ℝ) (503112447759/1000000000000 : ℝ) (251550371201/500000000000 : ℝ) (50310074241/100000000000 : ℝ) (125776648769/250000000000 : ℝ) (100621319017/200000000000 : ℝ) (251553297521/500000000000 : ℝ) (503106595051/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4283/32768 : ℝ))) 4 (125776648769/250000000000 : ℝ) (100621319017/200000000000 : ℝ) (251553297521/500000000000 : ℝ) (503106595051/1000000000000 : ℝ) (503106595059/1000000000000 : ℝ) (125776648767/250000000000 : ℝ) (251553297529/500000000000 : ℝ) (125776648767/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4283/32768 : ℝ))) 5 (503106595059/1000000000000 : ℝ) (125776648767/250000000000 : ℝ) (251553297529/500000000000 : ℝ) (125776648767/250000000000 : ℝ) (251553297529/500000000000 : ℝ) (125776648767/250000000000 : ℝ) (251553297529/500000000000 : ℝ) (125776648767/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4283/32768 : ℝ))) 6 (251553297529/500000000000 : ℝ) (125776648767/250000000000 : ℝ) (251553297529/500000000000 : ℝ) (125776648767/250000000000 : ℝ) (251553297529/500000000000 : ℝ) (125776648767/250000000000 : ℝ) (251553297529/500000000000 : ℝ) (125776648767/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4283/32768 : ℝ))) 7 (251553297529/500000000000 : ℝ) (125776648767/250000000000 : ℝ) (251553297529/500000000000 : ℝ) (125776648767/250000000000 : ℝ) (251553297529/500000000000 : ℝ) (125776648767/250000000000 : ℝ) (251553297529/500000000000 : ℝ) (125776648767/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4283/32768 : ℝ)) hmem 8 (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ) (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4283/32768 : ℝ))) hcmem 8 (251553297529/500000000000 : ℝ) (125776648767/250000000000 : ℝ) (251553297529/500000000000 : ℝ) (125776648767/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4283/32768 : ℝ)) (991880650967/1000000000000 : ℝ) (99188065097/100000000000 : ℝ) (251553297529/500000000000 : ℝ) (125776648767/250000000000 : ℝ) (796747058963/1000000000000 : ℝ) (398373529491/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1556_exp_lower
  have heNumeric : (1027461965233/500000000000 : ℝ)/4 ≤ Real.exp (-10656888490587/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027461965233/500000000000 : ℝ)/4 ≤ Real.exp ((8565/65536 : ℝ)-(398373529491/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8565/65536 : ℝ) (4283/32768 : ℝ) (398373529491/500000000000 : ℝ) (1027461965233/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1557; no trusted numerical premise.
theorem cover8_leaf1557_exp_radius : (997959552581761211/1000000000000000000 : ℝ) ≤ Real.exp ((-8567/524288 : ℝ)/8) ∧ Real.exp ((-8567/524288 : ℝ)/8) ≤ (249489888145440303/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8567/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1557_exp_lower : (920114729204855877/1000000000000000000 : ℝ) ≤ Real.exp ((-5328442307629/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328442307629/8000000000000 : ℝ)/8) ≤ (460057364602427939/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328442307629/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1557_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410984885637/200000000000 : ℝ) ≤ 4*Real.exp (4283/32768 : ℝ)*Real.exp (-mu (radius 8 (8567/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (410984885637/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8567/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1557_exp_radius
  have hrNumeric : (19675850441/20000000000 : ℝ) ≤ Real.exp (-8567/524288 : ℝ) ∧ Real.exp (-8567/524288 : ℝ) ≤ (983792522051/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (19675850441/20000000000 : ℝ) ≤ (radius 8 (8567/65536 : ℝ)) ∧ (radius 8 (8567/65536 : ℝ)) ≤ (983792522051/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8567/65536 : ℝ)) (19675850441/20000000000 : ℝ) (983792522051/1000000000000 : ℝ) (896552753/5000000000 : ℝ) (89655275303/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8567/65536 : ℝ)) (19675850441/20000000000 : ℝ) (983792522051/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8567/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (19675850441/20000000000 : ℝ) (983792522051/1000000000000 : ℝ) (39675850441/40000000000 : ℝ) (495948130513/500000000000 : ℝ) (991863156917/1000000000000 : ℝ) (495931578459/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8567/65536 : ℝ)) 1 (39675850441/40000000000 : ℝ) (495948130513/500000000000 : ℝ) (991863156917/1000000000000 : ℝ) (495931578459/500000000000 : ℝ) (991879708971/1000000000000 : ℝ) (247969927243/250000000000 : ℝ) (30996240901/31250000000 : ℝ) (495939854417/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8567/65536 : ℝ)) 2 (991879708971/1000000000000 : ℝ) (247969927243/250000000000 : ℝ) (30996240901/31250000000 : ℝ) (495939854417/500000000000 : ℝ) (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ) (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8567/65536 : ℝ)) 3 (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ) (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ) (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ) (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8567/65536 : ℝ)) 4 (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ) (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ) (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ) (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8567/65536 : ℝ)) 5 (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ) (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ) (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ) (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8567/65536 : ℝ)) 6 (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ) (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ) (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ) (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8567/65536 : ℝ)) 7 (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ) (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ) (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ) (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8567/65536 : ℝ))) (896552753/5000000000 : ℝ) (89655275303/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8567/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (896552753/5000000000 : ℝ) (89655275303/500000000000 : ℝ) (5896552753/10000000000 : ℝ) (589655275303/1000000000000 : ℝ) (21172538263/50000000000 : ℝ) (105862691317/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8567/65536 : ℝ))) 1 (5896552753/10000000000 : ℝ) (589655275303/1000000000000 : ℝ) (21172538263/50000000000 : ℝ) (105862691317/250000000000 : ℝ) (12663825507/25000000000 : ℝ) (253276510143/500000000000 : ℝ) (499689881391/1000000000000 : ℝ) (249844940699/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8567/65536 : ℝ))) 2 (12663825507/25000000000 : ℝ) (253276510143/500000000000 : ℝ) (499689881391/1000000000000 : ℝ) (249844940699/500000000000 : ℝ) (100624290167/200000000000 : ℝ) (251560725421/500000000000 : ℝ) (62888718511/125000000000 : ℝ) (3930544907/7812500000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8567/65536 : ℝ))) 3 (100624290167/200000000000 : ℝ) (251560725421/500000000000 : ℝ) (62888718511/125000000000 : ℝ) (3930544907/7812500000 : ℝ) (503115599461/1000000000000 : ℝ) (503115599469/1000000000000 : ℝ) (503115599427/1000000000000 : ℝ) (100623119887/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8567/65536 : ℝ))) 4 (503115599461/1000000000000 : ℝ) (503115599469/1000000000000 : ℝ) (503115599427/1000000000000 : ℝ) (100623119887/200000000000 : ℝ) (125778899861/250000000000 : ℝ) (125778899863/250000000000 : ℝ) (503115599443/1000000000000 : ℝ) (125778899863/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8567/65536 : ℝ))) 5 (125778899861/250000000000 : ℝ) (125778899863/250000000000 : ℝ) (503115599443/1000000000000 : ℝ) (125778899863/250000000000 : ℝ) (503115599443/1000000000000 : ℝ) (125778899863/250000000000 : ℝ) (503115599443/1000000000000 : ℝ) (125778899863/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8567/65536 : ℝ))) 6 (503115599443/1000000000000 : ℝ) (125778899863/250000000000 : ℝ) (503115599443/1000000000000 : ℝ) (125778899863/250000000000 : ℝ) (503115599443/1000000000000 : ℝ) (125778899863/250000000000 : ℝ) (503115599443/1000000000000 : ℝ) (125778899863/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8567/65536 : ℝ))) 7 (503115599443/1000000000000 : ℝ) (125778899863/250000000000 : ℝ) (503115599443/1000000000000 : ℝ) (125778899863/250000000000 : ℝ) (503115599443/1000000000000 : ℝ) (125778899863/250000000000 : ℝ) (503115599443/1000000000000 : ℝ) (125778899863/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8567/65536 : ℝ)) hmem 8 (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ) (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8567/65536 : ℝ))) hcmem 8 (503115599443/1000000000000 : ℝ) (125778899863/250000000000 : ℝ) (503115599443/1000000000000 : ℝ) (125778899863/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8567/65536 : ℝ)) (991879708901/1000000000000 : ℝ) (991879708903/1000000000000 : ℝ) (503115599443/1000000000000 : ℝ) (125778899863/250000000000 : ℝ) (398381037773/500000000000 : ℝ) (796762075563/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1557_exp_lower
  have heNumeric : (410984885637/200000000000 : ℝ)/4 ≤ Real.exp (-5328442307629/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410984885637/200000000000 : ℝ)/4 ≤ Real.exp ((4283/32768 : ℝ)-(796762075563/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4283/32768 : ℝ) (8567/65536 : ℝ) (796762075563/1000000000000 : ℝ) (410984885637/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1558; no trusted numerical premise.
theorem cover8_leaf1558_exp_radius : (997959314649691047/1000000000000000000 : ℝ) ≤ Real.exp ((-1071/65536 : ℝ)/8) ∧ Real.exp ((-1071/65536 : ℝ)/8) ≤ (124744914331211381/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1071/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1558_exp_lower : (184022951439594791/200000000000000000 : ℝ) ≤ Real.exp ((-10656880721049/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656880721049/16000000000000 : ℝ)/8) ≤ (230028689299493489/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656880721049/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1558_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054924928329/1000000000000 : ℝ) ≤ 4*Real.exp (8567/65536 : ℝ)*Real.exp (-mu (radius 8 (1071/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2054924928329/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1071/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1558_exp_radius
  have hrNumeric : (61486915351/62500000000 : ℝ) ≤ Real.exp (-1071/65536 : ℝ) ∧ Real.exp (-1071/65536 : ℝ) ≤ (983790645617/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61486915351/62500000000 : ℝ) ≤ (radius 8 (1071/8192 : ℝ)) ∧ (radius 8 (1071/8192 : ℝ)) ≤ (983790645617/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1071/8192 : ℝ)) (61486915351/62500000000 : ℝ) (983790645617/1000000000000 : ℝ) (44830211351/250000000000 : ℝ) (17932084541/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1071/8192 : ℝ)) (61486915351/62500000000 : ℝ) (983790645617/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1071/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61486915351/62500000000 : ℝ) (983790645617/1000000000000 : ℝ) (123986915351/125000000000 : ℝ) (991895322809/1000000000000 : ℝ) (991862211003/1000000000000 : ℝ) (247965552751/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1071/8192 : ℝ)) 1 (123986915351/125000000000 : ℝ) (991895322809/1000000000000 : ℝ) (991862211003/1000000000000 : ℝ) (247965552751/250000000000 : ℝ) (198375753381/200000000000 : ℝ) (991878766907/1000000000000 : ℝ) (991878766767/1000000000000 : ℝ) (991878766769/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1071/8192 : ℝ)) 2 (198375753381/200000000000 : ℝ) (991878766907/1000000000000 : ℝ) (991878766767/1000000000000 : ℝ) (991878766769/1000000000000 : ℝ) (247969691709/250000000000 : ℝ) (495939383419/500000000000 : ℝ) (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1071/8192 : ℝ)) 3 (247969691709/250000000000 : ℝ) (495939383419/500000000000 : ℝ) (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ) (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ) (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1071/8192 : ℝ)) 4 (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ) (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ) (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ) (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1071/8192 : ℝ)) 5 (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ) (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ) (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ) (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1071/8192 : ℝ)) 6 (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ) (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ) (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ) (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1071/8192 : ℝ)) 7 (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ) (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ) (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ) (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1071/8192 : ℝ))) (44830211351/250000000000 : ℝ) (17932084541/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1071/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44830211351/250000000000 : ℝ) (17932084541/100000000000 : ℝ) (294830211351/500000000000 : ℝ) (117932084541/200000000000 : ℝ) (423462920931/1000000000000 : ℝ) (423462920939/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1071/8192 : ℝ))) 1 (294830211351/500000000000 : ℝ) (117932084541/200000000000 : ℝ) (423462920931/1000000000000 : ℝ) (423462920939/1000000000000 : ℝ) (63320208977/125000000000 : ℝ) (253280835911/500000000000 : ℝ) (249849617247/500000000000 : ℝ) (499699234501/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1071/8192 : ℝ))) 2 (63320208977/125000000000 : ℝ) (253280835911/500000000000 : ℝ) (249849617247/500000000000 : ℝ) (499699234501/1000000000000 : ℝ) (100626090631/200000000000 : ℝ) (251565226581/500000000000 : ℝ) (50311875301/100000000000 : ℝ) (503118753017/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1071/8192 : ℝ))) 3 (100626090631/200000000000 : ℝ) (251565226581/500000000000 : ℝ) (50311875301/100000000000 : ℝ) (503118753017/1000000000000 : ℝ) (251562301541/500000000000 : ℝ) (50312460309/100000000000 : ℝ) (62890575381/125000000000 : ℝ) (31445287691/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1071/8192 : ℝ))) 4 (251562301541/500000000000 : ℝ) (50312460309/100000000000 : ℝ) (62890575381/125000000000 : ℝ) (31445287691/62500000000 : ℝ) (100624920613/200000000000 : ℝ) (503124603073/1000000000000 : ℝ) (62890575383/125000000000 : ℝ) (503124603073/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1071/8192 : ℝ))) 5 (100624920613/200000000000 : ℝ) (503124603073/1000000000000 : ℝ) (62890575383/125000000000 : ℝ) (503124603073/1000000000000 : ℝ) (62890575383/125000000000 : ℝ) (503124603073/1000000000000 : ℝ) (62890575383/125000000000 : ℝ) (503124603073/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1071/8192 : ℝ))) 6 (62890575383/125000000000 : ℝ) (503124603073/1000000000000 : ℝ) (62890575383/125000000000 : ℝ) (503124603073/1000000000000 : ℝ) (62890575383/125000000000 : ℝ) (503124603073/1000000000000 : ℝ) (62890575383/125000000000 : ℝ) (503124603073/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1071/8192 : ℝ))) 7 (62890575383/125000000000 : ℝ) (503124603073/1000000000000 : ℝ) (62890575383/125000000000 : ℝ) (503124603073/1000000000000 : ℝ) (62890575383/125000000000 : ℝ) (503124603073/1000000000000 : ℝ) (62890575383/125000000000 : ℝ) (503124603073/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1071/8192 : ℝ)) hmem 8 (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ) (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1071/8192 : ℝ))) hcmem 8 (62890575383/125000000000 : ℝ) (503124603073/1000000000000 : ℝ) (62890575383/125000000000 : ℝ) (503124603073/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1071/8192 : ℝ)) (198375753367/200000000000 : ℝ) (495939383419/500000000000 : ℝ) (62890575383/125000000000 : ℝ) (503124603073/1000000000000 : ℝ) (398388545473/500000000000 : ℝ) (199194272741/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1558_exp_lower
  have heNumeric : (2054924928329/1000000000000 : ℝ)/4 ≤ Real.exp (-10656880721049/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054924928329/1000000000000 : ℝ)/4 ≤ Real.exp ((8567/65536 : ℝ)-(199194272741/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8567/65536 : ℝ) (1071/8192 : ℝ) (199194272741/250000000000 : ℝ) (2054924928329/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1559; no trusted numerical premise.
theorem cover8_leaf1559_exp_radius : (997959076717677611/1000000000000000000 : ℝ) ≤ Real.exp ((-8569/524288 : ℝ)/8) ∧ Real.exp ((-8569/524288 : ℝ)/8) ≤ (249489769179419403/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8569/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1559_exp_lower : (920114785327959959/1000000000000000000 : ℝ) ≤ Real.exp ((-53284384039/80000000000 : ℝ)/8) ∧ Real.exp ((-53284384039/80000000000 : ℝ)/8) ≤ (23002869633198999/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-53284384039/80000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1559_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027462715459/500000000000 : ℝ) ≤ 4*Real.exp (1071/8192 : ℝ)*Real.exp (-mu (radius 8 (8569/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027462715459/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8569/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1559_exp_radius
  have hrNumeric : (491894384593/500000000000 : ℝ) ≤ Real.exp (-8569/524288 : ℝ) ∧ Real.exp (-8569/524288 : ℝ) ≤ (983788769187/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491894384593/500000000000 : ℝ) ≤ (radius 8 (8569/65536 : ℝ)) ∧ (radius 8 (8569/65536 : ℝ)) ≤ (983788769187/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8569/65536 : ℝ)) (491894384593/500000000000 : ℝ) (983788769187/1000000000000 : ℝ) (7173245583/40000000000 : ℝ) (89665569791/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8569/65536 : ℝ)) (491894384593/500000000000 : ℝ) (983788769187/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8569/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491894384593/500000000000 : ℝ) (983788769187/1000000000000 : ℝ) (991894384593/1000000000000 : ℝ) (495947192297/500000000000 : ℝ) (99186126509/100000000000 : ℝ) (991861265091/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8569/65536 : ℝ)) 1 (991894384593/1000000000000 : ℝ) (495947192297/500000000000 : ℝ) (99186126509/100000000000 : ℝ) (991861265091/1000000000000 : ℝ) (991877824841/1000000000000 : ℝ) (991877824843/1000000000000 : ℝ) (991877824703/1000000000000 : ℝ) (198375564941/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8569/65536 : ℝ)) 2 (991877824841/1000000000000 : ℝ) (991877824843/1000000000000 : ℝ) (991877824703/1000000000000 : ℝ) (198375564941/200000000000 : ℝ) (247969456193/250000000000 : ℝ) (495938912387/500000000000 : ℝ) (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8569/65536 : ℝ)) 3 (247969456193/250000000000 : ℝ) (495938912387/500000000000 : ℝ) (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ) (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ) (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8569/65536 : ℝ)) 4 (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ) (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ) (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ) (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8569/65536 : ℝ)) 5 (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ) (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ) (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ) (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8569/65536 : ℝ)) 6 (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ) (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ) (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ) (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8569/65536 : ℝ)) 7 (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ) (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ) (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ) (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8569/65536 : ℝ))) (7173245583/40000000000 : ℝ) (89665569791/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8569/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7173245583/40000000000 : ℝ) (89665569791/500000000000 : ℝ) (589665569787/1000000000000 : ℝ) (589665569791/1000000000000 : ℝ) (211737537753/500000000000 : ℝ) (84695015103/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8569/65536 : ℝ))) 1 (589665569787/1000000000000 : ℝ) (589665569791/1000000000000 : ℝ) (211737537753/500000000000 : ℝ) (84695015103/200000000000 : ℝ) (253285161323/500000000000 : ℝ) (506570322653/1000000000000 : ℝ) (499708586767/1000000000000 : ℝ) (19988343471/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8569/65536 : ℝ))) 2 (253285161323/500000000000 : ℝ) (506570322653/1000000000000 : ℝ) (499708586767/1000000000000 : ℝ) (19988343471/40000000000 : ℝ) (251569727353/500000000000 : ℝ) (251569727357/500000000000 : ℝ) (251563878581/500000000000 : ℝ) (503127757171/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8569/65536 : ℝ))) 3 (251569727353/500000000000 : ℝ) (251569727357/500000000000 : ℝ) (251563878581/500000000000 : ℝ) (503127757171/1000000000000 : ℝ) (251566802967/500000000000 : ℝ) (503133605943/1000000000000 : ℝ) (5031336059/10000000000 : ℝ) (503133605909/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8569/65536 : ℝ))) 4 (251566802967/500000000000 : ℝ) (503133605943/1000000000000 : ℝ) (5031336059/10000000000 : ℝ) (503133605909/1000000000000 : ℝ) (503133605917/1000000000000 : ℝ) (251566802963/500000000000 : ℝ) (125783401479/250000000000 : ℝ) (251566802963/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8569/65536 : ℝ))) 5 (503133605917/1000000000000 : ℝ) (251566802963/500000000000 : ℝ) (125783401479/250000000000 : ℝ) (251566802963/500000000000 : ℝ) (125783401479/250000000000 : ℝ) (251566802963/500000000000 : ℝ) (125783401479/250000000000 : ℝ) (251566802963/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8569/65536 : ℝ))) 6 (125783401479/250000000000 : ℝ) (251566802963/500000000000 : ℝ) (125783401479/250000000000 : ℝ) (251566802963/500000000000 : ℝ) (125783401479/250000000000 : ℝ) (251566802963/500000000000 : ℝ) (125783401479/250000000000 : ℝ) (251566802963/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8569/65536 : ℝ))) 7 (125783401479/250000000000 : ℝ) (251566802963/500000000000 : ℝ) (125783401479/250000000000 : ℝ) (251566802963/500000000000 : ℝ) (125783401479/250000000000 : ℝ) (251566802963/500000000000 : ℝ) (125783401479/250000000000 : ℝ) (251566802963/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8569/65536 : ℝ)) hmem 8 (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ) (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8569/65536 : ℝ))) hcmem 8 (125783401479/250000000000 : ℝ) (251566802963/500000000000 : ℝ) (125783401479/250000000000 : ℝ) (251566802963/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8569/65536 : ℝ)) (991877824771/1000000000000 : ℝ) (495938912387/500000000000 : ℝ) (125783401479/250000000000 : ℝ) (251566802963/500000000000 : ℝ) (199198026289/250000000000 : ℝ) (31871684207/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1559_exp_lower
  have heNumeric : (1027462715459/500000000000 : ℝ)/4 ≤ Real.exp (-53284384039/80000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027462715459/500000000000 : ℝ)/4 ≤ Real.exp ((1071/8192 : ℝ)-(31871684207/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1071/8192 : ℝ) (8569/65536 : ℝ) (31871684207/40000000000 : ℝ) (1027462715459/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1560; no trusted numerical premise.
theorem cover8_leaf1560_exp_radius : (498979419392860451/500000000000000000 : ℝ) ≤ Real.exp ((-4285/262144 : ℝ)/8) ∧ Real.exp ((-4285/262144 : ℝ)/8) ≤ (997958838785720903/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4285/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1560_exp_lower : (460057406797406951/500000000000000000 : ℝ) ≤ Real.exp ((-10656872875511/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656872875511/16000000000000 : ℝ)/8) ≤ (920114813594813903/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656872875511/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1560_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027462967977/500000000000 : ℝ) ≤ 4*Real.exp (8569/65536 : ℝ)*Real.exp (-mu (radius 8 (4285/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027462967977/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4285/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1560_exp_radius
  have hrNumeric : (24594672319/25000000000 : ℝ) ≤ Real.exp (-4285/262144 : ℝ) ∧ Real.exp (-4285/262144 : ℝ) ≤ (983786892761/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24594672319/25000000000 : ℝ) ≤ (radius 8 (4285/32768 : ℝ)) ∧ (radius 8 (4285/32768 : ℝ)) ≤ (983786892761/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4285/32768 : ℝ)) (24594672319/25000000000 : ℝ) (983786892761/1000000000000 : ℝ) (89670716557/500000000000 : ℝ) (179341433121/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4285/32768 : ℝ)) (24594672319/25000000000 : ℝ) (983786892761/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4285/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24594672319/25000000000 : ℝ) (983786892761/1000000000000 : ℝ) (49594672319/50000000000 : ℝ) (991893446381/1000000000000 : ℝ) (495930159589/500000000000 : ℝ) (991860319179/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4285/32768 : ℝ)) 1 (49594672319/50000000000 : ℝ) (991893446381/1000000000000 : ℝ) (495930159589/500000000000 : ℝ) (991860319179/1000000000000 : ℝ) (991876882779/1000000000000 : ℝ) (49593844139/50000000000 : ℝ) (12398461033/12500000000 : ℝ) (495938441321/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4285/32768 : ℝ)) 2 (991876882779/1000000000000 : ℝ) (49593844139/50000000000 : ℝ) (12398461033/12500000000 : ℝ) (495938441321/500000000000 : ℝ) (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ) (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4285/32768 : ℝ)) 3 (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ) (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ) (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ) (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4285/32768 : ℝ)) 4 (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ) (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ) (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ) (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4285/32768 : ℝ)) 5 (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ) (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ) (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ) (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4285/32768 : ℝ)) 6 (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ) (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ) (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ) (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4285/32768 : ℝ)) 7 (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ) (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ) (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ) (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4285/32768 : ℝ))) (89670716557/500000000000 : ℝ) (179341433121/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4285/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89670716557/500000000000 : ℝ) (179341433121/1000000000000 : ℝ) (589670716557/1000000000000 : ℝ) (589670716561/1000000000000 : ℝ) (84697445797/200000000000 : ℝ) (211743614497/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4285/32768 : ℝ))) 1 (589670716557/1000000000000 : ℝ) (589670716561/1000000000000 : ℝ) (84697445797/200000000000 : ℝ) (211743614497/500000000000 : ℝ) (506578972771/1000000000000 : ℝ) (253289486389/500000000000 : ℝ) (499717938209/1000000000000 : ℝ) (499717938217/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4285/32768 : ℝ))) 2 (506578972771/1000000000000 : ℝ) (253289486389/500000000000 : ℝ) (499717938209/1000000000000 : ℝ) (499717938217/1000000000000 : ℝ) (50314845549/100000000000 : ℝ) (251574227749/500000000000 : ℝ) (251568380273/500000000000 : ℝ) (251568380277/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4285/32768 : ℝ))) 3 (50314845549/100000000000 : ℝ) (251574227749/500000000000 : ℝ) (251568380273/500000000000 : ℝ) (251568380277/500000000000 : ℝ) (251571304009/500000000000 : ℝ) (251571304013/500000000000 : ℝ) (31446412999/62500000000 : ℝ) (503142607993/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4285/32768 : ℝ))) 4 (251571304009/500000000000 : ℝ) (251571304013/500000000000 : ℝ) (31446412999/62500000000 : ℝ) (503142607993/1000000000000 : ℝ) (503142608001/1000000000000 : ℝ) (50314260801/100000000000 : ℝ) (31446413/62500000 : ℝ) (50314260801/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4285/32768 : ℝ))) 5 (503142608001/1000000000000 : ℝ) (50314260801/100000000000 : ℝ) (31446413/62500000 : ℝ) (50314260801/100000000000 : ℝ) (31446413/62500000 : ℝ) (50314260801/100000000000 : ℝ) (31446413/62500000 : ℝ) (50314260801/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4285/32768 : ℝ))) 6 (31446413/62500000 : ℝ) (50314260801/100000000000 : ℝ) (31446413/62500000 : ℝ) (50314260801/100000000000 : ℝ) (31446413/62500000 : ℝ) (50314260801/100000000000 : ℝ) (31446413/62500000 : ℝ) (50314260801/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4285/32768 : ℝ))) 7 (31446413/62500000 : ℝ) (50314260801/100000000000 : ℝ) (31446413/62500000 : ℝ) (50314260801/100000000000 : ℝ) (31446413/62500000 : ℝ) (50314260801/100000000000 : ℝ) (31446413/62500000 : ℝ) (50314260801/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4285/32768 : ℝ)) hmem 8 (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ) (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4285/32768 : ℝ))) hcmem 8 (31446413/62500000 : ℝ) (50314260801/100000000000 : ℝ) (31446413/62500000 : ℝ) (50314260801/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4285/32768 : ℝ)) (991876882709/1000000000000 : ℝ) (991876882711/1000000000000 : ℝ) (31446413/62500000 : ℝ) (50314260801/100000000000 : ℝ) (398403559089/500000000000 : ℝ) (199201779549/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1560_exp_lower
  have heNumeric : (1027462967977/500000000000 : ℝ)/4 ≤ Real.exp (-10656872875511/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027462967977/500000000000 : ℝ)/4 ≤ Real.exp ((8569/65536 : ℝ)-(199201779549/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8569/65536 : ℝ) (4285/32768 : ℝ) (199201779549/250000000000 : ℝ) (1027462967977/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1561; no trusted numerical premise.
theorem cover8_leaf1561_exp_radius : (24948965021345523/25000000000000000 : ℝ) ≤ Real.exp ((-8571/524288 : ℝ)/8) ∧ Real.exp ((-8571/524288 : ℝ)/8) ≤ (997958600853820921/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8571/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1561_exp_lower : (920114841997615681/1000000000000000000 : ℝ) ≤ Real.exp ((-1065686892431/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065686892431/1600000000000 : ℝ)/8) ≤ (460057420998807841/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065686892431/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1561_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027463221709/500000000000 : ℝ) ≤ 4*Real.exp (4285/32768 : ℝ)*Real.exp (-mu (radius 8 (8571/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027463221709/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8571/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1561_exp_radius
  have hrNumeric : (983785016337/1000000000000 : ℝ) ≤ Real.exp (-8571/524288 : ℝ) ∧ Real.exp (-8571/524288 : ℝ) ≤ (491892508169/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983785016337/1000000000000 : ℝ) ≤ (radius 8 (8571/65536 : ℝ)) ∧ (radius 8 (8571/65536 : ℝ)) ≤ (491892508169/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8571/65536 : ℝ)) (983785016337/1000000000000 : ℝ) (491892508169/500000000000 : ℝ) (89675863013/500000000000 : ℝ) (179351726033/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8571/65536 : ℝ)) (983785016337/1000000000000 : ℝ) (491892508169/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8571/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983785016337/1000000000000 : ℝ) (491892508169/500000000000 : ℝ) (123986563521/125000000000 : ℝ) (991892508169/1000000000000 : ℝ) (495929686633/500000000000 : ℝ) (247964843317/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8571/65536 : ℝ)) 1 (123986563521/125000000000 : ℝ) (991892508169/1000000000000 : ℝ) (495929686633/500000000000 : ℝ) (247964843317/250000000000 : ℝ) (991875940717/1000000000000 : ℝ) (991875940719/1000000000000 : ℝ) (495937970289/500000000000 : ℝ) (991875940581/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8571/65536 : ℝ)) 2 (991875940717/1000000000000 : ℝ) (991875940719/1000000000000 : ℝ) (495937970289/500000000000 : ℝ) (991875940581/1000000000000 : ℝ) (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ) (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8571/65536 : ℝ)) 3 (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ) (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ) (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ) (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8571/65536 : ℝ)) 4 (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ) (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ) (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ) (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8571/65536 : ℝ)) 5 (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ) (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ) (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ) (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8571/65536 : ℝ)) 6 (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ) (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ) (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ) (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8571/65536 : ℝ)) 7 (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ) (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ) (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ) (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8571/65536 : ℝ))) (89675863013/500000000000 : ℝ) (179351726033/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8571/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89675863013/500000000000 : ℝ) (179351726033/1000000000000 : ℝ) (589675863013/1000000000000 : ℝ) (589675863017/1000000000000 : ℝ) (3308588917/7812500000 : ℝ) (84699876277/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8571/65536 : ℝ))) 1 (589675863013/1000000000000 : ℝ) (589675863017/1000000000000 : ℝ) (3308588917/7812500000 : ℝ) (84699876277/200000000000 : ℝ) (253293811097/500000000000 : ℝ) (506587622201/1000000000000 : ℝ) (249863644413/500000000000 : ℝ) (249863644417/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8571/65536 : ℝ))) 2 (253293811097/500000000000 : ℝ) (506587622201/1000000000000 : ℝ) (249863644413/500000000000 : ℝ) (249863644417/500000000000 : ℝ) (50315745551/100000000000 : ℝ) (251578727759/500000000000 : ℝ) (100629152633/200000000000 : ℝ) (251572881587/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8571/65536 : ℝ))) 3 (50315745551/100000000000 : ℝ) (251578727759/500000000000 : ℝ) (100629152633/200000000000 : ℝ) (251572881587/500000000000 : ℝ) (503151609337/1000000000000 : ℝ) (251575804673/500000000000 : ℝ) (503151609303/1000000000000 : ℝ) (503151609313/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8571/65536 : ℝ))) 4 (503151609337/1000000000000 : ℝ) (251575804673/500000000000 : ℝ) (503151609303/1000000000000 : ℝ) (503151609313/1000000000000 : ℝ) (12578790233/25000000000 : ℝ) (50315160933/100000000000 : ℝ) (503151609319/1000000000000 : ℝ) (50315160933/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8571/65536 : ℝ))) 5 (12578790233/25000000000 : ℝ) (50315160933/100000000000 : ℝ) (503151609319/1000000000000 : ℝ) (50315160933/100000000000 : ℝ) (503151609319/1000000000000 : ℝ) (50315160933/100000000000 : ℝ) (503151609319/1000000000000 : ℝ) (50315160933/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8571/65536 : ℝ))) 6 (503151609319/1000000000000 : ℝ) (50315160933/100000000000 : ℝ) (503151609319/1000000000000 : ℝ) (50315160933/100000000000 : ℝ) (503151609319/1000000000000 : ℝ) (50315160933/100000000000 : ℝ) (503151609319/1000000000000 : ℝ) (50315160933/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8571/65536 : ℝ))) 7 (503151609319/1000000000000 : ℝ) (50315160933/100000000000 : ℝ) (503151609319/1000000000000 : ℝ) (50315160933/100000000000 : ℝ) (503151609319/1000000000000 : ℝ) (50315160933/100000000000 : ℝ) (503151609319/1000000000000 : ℝ) (50315160933/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8571/65536 : ℝ)) hmem 8 (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ) (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8571/65536 : ℝ))) hcmem 8 (503151609319/1000000000000 : ℝ) (50315160933/100000000000 : ℝ) (503151609319/1000000000000 : ℝ) (50315160933/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8571/65536 : ℝ)) (991875940647/1000000000000 : ℝ) (19837518813/20000000000 : ℝ) (503151609319/1000000000000 : ℝ) (50315160933/100000000000 : ℝ) (398411065007/500000000000 : ℝ) (159364426007/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1561_exp_lower
  have heNumeric : (1027463221709/500000000000 : ℝ)/4 ≤ Real.exp (-1065686892431/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027463221709/500000000000 : ℝ)/4 ≤ Real.exp ((4285/32768 : ℝ)-(159364426007/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4285/32768 : ℝ) (8571/65536 : ℝ) (159364426007/200000000000 : ℝ) (1027463221709/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1562; no trusted numerical premise.
theorem cover8_leaf1562_exp_radius : (498979181460988833/500000000000000000 : ℝ) ≤ Real.exp ((-2143/131072 : ℝ)/8) ∧ Real.exp ((-2143/131072 : ℝ)/8) ≤ (997958362921977667/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2143/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1562_exp_lower : (920114870537170409/1000000000000000000 : ℝ) ≤ Real.exp ((-2131372990817/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131372990817/3200000000000 : ℝ)/8) ≤ (92011487053717041/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131372990817/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1562_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (82197078133/40000000000 : ℝ) ≤ 4*Real.exp (8571/65536 : ℝ)*Real.exp (-mu (radius 8 (2143/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (82197078133/40000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2143/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1562_exp_radius
  have hrNumeric : (491891569959/500000000000 : ℝ) ≤ Real.exp (-2143/131072 : ℝ) ∧ Real.exp (-2143/131072 : ℝ) ≤ (983783139919/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491891569959/500000000000 : ℝ) ≤ (radius 8 (2143/16384 : ℝ)) ∧ (radius 8 (2143/16384 : ℝ)) ≤ (983783139919/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2143/16384 : ℝ)) (491891569959/500000000000 : ℝ) (983783139919/1000000000000 : ℝ) (89681009153/500000000000 : ℝ) (179362018313/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2143/16384 : ℝ)) (491891569959/500000000000 : ℝ) (983783139919/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2143/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491891569959/500000000000 : ℝ) (983783139919/1000000000000 : ℝ) (991891569959/1000000000000 : ℝ) (24797289249/25000000000 : ℝ) (247964606839/250000000000 : ℝ) (991858427357/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2143/16384 : ℝ)) 1 (991891569959/1000000000000 : ℝ) (24797289249/25000000000 : ℝ) (247964606839/250000000000 : ℝ) (991858427357/1000000000000 : ℝ) (991874998657/1000000000000 : ℝ) (991874998659/1000000000000 : ℝ) (991874998519/1000000000000 : ℝ) (991874998521/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2143/16384 : ℝ)) 2 (991874998657/1000000000000 : ℝ) (991874998659/1000000000000 : ℝ) (991874998519/1000000000000 : ℝ) (991874998521/1000000000000 : ℝ) (247968749647/250000000000 : ℝ) (99187499859/100000000000 : ℝ) (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2143/16384 : ℝ)) 3 (247968749647/250000000000 : ℝ) (99187499859/100000000000 : ℝ) (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ) (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ) (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2143/16384 : ℝ)) 4 (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ) (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ) (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ) (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2143/16384 : ℝ)) 5 (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ) (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ) (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ) (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2143/16384 : ℝ)) 6 (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ) (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ) (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ) (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2143/16384 : ℝ)) 7 (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ) (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ) (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ) (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2143/16384 : ℝ))) (89681009153/500000000000 : ℝ) (179362018313/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2143/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89681009153/500000000000 : ℝ) (179362018313/1000000000000 : ℝ) (589681009153/1000000000000 : ℝ) (589681009157/1000000000000 : ℝ) (423511532671/1000000000000 : ℝ) (423511532681/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2143/16384 : ℝ))) 1 (589681009153/1000000000000 : ℝ) (589681009157/1000000000000 : ℝ) (423511532671/1000000000000 : ℝ) (423511532681/1000000000000 : ℝ) (7915566733/15625000000 : ℝ) (506596270919/1000000000000 : ℝ) (249868319307/500000000000 : ℝ) (249868319311/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2143/16384 : ℝ))) 2 (7915566733/15625000000 : ℝ) (506596270919/1000000000000 : ℝ) (249868319307/500000000000 : ℝ) (249868319311/500000000000 : ℝ) (503166454763/1000000000000 : ℝ) (503166454771/1000000000000 : ℝ) (503154765017/1000000000000 : ℝ) (251577382513/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2143/16384 : ℝ))) 3 (503166454763/1000000000000 : ℝ) (503166454771/1000000000000 : ℝ) (503154765017/1000000000000 : ℝ) (251577382513/500000000000 : ℝ) (50316060989/100000000000 : ℝ) (503160609899/1000000000000 : ℝ) (7861884529/15625000000 : ℝ) (100632121973/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2143/16384 : ℝ))) 4 (50316060989/100000000000 : ℝ) (503160609899/1000000000000 : ℝ) (7861884529/15625000000 : ℝ) (100632121973/200000000000 : ℝ) (503160609873/1000000000000 : ℝ) (251580304941/500000000000 : ℝ) (31447538117/62500000000 : ℝ) (251580304941/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2143/16384 : ℝ))) 5 (503160609873/1000000000000 : ℝ) (251580304941/500000000000 : ℝ) (31447538117/62500000000 : ℝ) (251580304941/500000000000 : ℝ) (31447538117/62500000000 : ℝ) (251580304941/500000000000 : ℝ) (31447538117/62500000000 : ℝ) (251580304941/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2143/16384 : ℝ))) 6 (31447538117/62500000000 : ℝ) (251580304941/500000000000 : ℝ) (31447538117/62500000000 : ℝ) (251580304941/500000000000 : ℝ) (31447538117/62500000000 : ℝ) (251580304941/500000000000 : ℝ) (31447538117/62500000000 : ℝ) (251580304941/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2143/16384 : ℝ))) 7 (31447538117/62500000000 : ℝ) (251580304941/500000000000 : ℝ) (31447538117/62500000000 : ℝ) (251580304941/500000000000 : ℝ) (31447538117/62500000000 : ℝ) (251580304941/500000000000 : ℝ) (31447538117/62500000000 : ℝ) (251580304941/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2143/16384 : ℝ)) hmem 8 (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ) (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2143/16384 : ℝ))) hcmem 8 (31447538117/62500000000 : ℝ) (251580304941/500000000000 : ℝ) (31447538117/62500000000 : ℝ) (251580304941/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2143/16384 : ℝ)) (991874998587/1000000000000 : ℝ) (99187499859/100000000000 : ℝ) (31447538117/62500000000 : ℝ) (251580304941/500000000000 : ℝ) (398418570333/500000000000 : ℝ) (159367428137/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1562_exp_lower
  have heNumeric : (82197078133/40000000000 : ℝ)/4 ≤ Real.exp (-2131372990817/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (82197078133/40000000000 : ℝ)/4 ≤ Real.exp ((8571/65536 : ℝ)-(159367428137/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8571/65536 : ℝ) (2143/16384 : ℝ) (159367428137/200000000000 : ℝ) (82197078133/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1563; no trusted numerical premise.
theorem cover8_leaf1563_exp_radius : (49897906249509557/50000000000000000 : ℝ) ≤ Real.exp ((-8573/524288 : ℝ)/8) ∧ Real.exp ((-8573/524288 : ℝ)/8) ≤ (997958124990191141/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8573/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1563_exp_lower : (920114899212672999/1000000000000000000 : ℝ) ≤ Real.exp ((-2664215241237/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664215241237/4000000000000 : ℝ)/8) ≤ (920114899212673/1000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664215241237/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1563_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027463732831/500000000000 : ℝ) ≤ 4*Real.exp (2143/16384 : ℝ)*Real.exp (-mu (radius 8 (8573/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027463732831/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8573/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1563_exp_radius
  have hrNumeric : (491890631751/500000000000 : ℝ) ≤ Real.exp (-8573/524288 : ℝ) ∧ Real.exp (-8573/524288 : ℝ) ≤ (983781263503/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491890631751/500000000000 : ℝ) ≤ (radius 8 (8573/65536 : ℝ)) ∧ (radius 8 (8573/65536 : ℝ)) ≤ (983781263503/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8573/65536 : ℝ)) (491890631751/500000000000 : ℝ) (983781263503/1000000000000 : ℝ) (4484307749/25000000000 : ℝ) (89686154983/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8573/65536 : ℝ)) (491890631751/500000000000 : ℝ) (983781263503/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8573/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491890631751/500000000000 : ℝ) (983781263503/1000000000000 : ℝ) (991890631751/1000000000000 : ℝ) (123986328969/125000000000 : ℝ) (495928740723/500000000000 : ℝ) (123982185181/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8573/65536 : ℝ)) 1 (991890631751/1000000000000 : ℝ) (123986328969/125000000000 : ℝ) (495928740723/500000000000 : ℝ) (123982185181/125000000000 : ℝ) (495937028299/500000000000 : ℝ) (4959370283/5000000000 : ℝ) (49593702823/50000000000 : ℝ) (495937028231/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8573/65536 : ℝ)) 2 (495937028299/500000000000 : ℝ) (4959370283/5000000000 : ℝ) (49593702823/50000000000 : ℝ) (495937028231/500000000000 : ℝ) (991874056529/1000000000000 : ℝ) (991874056531/1000000000000 : ℝ) (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8573/65536 : ℝ)) 3 (991874056529/1000000000000 : ℝ) (991874056531/1000000000000 : ℝ) (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ) (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ) (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8573/65536 : ℝ)) 4 (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ) (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ) (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ) (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8573/65536 : ℝ)) 5 (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ) (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ) (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ) (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8573/65536 : ℝ)) 6 (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ) (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ) (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ) (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8573/65536 : ℝ)) 7 (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ) (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ) (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ) (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8573/65536 : ℝ))) (4484307749/25000000000 : ℝ) (89686154983/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8573/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4484307749/25000000000 : ℝ) (89686154983/500000000000 : ℝ) (29484307749/50000000000 : ℝ) (589686154983/1000000000000 : ℝ) (423523682879/1000000000000 : ℝ) (423523682887/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8573/65536 : ℝ))) 1 (29484307749/50000000000 : ℝ) (589686154983/1000000000000 : ℝ) (423523682879/1000000000000 : ℝ) (423523682887/1000000000000 : ℝ) (506604918929/1000000000000 : ℝ) (101320983787/200000000000 : ℝ) (499745987577/1000000000000 : ℝ) (488033191/976562500 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8573/65536 : ℝ))) 2 (506604918929/1000000000000 : ℝ) (101320983787/200000000000 : ℝ) (499745987577/1000000000000 : ℝ) (488033191/976562500 : ℝ) (503175453253/1000000000000 : ℝ) (25158772663/50000000000 : ℝ) (100632753221/200000000000 : ℝ) (503163766113/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8573/65536 : ℝ))) 3 (503175453253/1000000000000 : ℝ) (25158772663/50000000000 : ℝ) (100632753221/200000000000 : ℝ) (503163766113/1000000000000 : ℝ) (503169609679/1000000000000 : ℝ) (503169609687/1000000000000 : ℝ) (100633921929/200000000000 : ℝ) (503169609653/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8573/65536 : ℝ))) 4 (503169609679/1000000000000 : ℝ) (503169609687/1000000000000 : ℝ) (100633921929/200000000000 : ℝ) (503169609653/1000000000000 : ℝ) (251584804831/500000000000 : ℝ) (50316960967/100000000000 : ℝ) (503169609661/1000000000000 : ℝ) (50316960967/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8573/65536 : ℝ))) 5 (251584804831/500000000000 : ℝ) (50316960967/100000000000 : ℝ) (503169609661/1000000000000 : ℝ) (50316960967/100000000000 : ℝ) (503169609661/1000000000000 : ℝ) (50316960967/100000000000 : ℝ) (503169609661/1000000000000 : ℝ) (50316960967/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8573/65536 : ℝ))) 6 (503169609661/1000000000000 : ℝ) (50316960967/100000000000 : ℝ) (503169609661/1000000000000 : ℝ) (50316960967/100000000000 : ℝ) (503169609661/1000000000000 : ℝ) (50316960967/100000000000 : ℝ) (503169609661/1000000000000 : ℝ) (50316960967/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8573/65536 : ℝ))) 7 (503169609661/1000000000000 : ℝ) (50316960967/100000000000 : ℝ) (503169609661/1000000000000 : ℝ) (50316960967/100000000000 : ℝ) (503169609661/1000000000000 : ℝ) (50316960967/100000000000 : ℝ) (503169609661/1000000000000 : ℝ) (50316960967/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8573/65536 : ℝ)) hmem 8 (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ) (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8573/65536 : ℝ))) hcmem 8 (503169609661/1000000000000 : ℝ) (50316960967/100000000000 : ℝ) (503169609661/1000000000000 : ℝ) (50316960967/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8573/65536 : ℝ)) (61992128533/62500000000 : ℝ) (991874056531/1000000000000 : ℝ) (503169609661/1000000000000 : ℝ) (50316960967/100000000000 : ℝ) (159370430027/200000000000 : ℝ) (796852150153/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1563_exp_lower
  have heNumeric : (1027463732831/500000000000 : ℝ)/4 ≤ Real.exp (-2664215241237/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027463732831/500000000000 : ℝ)/4 ≤ Real.exp ((2143/16384 : ℝ)-(796852150153/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2143/16384 : ℝ) (8573/65536 : ℝ) (796852150153/1000000000000 : ℝ) (1027463732831/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1564; no trusted numerical premise.
theorem cover8_leaf1564_exp_radius : (49897894352923067/50000000000000000 : ℝ) ≤ Real.exp ((-4287/262144 : ℝ)/8) ∧ Real.exp ((-4287/262144 : ℝ)/8) ≤ (997957887058461341/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4287/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1564_exp_lower : (230028732006232141/250000000000000000 : ℝ) ≤ Real.exp ((-10656856956787/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656856956787/16000000000000 : ℝ)/8) ≤ (184022985604985713/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656856956787/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1564_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027463990221/500000000000 : ℝ) ≤ 4*Real.exp (8573/65536 : ℝ)*Real.exp (-mu (radius 8 (4287/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027463990221/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4287/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1564_exp_radius
  have hrNumeric : (98377938709/100000000000 : ℝ) ≤ Real.exp (-4287/262144 : ℝ) ∧ Real.exp (-4287/262144 : ℝ) ≤ (983779387091/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98377938709/100000000000 : ℝ) ≤ (radius 8 (4287/32768 : ℝ)) ∧ (radius 8 (4287/32768 : ℝ)) ≤ (983779387091/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4287/32768 : ℝ)) (98377938709/100000000000 : ℝ) (983779387091/1000000000000 : ℝ) (179382600981/1000000000000 : ℝ) (179382600987/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4287/32768 : ℝ)) (98377938709/100000000000 : ℝ) (983779387091/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4287/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98377938709/100000000000 : ℝ) (983779387091/1000000000000 : ℝ) (198377938709/200000000000 : ℝ) (495944846773/500000000000 : ℝ) (495928267769/500000000000 : ℝ) (991856535539/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4287/32768 : ℝ)) 1 (198377938709/200000000000 : ℝ) (495944846773/500000000000 : ℝ) (495928267769/500000000000 : ℝ) (991856535539/1000000000000 : ℝ) (991873114541/1000000000000 : ℝ) (991873114543/1000000000000 : ℝ) (495936557201/500000000000 : ℝ) (247968278601/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4287/32768 : ℝ)) 2 (991873114541/1000000000000 : ℝ) (991873114543/1000000000000 : ℝ) (495936557201/500000000000 : ℝ) (247968278601/250000000000 : ℝ) (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ) (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4287/32768 : ℝ)) 3 (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ) (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ) (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ) (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4287/32768 : ℝ)) 4 (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ) (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ) (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ) (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4287/32768 : ℝ)) 5 (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ) (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ) (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ) (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4287/32768 : ℝ)) 6 (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ) (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ) (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ) (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4287/32768 : ℝ)) 7 (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ) (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ) (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ) (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4287/32768 : ℝ))) (179382600981/1000000000000 : ℝ) (179382600987/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4287/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179382600981/1000000000000 : ℝ) (179382600987/1000000000000 : ℝ) (58969130049/100000000000 : ℝ) (294845650247/500000000000 : ℝ) (423535831991/1000000000000 : ℝ) (423535831999/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4287/32768 : ℝ))) 1 (58969130049/100000000000 : ℝ) (294845650247/500000000000 : ℝ) (423535831991/1000000000000 : ℝ) (423535831999/1000000000000 : ℝ) (3166334789/6250000000 : ℝ) (506613566247/1000000000000 : ℝ) (49975533571/100000000000 : ℝ) (499755335717/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4287/32768 : ℝ))) 2 (3166334789/6250000000 : ℝ) (506613566247/1000000000000 : ℝ) (49975533571/100000000000 : ℝ) (499755335717/1000000000000 : ℝ) (20127378039/40000000000 : ℝ) (251592225491/500000000000 : ℝ) (62896595803/125000000000 : ℝ) (15724148951/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4287/32768 : ℝ))) 3 (20127378039/40000000000 : ℝ) (251592225491/500000000000 : ℝ) (62896595803/125000000000 : ℝ) (15724148951/31250000000 : ℝ) (503178608699/1000000000000 : ℝ) (503178608707/1000000000000 : ℝ) (100635721733/200000000000 : ℝ) (251589304337/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4287/32768 : ℝ))) 4 (503178608699/1000000000000 : ℝ) (503178608707/1000000000000 : ℝ) (100635721733/200000000000 : ℝ) (251589304337/500000000000 : ℝ) (251589304341/500000000000 : ℝ) (503178608691/1000000000000 : ℝ) (503178608681/1000000000000 : ℝ) (503178608691/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4287/32768 : ℝ))) 5 (251589304341/500000000000 : ℝ) (503178608691/1000000000000 : ℝ) (503178608681/1000000000000 : ℝ) (503178608691/1000000000000 : ℝ) (503178608681/1000000000000 : ℝ) (503178608691/1000000000000 : ℝ) (503178608681/1000000000000 : ℝ) (503178608691/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4287/32768 : ℝ))) 6 (503178608681/1000000000000 : ℝ) (503178608691/1000000000000 : ℝ) (503178608681/1000000000000 : ℝ) (503178608691/1000000000000 : ℝ) (503178608681/1000000000000 : ℝ) (503178608691/1000000000000 : ℝ) (503178608681/1000000000000 : ℝ) (503178608691/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4287/32768 : ℝ))) 7 (503178608681/1000000000000 : ℝ) (503178608691/1000000000000 : ℝ) (503178608681/1000000000000 : ℝ) (503178608691/1000000000000 : ℝ) (503178608681/1000000000000 : ℝ) (503178608691/1000000000000 : ℝ) (503178608681/1000000000000 : ℝ) (503178608691/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4287/32768 : ℝ)) hmem 8 (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ) (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4287/32768 : ℝ))) hcmem 8 (503178608681/1000000000000 : ℝ) (503178608691/1000000000000 : ℝ) (503178608681/1000000000000 : ℝ) (503178608691/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4287/32768 : ℝ)) (991873114471/1000000000000 : ℝ) (495936557237/500000000000 : ℝ) (503178608681/1000000000000 : ℝ) (503178608691/1000000000000 : ℝ) (796867158413/1000000000000 : ℝ) (24902098701/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1564_exp_lower
  have heNumeric : (1027463990221/500000000000 : ℝ)/4 ≤ Real.exp (-10656856956787/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027463990221/500000000000 : ℝ)/4 ≤ Real.exp ((8573/65536 : ℝ)-(24902098701/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8573/65536 : ℝ) (4287/32768 : ℝ) (24902098701/31250000000 : ℝ) (1027463990221/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1565; no trusted numerical premise.
theorem cover8_leaf1565_exp_radius : (249489412281697067/250000000000000000 : ℝ) ≤ Real.exp ((-8575/524288 : ℝ)/8) ∧ Real.exp ((-8575/524288 : ℝ)/8) ≤ (997957649126788269/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8575/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1565_exp_lower : (920114956973592073/1000000000000000000 : ℝ) ≤ Real.exp ((-213137058593/320000000000 : ℝ)/8) ∧ Real.exp ((-213137058593/320000000000 : ℝ)/8) ≤ (460057478486796037/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-213137058593/320000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1565_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054928497659/1000000000000 : ℝ) ≤ 4*Real.exp (4287/32768 : ℝ)*Real.exp (-mu (radius 8 (8575/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054928497659/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8575/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1565_exp_radius
  have hrNumeric : (491888755341/500000000000 : ℝ) ≤ Real.exp (-8575/524288 : ℝ) ∧ Real.exp (-8575/524288 : ℝ) ≤ (983777510683/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491888755341/500000000000 : ℝ) ≤ (radius 8 (8575/65536 : ℝ)) ∧ (radius 8 (8575/65536 : ℝ)) ≤ (983777510683/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8575/65536 : ℝ)) (491888755341/500000000000 : ℝ) (983777510683/1000000000000 : ℝ) (17939289137/100000000000 : ℝ) (179392891377/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8575/65536 : ℝ)) (491888755341/500000000000 : ℝ) (983777510683/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8575/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491888755341/500000000000 : ℝ) (983777510683/1000000000000 : ℝ) (991888755341/1000000000000 : ℝ) (495944377671/500000000000 : ℝ) (99185558963/100000000000 : ℝ) (3874435897/3906250000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8575/65536 : ℝ)) 1 (991888755341/1000000000000 : ℝ) (495944377671/500000000000 : ℝ) (99185558963/100000000000 : ℝ) (3874435897/3906250000 : ℝ) (198374434497/200000000000 : ℝ) (991872172487/1000000000000 : ℝ) (495936086173/500000000000 : ℝ) (991872172349/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8575/65536 : ℝ)) 2 (198374434497/200000000000 : ℝ) (991872172487/1000000000000 : ℝ) (495936086173/500000000000 : ℝ) (991872172349/1000000000000 : ℝ) (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ) (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8575/65536 : ℝ)) 3 (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ) (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ) (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ) (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8575/65536 : ℝ)) 4 (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ) (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ) (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ) (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8575/65536 : ℝ)) 5 (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ) (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ) (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ) (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8575/65536 : ℝ)) 6 (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ) (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ) (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ) (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8575/65536 : ℝ)) 7 (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ) (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ) (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ) (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8575/65536 : ℝ))) (17939289137/100000000000 : ℝ) (179392891377/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8575/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17939289137/100000000000 : ℝ) (179392891377/1000000000000 : ℝ) (117939289137/200000000000 : ℝ) (589696445689/1000000000000 : ℝ) (423547980009/1000000000000 : ℝ) (211773990009/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8575/65536 : ℝ))) 1 (117939289137/200000000000 : ℝ) (589696445689/1000000000000 : ℝ) (423547980009/1000000000000 : ℝ) (211773990009/500000000000 : ℝ) (506622212847/1000000000000 : ℝ) (253311106427/500000000000 : ℝ) (249882341507/500000000000 : ℝ) (249882341511/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8575/65536 : ℝ))) 2 (506622212847/1000000000000 : ℝ) (253311106427/500000000000 : ℝ) (249882341507/500000000000 : ℝ) (249882341511/500000000000 : ℝ) (50319344793/100000000000 : ℝ) (251596723969/500000000000 : ℝ) (62897720747/125000000000 : ℝ) (100636353197/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8575/65536 : ℝ))) 3 (50319344793/100000000000 : ℝ) (251596723969/500000000000 : ℝ) (62897720747/125000000000 : ℝ) (100636353197/200000000000 : ℝ) (503187606953/1000000000000 : ℝ) (251593803481/500000000000 : ℝ) (503187606919/1000000000000 : ℝ) (31449225433/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8575/65536 : ℝ))) 4 (503187606953/1000000000000 : ℝ) (251593803481/500000000000 : ℝ) (503187606919/1000000000000 : ℝ) (31449225433/62500000000 : ℝ) (62898450867/125000000000 : ℝ) (100637521389/200000000000 : ℝ) (100637521387/200000000000 : ℝ) (100637521389/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8575/65536 : ℝ))) 5 (62898450867/125000000000 : ℝ) (100637521389/200000000000 : ℝ) (100637521387/200000000000 : ℝ) (100637521389/200000000000 : ℝ) (100637521387/200000000000 : ℝ) (100637521389/200000000000 : ℝ) (100637521387/200000000000 : ℝ) (100637521389/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8575/65536 : ℝ))) 6 (100637521387/200000000000 : ℝ) (100637521389/200000000000 : ℝ) (100637521387/200000000000 : ℝ) (100637521389/200000000000 : ℝ) (100637521387/200000000000 : ℝ) (100637521389/200000000000 : ℝ) (100637521387/200000000000 : ℝ) (100637521389/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8575/65536 : ℝ))) 7 (100637521387/200000000000 : ℝ) (100637521389/200000000000 : ℝ) (100637521387/200000000000 : ℝ) (100637521389/200000000000 : ℝ) (100637521387/200000000000 : ℝ) (100637521389/200000000000 : ℝ) (100637521387/200000000000 : ℝ) (100637521389/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8575/65536 : ℝ)) hmem 8 (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ) (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8575/65536 : ℝ))) hcmem 8 (100637521387/200000000000 : ℝ) (100637521389/200000000000 : ℝ) (100637521387/200000000000 : ℝ) (100637521389/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8575/65536 : ℝ)) (198374434483/200000000000 : ℝ) (495936086209/500000000000 : ℝ) (100637521387/200000000000 : ℝ) (100637521389/200000000000 : ℝ) (398441082753/500000000000 : ℝ) (31875286621/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1565_exp_lower
  have heNumeric : (2054928497659/1000000000000 : ℝ)/4 ≤ Real.exp (-213137058593/320000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054928497659/1000000000000 : ℝ)/4 ≤ Real.exp ((4287/32768 : ℝ)-(31875286621/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4287/32768 : ℝ) (8575/65536 : ℝ) (31875286621/40000000000 : ℝ) (2054928497659/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1566; no trusted numerical premise.
theorem cover8_leaf1566_exp_radius : (249489352798792981/250000000000000000 : ℝ) ≤ Real.exp ((-67/4096 : ℝ)/8) ∧ Real.exp ((-67/4096 : ℝ)/8) ≤ (39918296447806877/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1566_exp_lower : (920114986058318497/1000000000000000000 : ℝ) ≤ Real.exp ((-2131369776717/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131369776717/3200000000000 : ℝ)/8) ≤ (460057493029159249/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131369776717/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1566_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513732254327/250000000000 : ℝ) ≤ 4*Real.exp (8575/65536 : ℝ)*Real.exp (-mu (radius 8 (67/512 : ℝ))) ∧ (20549/10000 : ℝ) < (513732254327/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1566_exp_radius
  have hrNumeric : (983775634277/1000000000000 : ℝ) ≤ Real.exp (-67/4096 : ℝ) ∧ Real.exp (-67/4096 : ℝ) ≤ (491887817139/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983775634277/1000000000000 : ℝ) ≤ (radius 8 (67/512 : ℝ)) ∧ (radius 8 (67/512 : ℝ)) ≤ (491887817139/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67/512 : ℝ)) (983775634277/1000000000000 : ℝ) (491887817139/500000000000 : ℝ) (179403181133/1000000000000 : ℝ) (8970159057/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67/512 : ℝ)) (983775634277/1000000000000 : ℝ) (491887817139/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983775634277/1000000000000 : ℝ) (491887817139/500000000000 : ℝ) (495943908569/500000000000 : ℝ) (991887817139/1000000000000 : ℝ) (247963660931/250000000000 : ℝ) (39674185749/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67/512 : ℝ)) 1 (495943908569/500000000000 : ℝ) (991887817139/1000000000000 : ℝ) (247963660931/250000000000 : ℝ) (39674185749/40000000000 : ℝ) (991871230431/1000000000000 : ℝ) (30995975951/31250000000 : ℝ) (247967807573/250000000000 : ℝ) (495935615147/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67/512 : ℝ)) 2 (991871230431/1000000000000 : ℝ) (30995975951/31250000000 : ℝ) (247967807573/250000000000 : ℝ) (495935615147/500000000000 : ℝ) (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ) (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67/512 : ℝ)) 3 (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ) (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ) (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ) (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67/512 : ℝ)) 4 (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ) (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ) (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ) (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67/512 : ℝ)) 5 (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ) (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ) (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ) (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67/512 : ℝ)) 6 (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ) (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ) (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ) (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67/512 : ℝ)) 7 (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ) (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ) (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ) (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67/512 : ℝ))) (179403181133/1000000000000 : ℝ) (8970159057/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179403181133/1000000000000 : ℝ) (8970159057/50000000000 : ℝ) (294850795283/500000000000 : ℝ) (58970159057/100000000000 : ℝ) (423560126939/1000000000000 : ℝ) (105890031737/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67/512 : ℝ))) 1 (294850795283/500000000000 : ℝ) (58970159057/100000000000 : ℝ) (423560126939/1000000000000 : ℝ) (105890031737/250000000000 : ℝ) (247378349/488281250 : ℝ) (506630858759/1000000000000 : ℝ) (499774029493/1000000000000 : ℝ) (499774029501/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67/512 : ℝ))) 2 (247378349/488281250 : ℝ) (506630858759/1000000000000 : ℝ) (499774029493/1000000000000 : ℝ) (499774029501/1000000000000 : ℝ) (251601222061/500000000000 : ℝ) (50320244413/100000000000 : ℝ) (125797691191/250000000000 : ℝ) (125797691193/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67/512 : ℝ))) 3 (251601222061/500000000000 : ℝ) (50320244413/100000000000 : ℝ) (125797691191/250000000000 : ℝ) (125797691193/250000000000 : ℝ) (503196604443/1000000000000 : ℝ) (503196604451/1000000000000 : ℝ) (503196604409/1000000000000 : ℝ) (251598302209/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67/512 : ℝ))) 4 (503196604443/1000000000000 : ℝ) (503196604451/1000000000000 : ℝ) (503196604409/1000000000000 : ℝ) (251598302209/500000000000 : ℝ) (251598302213/500000000000 : ℝ) (100639320887/200000000000 : ℝ) (20127864177/40000000000 : ℝ) (100639320887/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67/512 : ℝ))) 5 (251598302213/500000000000 : ℝ) (100639320887/200000000000 : ℝ) (20127864177/40000000000 : ℝ) (100639320887/200000000000 : ℝ) (20127864177/40000000000 : ℝ) (100639320887/200000000000 : ℝ) (20127864177/40000000000 : ℝ) (100639320887/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67/512 : ℝ))) 6 (20127864177/40000000000 : ℝ) (100639320887/200000000000 : ℝ) (20127864177/40000000000 : ℝ) (100639320887/200000000000 : ℝ) (20127864177/40000000000 : ℝ) (100639320887/200000000000 : ℝ) (20127864177/40000000000 : ℝ) (100639320887/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67/512 : ℝ))) 7 (20127864177/40000000000 : ℝ) (100639320887/200000000000 : ℝ) (20127864177/40000000000 : ℝ) (100639320887/200000000000 : ℝ) (20127864177/40000000000 : ℝ) (100639320887/200000000000 : ℝ) (20127864177/40000000000 : ℝ) (100639320887/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67/512 : ℝ)) hmem 8 (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ) (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67/512 : ℝ))) hcmem 8 (20127864177/40000000000 : ℝ) (100639320887/200000000000 : ℝ) (20127864177/40000000000 : ℝ) (100639320887/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67/512 : ℝ)) (991871230361/1000000000000 : ℝ) (991871230363/1000000000000 : ℝ) (20127864177/40000000000 : ℝ) (100639320887/200000000000 : ℝ) (796897171417/1000000000000 : ℝ) (159379434287/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1566_exp_lower
  have heNumeric : (513732254327/250000000000 : ℝ)/4 ≤ Real.exp (-2131369776717/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513732254327/250000000000 : ℝ)/4 ≤ Real.exp ((8575/65536 : ℝ)-(159379434287/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8575/65536 : ℝ) (67/512 : ℝ) (159379434287/200000000000 : ℝ) (513732254327/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1567; no trusted numerical premise.
theorem cover8_leaf1567_exp_radius : (498978586631806153/500000000000000000 : ℝ) ≤ Real.exp ((-8577/524288 : ℝ)/8) ∧ Real.exp ((-8577/524288 : ℝ)/8) ≤ (997957173263612307/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8577/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1567_exp_lower : (115014376909816597/125000000000000000 : ℝ) ≤ Real.exp ((-666052801167/1000000000000 : ℝ)/8) ∧ Real.exp ((-666052801167/1000000000000 : ℝ)/8) ≤ (920115015278532777/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666052801167/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1567_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054929539377/1000000000000 : ℝ) ≤ 4*Real.exp (67/512 : ℝ)*Real.exp (-mu (radius 8 (8577/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054929539377/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8577/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1567_exp_radius
  have hrNumeric : (7870190063/8000000000 : ℝ) ≤ Real.exp (-8577/524288 : ℝ) ∧ Real.exp (-8577/524288 : ℝ) ≤ (245943439469/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (7870190063/8000000000 : ℝ) ≤ (radius 8 (8577/65536 : ℝ)) ∧ (radius 8 (8577/65536 : ℝ)) ≤ (245943439469/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8577/65536 : ℝ)) (7870190063/8000000000 : ℝ) (245943439469/250000000000 : ℝ) (17941347027/100000000000 : ℝ) (179413470277/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8577/65536 : ℝ)) (7870190063/8000000000 : ℝ) (245943439469/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8577/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (7870190063/8000000000 : ℝ) (245943439469/250000000000 : ℝ) (991886878937/1000000000000 : ℝ) (495943439469/500000000000 : ℝ) (991853697817/1000000000000 : ℝ) (991853697819/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8577/65536 : ℝ)) 1 (991886878937/1000000000000 : ℝ) (495943439469/500000000000 : ℝ) (991853697817/1000000000000 : ℝ) (991853697819/1000000000000 : ℝ) (991870288377/1000000000000 : ℝ) (991870288379/1000000000000 : ℝ) (495935144119/500000000000 : ℝ) (12398378603/12500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8577/65536 : ℝ)) 2 (991870288377/1000000000000 : ℝ) (991870288379/1000000000000 : ℝ) (495935144119/500000000000 : ℝ) (12398378603/12500000000 : ℝ) (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ) (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8577/65536 : ℝ)) 3 (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ) (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ) (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ) (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8577/65536 : ℝ)) 4 (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ) (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ) (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ) (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8577/65536 : ℝ)) 5 (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ) (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ) (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ) (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8577/65536 : ℝ)) 6 (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ) (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ) (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ) (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8577/65536 : ℝ)) 7 (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ) (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ) (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ) (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8577/65536 : ℝ))) (17941347027/100000000000 : ℝ) (179413470277/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8577/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17941347027/100000000000 : ℝ) (179413470277/1000000000000 : ℝ) (117941347027/200000000000 : ℝ) (589706735139/1000000000000 : ℝ) (211786136391/500000000000 : ℝ) (423572272791/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8577/65536 : ℝ))) 1 (117941347027/200000000000 : ℝ) (589706735139/1000000000000 : ℝ) (211786136391/500000000000 : ℝ) (423572272791/1000000000000 : ℝ) (253319751979/500000000000 : ℝ) (101327900793/200000000000 : ℝ) (499783375149/1000000000000 : ℝ) (499783375157/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8577/65536 : ℝ))) 2 (253319751979/500000000000 : ℝ) (101327900793/200000000000 : ℝ) (499783375149/1000000000000 : ℝ) (499783375157/1000000000000 : ℝ) (503211439553/1000000000000 : ℝ) (503211439561/1000000000000 : ℝ) (50319976279/100000000000 : ℝ) (251599881399/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8577/65536 : ℝ))) 3 (503211439553/1000000000000 : ℝ) (503211439561/1000000000000 : ℝ) (50319976279/100000000000 : ℝ) (251599881399/500000000000 : ℝ) (503205601171/1000000000000 : ℝ) (25160280059/50000000000 : ℝ) (503205601137/1000000000000 : ℝ) (251602800573/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8577/65536 : ℝ))) 4 (503205601171/1000000000000 : ℝ) (25160280059/50000000000 : ℝ) (503205601137/1000000000000 : ℝ) (251602800573/500000000000 : ℝ) (251602800577/500000000000 : ℝ) (503205601163/1000000000000 : ℝ) (503205601153/1000000000000 : ℝ) (503205601163/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8577/65536 : ℝ))) 5 (251602800577/500000000000 : ℝ) (503205601163/1000000000000 : ℝ) (503205601153/1000000000000 : ℝ) (503205601163/1000000000000 : ℝ) (503205601153/1000000000000 : ℝ) (503205601163/1000000000000 : ℝ) (503205601153/1000000000000 : ℝ) (503205601163/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8577/65536 : ℝ))) 6 (503205601153/1000000000000 : ℝ) (503205601163/1000000000000 : ℝ) (503205601153/1000000000000 : ℝ) (503205601163/1000000000000 : ℝ) (503205601153/1000000000000 : ℝ) (503205601163/1000000000000 : ℝ) (503205601153/1000000000000 : ℝ) (503205601163/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8577/65536 : ℝ))) 7 (503205601153/1000000000000 : ℝ) (503205601163/1000000000000 : ℝ) (503205601153/1000000000000 : ℝ) (503205601163/1000000000000 : ℝ) (503205601153/1000000000000 : ℝ) (503205601163/1000000000000 : ℝ) (503205601153/1000000000000 : ℝ) (503205601163/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8577/65536 : ℝ)) hmem 8 (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ) (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8577/65536 : ℝ))) hcmem 8 (503205601153/1000000000000 : ℝ) (503205601163/1000000000000 : ℝ) (503205601153/1000000000000 : ℝ) (503205601163/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8577/65536 : ℝ)) (991870288307/1000000000000 : ℝ) (99187028831/100000000000 : ℝ) (503205601153/1000000000000 : ℝ) (503205601163/1000000000000 : ℝ) (199228044037/250000000000 : ℝ) (796912176167/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1567_exp_lower
  have heNumeric : (2054929539377/1000000000000 : ℝ)/4 ≤ Real.exp (-666052801167/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054929539377/1000000000000 : ℝ)/4 ≤ Real.exp ((67/512 : ℝ)-(796912176167/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67/512 : ℝ) (8577/65536 : ℝ) (796912176167/1000000000000 : ℝ) (2054929539377/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1568; no trusted numerical premise.
theorem cover8_leaf1568_exp_radius : (124744616916513677/125000000000000000 : ℝ) ≤ Real.exp ((-4289/262144 : ℝ)/8) ∧ Real.exp ((-4289/262144 : ℝ)/8) ≤ (997956935332109417/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4289/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1568_exp_lower : (230028761159105049/250000000000000000 : ℝ) ≤ Real.exp ((-10656840734607/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656840734607/16000000000000 : ℝ)/8) ≤ (920115044636420197/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656840734607/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1568_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027465031953/500000000000 : ℝ) ≤ 4*Real.exp (8577/65536 : ℝ)*Real.exp (-mu (radius 8 (4289/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027465031953/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4289/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1568_exp_radius
  have hrNumeric : (491885940739/500000000000 : ℝ) ≤ Real.exp (-4289/262144 : ℝ) ∧ Real.exp (-4289/262144 : ℝ) ≤ (983771881479/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491885940739/500000000000 : ℝ) ≤ (radius 8 (4289/32768 : ℝ)) ∧ (radius 8 (4289/32768 : ℝ)) ≤ (983771881479/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4289/32768 : ℝ)) (491885940739/500000000000 : ℝ) (983771881479/1000000000000 : ℝ) (17942375877/100000000000 : ℝ) (22427969847/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4289/32768 : ℝ)) (491885940739/500000000000 : ℝ) (983771881479/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4289/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491885940739/500000000000 : ℝ) (983771881479/1000000000000 : ℝ) (991885940739/1000000000000 : ℝ) (49594297037/50000000000 : ℝ) (991852751913/1000000000000 : ℝ) (495926375957/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4289/32768 : ℝ)) 1 (991885940739/1000000000000 : ℝ) (49594297037/50000000000 : ℝ) (991852751913/1000000000000 : ℝ) (495926375957/500000000000 : ℝ) (495934673163/500000000000 : ℝ) (991869346327/1000000000000 : ℝ) (991869346187/1000000000000 : ℝ) (991869346189/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4289/32768 : ℝ)) 2 (495934673163/500000000000 : ℝ) (991869346327/1000000000000 : ℝ) (991869346187/1000000000000 : ℝ) (991869346189/1000000000000 : ℝ) (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ) (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4289/32768 : ℝ)) 3 (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ) (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ) (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ) (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4289/32768 : ℝ)) 4 (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ) (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ) (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ) (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4289/32768 : ℝ)) 5 (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ) (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ) (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ) (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4289/32768 : ℝ)) 6 (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ) (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ) (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ) (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4289/32768 : ℝ)) 7 (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ) (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ) (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ) (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4289/32768 : ℝ))) (17942375877/100000000000 : ℝ) (22427969847/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4289/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17942375877/100000000000 : ℝ) (22427969847/125000000000 : ℝ) (117942375877/200000000000 : ℝ) (147427969847/250000000000 : ℝ) (16943376701/40000000000 : ℝ) (423584417533/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4289/32768 : ℝ))) 1 (117942375877/200000000000 : ℝ) (147427969847/250000000000 : ℝ) (16943376701/40000000000 : ℝ) (423584417533/1000000000000 : ℝ) (101329629691/200000000000 : ℝ) (506648148461/1000000000000 : ℝ) (499792719971/1000000000000 : ℝ) (249896359989/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4289/32768 : ℝ))) 2 (101329629691/200000000000 : ℝ) (506648148461/1000000000000 : ℝ) (499792719971/1000000000000 : ℝ) (249896359989/500000000000 : ℝ) (503220434213/1000000000000 : ℝ) (25161021711/50000000000 : ℝ) (503208760043/1000000000000 : ℝ) (503208760051/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4289/32768 : ℝ))) 3 (503220434213/1000000000000 : ℝ) (25161021711/50000000000 : ℝ) (503208760043/1000000000000 : ℝ) (503208760051/1000000000000 : ℝ) (62901824641/125000000000 : ℝ) (31450912321/62500000000 : ℝ) (251607298547/500000000000 : ℝ) (251607298551/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4289/32768 : ℝ))) 4 (62901824641/125000000000 : ℝ) (31450912321/62500000000 : ℝ) (251607298547/500000000000 : ℝ) (251607298551/500000000000 : ℝ) (503214597111/1000000000000 : ℝ) (503214597119/1000000000000 : ℝ) (50321459711/100000000000 : ℝ) (503214597119/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4289/32768 : ℝ))) 5 (503214597111/1000000000000 : ℝ) (503214597119/1000000000000 : ℝ) (50321459711/100000000000 : ℝ) (503214597119/1000000000000 : ℝ) (50321459711/100000000000 : ℝ) (503214597119/1000000000000 : ℝ) (50321459711/100000000000 : ℝ) (503214597119/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4289/32768 : ℝ))) 6 (50321459711/100000000000 : ℝ) (503214597119/1000000000000 : ℝ) (50321459711/100000000000 : ℝ) (503214597119/1000000000000 : ℝ) (50321459711/100000000000 : ℝ) (503214597119/1000000000000 : ℝ) (50321459711/100000000000 : ℝ) (503214597119/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4289/32768 : ℝ))) 7 (50321459711/100000000000 : ℝ) (503214597119/1000000000000 : ℝ) (50321459711/100000000000 : ℝ) (503214597119/1000000000000 : ℝ) (50321459711/100000000000 : ℝ) (503214597119/1000000000000 : ℝ) (50321459711/100000000000 : ℝ) (503214597119/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4289/32768 : ℝ)) hmem 8 (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ) (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4289/32768 : ℝ))) hcmem 8 (50321459711/100000000000 : ℝ) (503214597119/1000000000000 : ℝ) (50321459711/100000000000 : ℝ) (503214597119/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4289/32768 : ℝ)) (61991834141/62500000000 : ℝ) (495934673129/500000000000 : ℝ) (50321459711/100000000000 : ℝ) (503214597119/1000000000000 : ℝ) (159385435937/200000000000 : ℝ) (398463589851/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1568_exp_lower
  have heNumeric : (1027465031953/500000000000 : ℝ)/4 ≤ Real.exp (-10656840734607/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027465031953/500000000000 : ℝ)/4 ≤ Real.exp ((8577/65536 : ℝ)-(398463589851/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8577/65536 : ℝ) (4289/32768 : ℝ) (398463589851/500000000000 : ℝ) (1027465031953/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1569; no trusted numerical premise.
theorem cover8_leaf1569_exp_radius : (997956697400663253/1000000000000000000 : ℝ) ≤ Real.exp ((-8579/524288 : ℝ)/8) ∧ Real.exp ((-8579/524288 : ℝ)/8) ≤ (498978348700331627/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8579/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1569_exp_lower : (920115074128875383/1000000000000000000 : ℝ) ≤ Real.exp ((-5328418315911/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328418315911/8000000000000 : ℝ)/8) ≤ (115014384266109423/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328418315911/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1569_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (51373264771/25000000000 : ℝ) ≤ 4*Real.exp (4289/32768 : ℝ)*Real.exp (-mu (radius 8 (8579/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (51373264771/25000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8579/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1569_exp_radius
  have hrNumeric : (983770005083/1000000000000 : ℝ) ≤ Real.exp (-8579/524288 : ℝ) ∧ Real.exp (-8579/524288 : ℝ) ≤ (245942501271/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983770005083/1000000000000 : ℝ) ≤ (radius 8 (8579/65536 : ℝ)) ∧ (radius 8 (8579/65536 : ℝ)) ≤ (245942501271/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8579/65536 : ℝ)) (983770005083/1000000000000 : ℝ) (245942501271/250000000000 : ℝ) (179434046649/1000000000000 : ℝ) (2803656979/15625000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8579/65536 : ℝ)) (983770005083/1000000000000 : ℝ) (245942501271/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8579/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983770005083/1000000000000 : ℝ) (245942501271/250000000000 : ℝ) (991885002541/1000000000000 : ℝ) (495942501271/500000000000 : ℝ) (123981475751/125000000000 : ℝ) (99185180601/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8579/65536 : ℝ)) 1 (991885002541/1000000000000 : ℝ) (495942501271/500000000000 : ℝ) (123981475751/125000000000 : ℝ) (99185180601/100000000000 : ℝ) (495934202137/500000000000 : ℝ) (247967101069/250000000000 : ℝ) (198373680827/200000000000 : ℝ) (495934202069/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8579/65536 : ℝ)) 2 (495934202137/500000000000 : ℝ) (247967101069/250000000000 : ℝ) (198373680827/200000000000 : ℝ) (495934202069/500000000000 : ℝ) (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ) (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8579/65536 : ℝ)) 3 (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ) (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ) (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ) (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8579/65536 : ℝ)) 4 (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ) (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ) (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ) (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8579/65536 : ℝ)) 5 (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ) (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ) (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ) (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8579/65536 : ℝ)) 6 (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ) (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ) (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ) (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8579/65536 : ℝ)) 7 (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ) (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ) (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ) (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8579/65536 : ℝ))) (179434046649/1000000000000 : ℝ) (2803656979/15625000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8579/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179434046649/1000000000000 : ℝ) (2803656979/15625000000 : ℝ) (147429255831/250000000000 : ℝ) (18428656979/31250000000 : ℝ) (211798280593/500000000000 : ℝ) (84719312239/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8579/65536 : ℝ))) 1 (147429255831/250000000000 : ℝ) (18428656979/31250000000 : ℝ) (211798280593/500000000000 : ℝ) (84719312239/200000000000 : ℝ) (101331358451/200000000000 : ℝ) (253328396131/500000000000 : ℝ) (249901031987/500000000000 : ℝ) (249901031991/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8579/65536 : ℝ))) 2 (101331358451/200000000000 : ℝ) (253328396131/500000000000 : ℝ) (249901031987/500000000000 : ℝ) (249901031991/500000000000 : ℝ) (251614714057/500000000000 : ℝ) (251614714061/500000000000 : ℝ) (251608878269/500000000000 : ℝ) (251608878273/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8579/65536 : ℝ))) 3 (251614714057/500000000000 : ℝ) (251614714061/500000000000 : ℝ) (251608878269/500000000000 : ℝ) (251608878273/500000000000 : ℝ) (251611796163/500000000000 : ℝ) (251611796167/500000000000 : ℝ) (125805898073/250000000000 : ℝ) (503223592301/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8579/65536 : ℝ))) 4 (251611796163/500000000000 : ℝ) (251611796167/500000000000 : ℝ) (125805898073/250000000000 : ℝ) (503223592301/1000000000000 : ℝ) (503223592309/1000000000000 : ℝ) (251611796159/500000000000 : ℝ) (125805898077/250000000000 : ℝ) (251611796159/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8579/65536 : ℝ))) 5 (503223592309/1000000000000 : ℝ) (251611796159/500000000000 : ℝ) (125805898077/250000000000 : ℝ) (251611796159/500000000000 : ℝ) (125805898077/250000000000 : ℝ) (251611796159/500000000000 : ℝ) (125805898077/250000000000 : ℝ) (251611796159/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8579/65536 : ℝ))) 6 (125805898077/250000000000 : ℝ) (251611796159/500000000000 : ℝ) (125805898077/250000000000 : ℝ) (251611796159/500000000000 : ℝ) (125805898077/250000000000 : ℝ) (251611796159/500000000000 : ℝ) (125805898077/250000000000 : ℝ) (251611796159/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8579/65536 : ℝ))) 7 (125805898077/250000000000 : ℝ) (251611796159/500000000000 : ℝ) (125805898077/250000000000 : ℝ) (251611796159/500000000000 : ℝ) (125805898077/250000000000 : ℝ) (251611796159/500000000000 : ℝ) (125805898077/250000000000 : ℝ) (251611796159/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8579/65536 : ℝ)) hmem 8 (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ) (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8579/65536 : ℝ))) hcmem 8 (125805898077/250000000000 : ℝ) (251611796159/500000000000 : ℝ) (125805898077/250000000000 : ℝ) (251611796159/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8579/65536 : ℝ)) (247967101051/250000000000 : ℝ) (991868404207/1000000000000 : ℝ) (125805898077/250000000000 : ℝ) (251611796159/500000000000 : ℝ) (24904443189/31250000000 : ℝ) (796942182067/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1569_exp_lower
  have heNumeric : (51373264771/25000000000 : ℝ)/4 ≤ Real.exp (-5328418315911/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (51373264771/25000000000 : ℝ)/4 ≤ Real.exp ((4289/32768 : ℝ)-(796942182067/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4289/32768 : ℝ) (8579/65536 : ℝ) (796942182067/1000000000000 : ℝ) (51373264771/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1570; no trusted numerical premise.
theorem cover8_leaf1570_exp_radius : (498978229734636909/500000000000000000 : ℝ) ≤ Real.exp ((-2145/131072 : ℝ)/8) ∧ Real.exp ((-2145/131072 : ℝ)/8) ≤ (997956459469273819/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2145/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1570_exp_lower : (460057551879501869/500000000000000000 : ℝ) ≤ Real.exp ((-2131366501977/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131366501977/3200000000000 : ℝ)/8) ≤ (920115103759003739/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131366501977/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1570_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054931120233/1000000000000 : ℝ) ≤ 4*Real.exp (8579/65536 : ℝ)*Real.exp (-mu (radius 8 (2145/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054931120233/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2145/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1570_exp_radius
  have hrNumeric : (983768128693/1000000000000 : ℝ) ≤ Real.exp (-2145/131072 : ℝ) ∧ Real.exp (-2145/131072 : ℝ) ≤ (491884064347/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983768128693/1000000000000 : ℝ) ≤ (radius 8 (2145/16384 : ℝ)) ∧ (radius 8 (2145/16384 : ℝ)) ≤ (491884064347/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2145/16384 : ℝ)) (983768128693/1000000000000 : ℝ) (491884064347/500000000000 : ℝ) (179444333891/1000000000000 : ℝ) (89722166949/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2145/16384 : ℝ)) (983768128693/1000000000000 : ℝ) (491884064347/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2145/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983768128693/1000000000000 : ℝ) (491884064347/500000000000 : ℝ) (495942032173/500000000000 : ℝ) (991884064347/1000000000000 : ℝ) (198370172021/200000000000 : ℝ) (991850860107/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2145/16384 : ℝ)) 1 (495942032173/500000000000 : ℝ) (991884064347/1000000000000 : ℝ) (198370172021/200000000000 : ℝ) (991850860107/1000000000000 : ℝ) (39674698489/40000000000 : ℝ) (991867462227/1000000000000 : ℝ) (495933731043/500000000000 : ℝ) (991867462089/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2145/16384 : ℝ)) 2 (39674698489/40000000000 : ℝ) (991867462227/1000000000000 : ℝ) (495933731043/500000000000 : ℝ) (991867462089/1000000000000 : ℝ) (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ) (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2145/16384 : ℝ)) 3 (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ) (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ) (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ) (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2145/16384 : ℝ)) 4 (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ) (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ) (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ) (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2145/16384 : ℝ)) 5 (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ) (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ) (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ) (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2145/16384 : ℝ)) 6 (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ) (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ) (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ) (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2145/16384 : ℝ)) 7 (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ) (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ) (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ) (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2145/16384 : ℝ))) (179444333891/1000000000000 : ℝ) (89722166949/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2145/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179444333891/1000000000000 : ℝ) (89722166949/500000000000 : ℝ) (117944433389/200000000000 : ℝ) (589722166949/1000000000000 : ℝ) (423608703747/1000000000000 : ℝ) (423608703757/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2145/16384 : ℝ))) 1 (117944433389/200000000000 : ℝ) (589722166949/1000000000000 : ℝ) (423608703747/1000000000000 : ℝ) (423608703757/1000000000000 : ℝ) (253332717673/500000000000 : ℝ) (506665435353/1000000000000 : ℝ) (499811407143/1000000000000 : ℝ) (499811407151/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2145/16384 : ℝ))) 2 (253332717673/500000000000 : ℝ) (506665435353/1000000000000 : ℝ) (499811407143/1000000000000 : ℝ) (499811407151/1000000000000 : ℝ) (125809605311/250000000000 : ℝ) (125809605313/250000000000 : ℝ) (25161337613/50000000000 : ℝ) (503226752269/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2145/16384 : ℝ))) 3 (125809605311/250000000000 : ℝ) (125809605313/250000000000 : ℝ) (25161337613/50000000000 : ℝ) (503226752269/1000000000000 : ℝ) (491438073/976562500 : ℝ) (503232586761/1000000000000 : ℝ) (251616293359/500000000000 : ℝ) (503232586727/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2145/16384 : ℝ))) 4 (491438073/976562500 : ℝ) (503232586761/1000000000000 : ℝ) (251616293359/500000000000 : ℝ) (503232586727/1000000000000 : ℝ) (100646517347/200000000000 : ℝ) (62904073343/125000000000 : ℝ) (251616293367/500000000000 : ℝ) (62904073343/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2145/16384 : ℝ))) 5 (100646517347/200000000000 : ℝ) (62904073343/125000000000 : ℝ) (251616293367/500000000000 : ℝ) (62904073343/125000000000 : ℝ) (251616293367/500000000000 : ℝ) (62904073343/125000000000 : ℝ) (251616293367/500000000000 : ℝ) (62904073343/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2145/16384 : ℝ))) 6 (251616293367/500000000000 : ℝ) (62904073343/125000000000 : ℝ) (251616293367/500000000000 : ℝ) (62904073343/125000000000 : ℝ) (251616293367/500000000000 : ℝ) (62904073343/125000000000 : ℝ) (251616293367/500000000000 : ℝ) (62904073343/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2145/16384 : ℝ))) 7 (251616293367/500000000000 : ℝ) (62904073343/125000000000 : ℝ) (251616293367/500000000000 : ℝ) (62904073343/125000000000 : ℝ) (251616293367/500000000000 : ℝ) (62904073343/125000000000 : ℝ) (251616293367/500000000000 : ℝ) (62904073343/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2145/16384 : ℝ)) hmem 8 (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ) (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2145/16384 : ℝ))) hcmem 8 (251616293367/500000000000 : ℝ) (62904073343/125000000000 : ℝ) (251616293367/500000000000 : ℝ) (62904073343/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2145/16384 : ℝ)) (198373492431/200000000000 : ℝ) (495933731079/500000000000 : ℝ) (251616293367/500000000000 : ℝ) (62904073343/125000000000 : ℝ) (49809823951/62500000000 : ℝ) (159391436647/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1570_exp_lower
  have heNumeric : (2054931120233/1000000000000 : ℝ)/4 ≤ Real.exp (-2131366501977/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054931120233/1000000000000 : ℝ)/4 ≤ Real.exp ((8579/65536 : ℝ)-(159391436647/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8579/65536 : ℝ) (2145/16384 : ℝ) (159391436647/200000000000 : ℝ) (2054931120233/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1571; no trusted numerical premise.
theorem cover8_leaf1571_exp_radius : (997955983606665129/1000000000000000000 : ℝ) ≤ Real.exp ((-4291/262144 : ℝ)/8) ∧ Real.exp ((-4291/262144 : ℝ)/8) ≤ (99795598360666513/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4291/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1571_exp_lower : (920113408447228899/1000000000000000000 : ℝ) ≤ Real.exp ((-532853417503/800000000000 : ℝ)/8) ∧ Real.exp ((-532853417503/800000000000 : ℝ)/8) ≤ (9201134084472289/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-532853417503/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1571_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900830749/1000000000000 : ℝ) ≤ 4*Real.exp (2145/16384 : ℝ)*Real.exp (-mu (radius 8 (4291/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900830749/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4291/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1571_exp_radius
  have hrNumeric : (491882187961/500000000000 : ℝ) ≤ Real.exp (-4291/262144 : ℝ) ∧ Real.exp (-4291/262144 : ℝ) ≤ (983764375923/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491882187961/500000000000 : ℝ) ≤ (radius 8 (4291/32768 : ℝ)) ∧ (radius 8 (4291/32768 : ℝ)) ≤ (983764375923/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4291/32768 : ℝ)) (491882187961/500000000000 : ℝ) (983764375923/1000000000000 : ℝ) (179464906499/1000000000000 : ℝ) (35892981301/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4291/32768 : ℝ)) (491882187961/500000000000 : ℝ) (983764375923/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4291/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491882187961/500000000000 : ℝ) (983764375923/1000000000000 : ℝ) (991882187961/1000000000000 : ℝ) (495941093981/500000000000 : ℝ) (495924484151/500000000000 : ℝ) (991848968303/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4291/32768 : ℝ)) 1 (991882187961/1000000000000 : ℝ) (495941093981/500000000000 : ℝ) (495924484151/500000000000 : ℝ) (991848968303/1000000000000 : ℝ) (991865578131/1000000000000 : ℝ) (991865578133/1000000000000 : ℝ) (123983197249/125000000000 : ℝ) (495932788997/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4291/32768 : ℝ)) 2 (991865578131/1000000000000 : ℝ) (991865578133/1000000000000 : ℝ) (123983197249/125000000000 : ℝ) (495932788997/500000000000 : ℝ) (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ) (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4291/32768 : ℝ)) 3 (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ) (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ) (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ) (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4291/32768 : ℝ)) 4 (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ) (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ) (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ) (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4291/32768 : ℝ)) 5 (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ) (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ) (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ) (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4291/32768 : ℝ)) 6 (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ) (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ) (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ) (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4291/32768 : ℝ)) 7 (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ) (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ) (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ) (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4291/32768 : ℝ))) (179464906499/1000000000000 : ℝ) (35892981301/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4291/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179464906499/1000000000000 : ℝ) (35892981301/200000000000 : ℝ) (589732453249/1000000000000 : ℝ) (589732453253/1000000000000 : ℝ) (105908246403/250000000000 : ℝ) (21181649281/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4291/32768 : ℝ))) 1 (589732453249/1000000000000 : ℝ) (589732453253/1000000000000 : ℝ) (105908246403/250000000000 : ℝ) (21181649281/50000000000 : ℝ) (50668271943/100000000000 : ℝ) (506682719437/1000000000000 : ℝ) (499830091013/1000000000000 : ℝ) (24991504551/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4291/32768 : ℝ))) 2 (50668271943/100000000000 : ℝ) (506682719437/1000000000000 : ℝ) (499830091013/1000000000000 : ℝ) (24991504551/50000000000 : ℝ) (503256405221/1000000000000 : ℝ) (503256405229/1000000000000 : ℝ) (25162237071/50000000000 : ℝ) (125811185357/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4291/32768 : ℝ))) 3 (503256405221/1000000000000 : ℝ) (503256405229/1000000000000 : ℝ) (25162237071/50000000000 : ℝ) (125811185357/250000000000 : ℝ) (12581264333/25000000000 : ℝ) (503250573329/1000000000000 : ℝ) (251625286643/500000000000 : ℝ) (100650114659/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4291/32768 : ℝ))) 4 (12581264333/25000000000 : ℝ) (503250573329/1000000000000 : ℝ) (251625286643/500000000000 : ℝ) (100650114659/200000000000 : ℝ) (503250573303/1000000000000 : ℝ) (245727819/488281250 : ℝ) (251625286651/500000000000 : ℝ) (245727819/488281250 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4291/32768 : ℝ))) 5 (503250573303/1000000000000 : ℝ) (245727819/488281250 : ℝ) (251625286651/500000000000 : ℝ) (245727819/488281250 : ℝ) (251625286651/500000000000 : ℝ) (245727819/488281250 : ℝ) (251625286651/500000000000 : ℝ) (245727819/488281250 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4291/32768 : ℝ))) 6 (251625286651/500000000000 : ℝ) (245727819/488281250 : ℝ) (251625286651/500000000000 : ℝ) (245727819/488281250 : ℝ) (251625286651/500000000000 : ℝ) (245727819/488281250 : ℝ) (251625286651/500000000000 : ℝ) (245727819/488281250 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4291/32768 : ℝ))) 7 (251625286651/500000000000 : ℝ) (245727819/488281250 : ℝ) (251625286651/500000000000 : ℝ) (245727819/488281250 : ℝ) (251625286651/500000000000 : ℝ) (245727819/488281250 : ℝ) (251625286651/500000000000 : ℝ) (245727819/488281250 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4291/32768 : ℝ)) hmem 8 (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ) (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4291/32768 : ℝ))) hcmem 8 (251625286651/500000000000 : ℝ) (245727819/488281250 : ℝ) (251625286651/500000000000 : ℝ) (245727819/488281250 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4291/32768 : ℝ)) (991865578061/1000000000000 : ℝ) (61991598629/62500000000 : ℝ) (251625286651/500000000000 : ℝ) (245727819/488281250 : ℝ) (12452924719/15625000000 : ℝ) (159397436407/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1571_exp_lower
  have heNumeric : (2054900830749/1000000000000 : ℝ)/4 ≤ Real.exp (-532853417503/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900830749/1000000000000 : ℝ)/4 ≤ Real.exp ((2145/16384 : ℝ)-(159397436407/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2145/16384 : ℝ) (4291/32768 : ℝ) (159397436407/200000000000 : ℝ) (2054900830749/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1572; no trusted numerical premise.
theorem cover8_leaf1572_exp_radius : (249488876936070837/250000000000000000 : ℝ) ≤ Real.exp ((-1073/65536 : ℝ)/8) ∧ Real.exp ((-1073/65536 : ℝ)/8) ≤ (997955507744283349/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1073/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1572_exp_lower : (460056734329503319/500000000000000000 : ℝ) ≤ Real.exp ((-5328529986901/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328529986901/8000000000000 : ℝ)/8) ≤ (920113468659006639/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328529986901/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1572_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901906523/1000000000000 : ℝ) ≤ 4*Real.exp (4291/32768 : ℝ)*Real.exp (-mu (radius 8 (1073/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901906523/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1073/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1572_exp_radius
  have hrNumeric : (491880311583/500000000000 : ℝ) ≤ Real.exp (-1073/65536 : ℝ) ∧ Real.exp (-1073/65536 : ℝ) ≤ (983760623167/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491880311583/500000000000 : ℝ) ≤ (radius 8 (1073/8192 : ℝ)) ∧ (radius 8 (1073/8192 : ℝ)) ≤ (983760623167/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1073/8192 : ℝ)) (491880311583/500000000000 : ℝ) (983760623167/1000000000000 : ℝ) (44871369147/250000000000 : ℝ) (89742738297/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1073/8192 : ℝ)) (491880311583/500000000000 : ℝ) (983760623167/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1073/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491880311583/500000000000 : ℝ) (983760623167/1000000000000 : ℝ) (991880311583/1000000000000 : ℝ) (30996259737/31250000000 : ℝ) (495923538251/500000000000 : ℝ) (991847076503/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1073/8192 : ℝ)) 1 (991880311583/1000000000000 : ℝ) (30996259737/31250000000 : ℝ) (495923538251/500000000000 : ℝ) (991847076503/1000000000000 : ℝ) (495931847021/500000000000 : ℝ) (247965923511/250000000000 : ℝ) (991863693903/1000000000000 : ℝ) (198372738781/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1073/8192 : ℝ)) 2 (495931847021/500000000000 : ℝ) (247965923511/250000000000 : ℝ) (991863693903/1000000000000 : ℝ) (198372738781/200000000000 : ℝ) (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ) (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1073/8192 : ℝ)) 3 (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ) (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ) (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ) (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1073/8192 : ℝ)) 4 (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ) (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ) (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ) (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1073/8192 : ℝ)) 5 (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ) (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ) (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ) (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1073/8192 : ℝ)) 6 (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ) (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ) (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ) (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1073/8192 : ℝ)) 7 (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ) (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ) (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ) (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1073/8192 : ℝ))) (44871369147/250000000000 : ℝ) (89742738297/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1073/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44871369147/250000000000 : ℝ) (89742738297/500000000000 : ℝ) (294871369147/500000000000 : ℝ) (589742738297/1000000000000 : ℝ) (52957157889/125000000000 : ℝ) (5295715789/12500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1073/8192 : ℝ))) 1 (294871369147/500000000000 : ℝ) (589742738297/1000000000000 : ℝ) (52957157889/125000000000 : ℝ) (5295715789/12500000000 : ℝ) (506700000703/1000000000000 : ℝ) (506700000709/1000000000000 : ℝ) (19993950863/40000000000 : ℝ) (249924385791/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1073/8192 : ℝ))) 2 (506700000703/1000000000000 : ℝ) (506700000709/1000000000000 : ℝ) (19993950863/40000000000 : ℝ) (249924385791/500000000000 : ℝ) (503274386139/1000000000000 : ℝ) (251637193073/500000000000 : ℝ) (503262727517/1000000000000 : ℝ) (20130509101/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1073/8192 : ℝ))) 3 (503274386139/1000000000000 : ℝ) (251637193073/500000000000 : ℝ) (503262727517/1000000000000 : ℝ) (20130509101/40000000000 : ℝ) (125817139207/250000000000 : ℝ) (125817139209/250000000000 : ℝ) (251634278397/500000000000 : ℝ) (251634278401/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1073/8192 : ℝ))) 4 (125817139207/250000000000 : ℝ) (125817139209/250000000000 : ℝ) (251634278397/500000000000 : ℝ) (251634278401/500000000000 : ℝ) (503268556811/1000000000000 : ℝ) (503268556819/1000000000000 : ℝ) (50326855681/100000000000 : ℝ) (503268556819/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1073/8192 : ℝ))) 5 (503268556811/1000000000000 : ℝ) (503268556819/1000000000000 : ℝ) (50326855681/100000000000 : ℝ) (503268556819/1000000000000 : ℝ) (50326855681/100000000000 : ℝ) (503268556819/1000000000000 : ℝ) (50326855681/100000000000 : ℝ) (503268556819/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1073/8192 : ℝ))) 6 (50326855681/100000000000 : ℝ) (503268556819/1000000000000 : ℝ) (50326855681/100000000000 : ℝ) (503268556819/1000000000000 : ℝ) (50326855681/100000000000 : ℝ) (503268556819/1000000000000 : ℝ) (50326855681/100000000000 : ℝ) (503268556819/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1073/8192 : ℝ))) 7 (50326855681/100000000000 : ℝ) (503268556819/1000000000000 : ℝ) (50326855681/100000000000 : ℝ) (503268556819/1000000000000 : ℝ) (50326855681/100000000000 : ℝ) (503268556819/1000000000000 : ℝ) (50326855681/100000000000 : ℝ) (503268556819/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1073/8192 : ℝ)) hmem 8 (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ) (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1073/8192 : ℝ))) hcmem 8 (50326855681/100000000000 : ℝ) (503268556819/1000000000000 : ℝ) (50326855681/100000000000 : ℝ) (503268556819/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1073/8192 : ℝ)) (247965923493/250000000000 : ℝ) (39674547759/40000000000 : ℝ) (50326855681/100000000000 : ℝ) (503268556819/1000000000000 : ℝ) (9962714701/12500000000 : ℝ) (797017176097/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1572_exp_lower
  have heNumeric : (2054901906523/1000000000000 : ℝ)/4 ≤ Real.exp (-5328529986901/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901906523/1000000000000 : ℝ)/4 ≤ Real.exp ((4291/32768 : ℝ)-(797017176097/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4291/32768 : ℝ) (1073/8192 : ℝ) (797017176097/1000000000000 : ℝ) (2054901906523/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1573; no trusted numerical premise.
theorem cover8_leaf1573_exp_radius : (997955031882128477/1000000000000000000 : ℝ) ≤ Real.exp ((-4293/262144 : ℝ)/8) ∧ Real.exp ((-4293/262144 : ℝ)/8) ≤ (498977515941064239/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4293/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1573_exp_lower : (920113529414460399/1000000000000000000 : ℝ) ≤ Real.exp ((-1332131440239/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332131440239/2000000000000 : ℝ)/8) ≤ (2300283823536151/2500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332131440239/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1573_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902992011/1000000000000 : ℝ) ≤ 4*Real.exp (1073/8192 : ℝ)*Real.exp (-mu (radius 8 (4293/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902992011/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4293/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1573_exp_radius
  have hrNumeric : (122969608803/125000000000 : ℝ) ≤ Real.exp (-4293/262144 : ℝ) ∧ Real.exp (-4293/262144 : ℝ) ≤ (39350274817/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122969608803/125000000000 : ℝ) ≤ (radius 8 (4293/32768 : ℝ)) ∧ (radius 8 (4293/32768 : ℝ)) ≤ (39350274817/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4293/32768 : ℝ)) (122969608803/125000000000 : ℝ) (39350274817/40000000000 : ℝ) (44876511041/250000000000 : ℝ) (179506044171/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4293/32768 : ℝ)) (122969608803/125000000000 : ℝ) (39350274817/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4293/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122969608803/125000000000 : ℝ) (39350274817/40000000000 : ℝ) (247969608803/250000000000 : ℝ) (991878435213/1000000000000 : ℝ) (198369036941/200000000000 : ℝ) (991845184707/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4293/32768 : ℝ)) 1 (247969608803/250000000000 : ℝ) (991878435213/1000000000000 : ℝ) (198369036941/200000000000 : ℝ) (991845184707/1000000000000 : ℝ) (495930904979/500000000000 : ℝ) (24796545249/25000000000 : ℝ) (991861809819/1000000000000 : ℝ) (991861809821/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4293/32768 : ℝ)) 2 (495930904979/500000000000 : ℝ) (24796545249/25000000000 : ℝ) (991861809819/1000000000000 : ℝ) (991861809821/1000000000000 : ℝ) (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ) (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4293/32768 : ℝ)) 3 (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ) (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ) (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ) (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4293/32768 : ℝ)) 4 (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ) (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ) (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ) (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4293/32768 : ℝ)) 5 (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ) (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ) (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ) (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4293/32768 : ℝ)) 6 (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ) (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ) (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ) (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4293/32768 : ℝ)) 7 (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ) (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ) (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ) (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4293/32768 : ℝ))) (44876511041/250000000000 : ℝ) (179506044171/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4293/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44876511041/250000000000 : ℝ) (179506044171/1000000000000 : ℝ) (294876511041/500000000000 : ℝ) (294876511043/500000000000 : ℝ) (84736307251/200000000000 : ℝ) (52960192033/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4293/32768 : ℝ))) 1 (294876511041/500000000000 : ℝ) (294876511043/500000000000 : ℝ) (84736307251/200000000000 : ℝ) (52960192033/125000000000 : ℝ) (7917457487/15625000000 : ℝ) (20268691167/40000000000 : ℝ) (124966862209/250000000000 : ℝ) (124966862211/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4293/32768 : ℝ))) 2 (7917457487/15625000000 : ℝ) (20268691167/40000000000 : ℝ) (124966862209/250000000000 : ℝ) (124966862211/250000000000 : ℝ) (251646182001/500000000000 : ℝ) (50329236401/100000000000 : ℝ) (503280710557/1000000000000 : ℝ) (100656142113/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4293/32768 : ℝ))) 3 (251646182001/500000000000 : ℝ) (50329236401/100000000000 : ℝ) (503280710557/1000000000000 : ℝ) (100656142113/200000000000 : ℝ) (503286537279/1000000000000 : ℝ) (62910817161/125000000000 : ℝ) (100657307449/200000000000 : ℝ) (251643268627/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4293/32768 : ℝ))) 4 (503286537279/1000000000000 : ℝ) (62910817161/125000000000 : ℝ) (100657307449/200000000000 : ℝ) (251643268627/500000000000 : ℝ) (251643268631/500000000000 : ℝ) (503286537271/1000000000000 : ℝ) (503286537261/1000000000000 : ℝ) (503286537271/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4293/32768 : ℝ))) 5 (251643268631/500000000000 : ℝ) (503286537271/1000000000000 : ℝ) (503286537261/1000000000000 : ℝ) (503286537271/1000000000000 : ℝ) (503286537261/1000000000000 : ℝ) (503286537271/1000000000000 : ℝ) (503286537261/1000000000000 : ℝ) (503286537271/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4293/32768 : ℝ))) 6 (503286537261/1000000000000 : ℝ) (503286537271/1000000000000 : ℝ) (503286537261/1000000000000 : ℝ) (503286537271/1000000000000 : ℝ) (503286537261/1000000000000 : ℝ) (503286537271/1000000000000 : ℝ) (503286537261/1000000000000 : ℝ) (503286537271/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4293/32768 : ℝ))) 7 (503286537261/1000000000000 : ℝ) (503286537271/1000000000000 : ℝ) (503286537261/1000000000000 : ℝ) (503286537271/1000000000000 : ℝ) (503286537261/1000000000000 : ℝ) (503286537271/1000000000000 : ℝ) (503286537261/1000000000000 : ℝ) (503286537271/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4293/32768 : ℝ)) hmem 8 (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ) (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4293/32768 : ℝ))) hcmem 8 (503286537261/1000000000000 : ℝ) (503286537271/1000000000000 : ℝ) (503286537261/1000000000000 : ℝ) (503286537271/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4293/32768 : ℝ)) (30995681559/31250000000 : ℝ) (991861809891/1000000000000 : ℝ) (503286537261/1000000000000 : ℝ) (503286537271/1000000000000 : ℝ) (199261791353/250000000000 : ℝ) (99630895679/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1573_exp_lower
  have heNumeric : (2054902992011/1000000000000 : ℝ)/4 ≤ Real.exp (-1332131440239/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902992011/1000000000000 : ℝ)/4 ≤ Real.exp ((1073/8192 : ℝ)-(99630895679/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1073/8192 : ℝ) (4293/32768 : ℝ) (99630895679/125000000000 : ℝ) (2054902992011/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1574; no trusted numerical premise.
theorem cover8_leaf1574_exp_radius : (498977278010100257/500000000000000000 : ℝ) ≤ Real.exp ((-2147/131072 : ℝ)/8) ∧ Real.exp ((-2147/131072 : ℝ)/8) ≤ (199590911204040103/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2147/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1574_exp_lower : (920113590714510403/1000000000000000000 : ℝ) ≤ Real.exp ((-5328521497131/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328521497131/8000000000000 : ℝ)/8) ≤ (230028397678627601/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328521497131/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1574_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490408723/100000000000 : ℝ) ≤ 4*Real.exp (4293/32768 : ℝ)*Real.exp (-mu (radius 8 (2147/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (205490408723/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2147/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1574_exp_radius
  have hrNumeric : (983753117697/1000000000000 : ℝ) ≤ Real.exp (-2147/131072 : ℝ) ∧ Real.exp (-2147/131072 : ℝ) ≤ (491876558849/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983753117697/1000000000000 : ℝ) ≤ (radius 8 (2147/16384 : ℝ)) ∧ (radius 8 (2147/16384 : ℝ)) ≤ (491876558849/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2147/16384 : ℝ)) (983753117697/1000000000000 : ℝ) (491876558849/500000000000 : ℝ) (179526609223/1000000000000 : ℝ) (17952660923/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2147/16384 : ℝ)) (983753117697/1000000000000 : ℝ) (491876558849/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2147/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983753117697/1000000000000 : ℝ) (491876558849/500000000000 : ℝ) (242157363/244140625 : ℝ) (991876558849/1000000000000 : ℝ) (991843292913/1000000000000 : ℝ) (495921646457/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2147/16384 : ℝ)) 1 (242157363/244140625 : ℝ) (991876558849/1000000000000 : ℝ) (991843292913/1000000000000 : ℝ) (495921646457/500000000000 : ℝ) (24796498147/25000000000 : ℝ) (495929962941/500000000000 : ℝ) (991859925741/1000000000000 : ℝ) (991859925743/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2147/16384 : ℝ)) 2 (24796498147/25000000000 : ℝ) (495929962941/500000000000 : ℝ) (991859925741/1000000000000 : ℝ) (991859925743/1000000000000 : ℝ) (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ) (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2147/16384 : ℝ)) 3 (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ) (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ) (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ) (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2147/16384 : ℝ)) 4 (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ) (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ) (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ) (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2147/16384 : ℝ)) 5 (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ) (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ) (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ) (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2147/16384 : ℝ)) 6 (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ) (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ) (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ) (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2147/16384 : ℝ)) 7 (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ) (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ) (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ) (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2147/16384 : ℝ))) (179526609223/1000000000000 : ℝ) (17952660923/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2147/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179526609223/1000000000000 : ℝ) (17952660923/100000000000 : ℝ) (589763304611/1000000000000 : ℝ) (117952660923/200000000000 : ℝ) (211852902519/500000000000 : ℝ) (423705805047/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2147/16384 : ℝ))) 1 (589763304611/1000000000000 : ℝ) (117952660923/200000000000 : ℝ) (211852902519/500000000000 : ℝ) (423705805047/1000000000000 : ℝ) (63341819353/125000000000 : ℝ) (506734554831/1000000000000 : ℝ) (249943061397/500000000000 : ℝ) (249943061401/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2147/16384 : ℝ))) 2 (63341819353/125000000000 : ℝ) (506734554831/1000000000000 : ℝ) (249943061397/500000000000 : ℝ) (249943061401/500000000000 : ℝ) (503310338809/1000000000000 : ℝ) (503310338817/1000000000000 : ℝ) (503298690537/1000000000000 : ℝ) (100659738109/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2147/16384 : ℝ))) 3 (503310338809/1000000000000 : ℝ) (503310338817/1000000000000 : ℝ) (503298690537/1000000000000 : ℝ) (100659738109/200000000000 : ℝ) (503304514673/1000000000000 : ℝ) (503304514681/1000000000000 : ℝ) (503304514639/1000000000000 : ℝ) (62913064331/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2147/16384 : ℝ))) 4 (503304514673/1000000000000 : ℝ) (503304514681/1000000000000 : ℝ) (503304514639/1000000000000 : ℝ) (62913064331/125000000000 : ℝ) (15728266083/31250000000 : ℝ) (100660902933/200000000000 : ℝ) (100660902931/200000000000 : ℝ) (100660902933/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2147/16384 : ℝ))) 5 (15728266083/31250000000 : ℝ) (100660902933/200000000000 : ℝ) (100660902931/200000000000 : ℝ) (100660902933/200000000000 : ℝ) (100660902931/200000000000 : ℝ) (100660902933/200000000000 : ℝ) (100660902931/200000000000 : ℝ) (100660902933/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2147/16384 : ℝ))) 6 (100660902931/200000000000 : ℝ) (100660902933/200000000000 : ℝ) (100660902931/200000000000 : ℝ) (100660902933/200000000000 : ℝ) (100660902931/200000000000 : ℝ) (100660902933/200000000000 : ℝ) (100660902931/200000000000 : ℝ) (100660902933/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2147/16384 : ℝ))) 7 (100660902931/200000000000 : ℝ) (100660902933/200000000000 : ℝ) (100660902931/200000000000 : ℝ) (100660902933/200000000000 : ℝ) (100660902931/200000000000 : ℝ) (100660902933/200000000000 : ℝ) (100660902931/200000000000 : ℝ) (100660902933/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2147/16384 : ℝ)) hmem 8 (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ) (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2147/16384 : ℝ))) hcmem 8 (100660902931/200000000000 : ℝ) (100660902933/200000000000 : ℝ) (100660902931/200000000000 : ℝ) (100660902933/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2147/16384 : ℝ)) (99185992581/100000000000 : ℝ) (991859925813/1000000000000 : ℝ) (100660902931/200000000000 : ℝ) (100660902933/200000000000 : ℝ) (797077150013/1000000000000 : ℝ) (49817321877/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1574_exp_lower
  have heNumeric : (205490408723/100000000000 : ℝ)/4 ≤ Real.exp (-5328521497131/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490408723/100000000000 : ℝ)/4 ≤ Real.exp ((4293/32768 : ℝ)-(49817321877/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4293/32768 : ℝ) (2147/16384 : ℝ) (49817321877/62500000000 : ℝ) (205490408723/100000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1550_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1550_certificate
#check SmaleRate.Proofs.cover8_leaf1551_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1551_certificate
#check SmaleRate.Proofs.cover8_leaf1552_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1552_certificate
#check SmaleRate.Proofs.cover8_leaf1553_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1553_certificate
#check SmaleRate.Proofs.cover8_leaf1554_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1554_certificate
#check SmaleRate.Proofs.cover8_leaf1555_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1555_certificate
#check SmaleRate.Proofs.cover8_leaf1556_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1556_certificate
#check SmaleRate.Proofs.cover8_leaf1557_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1557_certificate
#check SmaleRate.Proofs.cover8_leaf1558_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1558_certificate
#check SmaleRate.Proofs.cover8_leaf1559_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1559_certificate
#check SmaleRate.Proofs.cover8_leaf1560_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1560_certificate
#check SmaleRate.Proofs.cover8_leaf1561_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1561_certificate
#check SmaleRate.Proofs.cover8_leaf1562_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1562_certificate
#check SmaleRate.Proofs.cover8_leaf1563_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1563_certificate
#check SmaleRate.Proofs.cover8_leaf1564_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1564_certificate
#check SmaleRate.Proofs.cover8_leaf1565_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1565_certificate
#check SmaleRate.Proofs.cover8_leaf1566_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1566_certificate
#check SmaleRate.Proofs.cover8_leaf1567_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1567_certificate
#check SmaleRate.Proofs.cover8_leaf1568_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1568_certificate
#check SmaleRate.Proofs.cover8_leaf1569_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1569_certificate
#check SmaleRate.Proofs.cover8_leaf1570_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1570_certificate
#check SmaleRate.Proofs.cover8_leaf1571_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1571_certificate
#check SmaleRate.Proofs.cover8_leaf1572_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1572_certificate
#check SmaleRate.Proofs.cover8_leaf1573_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1573_certificate
#check SmaleRate.Proofs.cover8_leaf1574_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1574_certificate
