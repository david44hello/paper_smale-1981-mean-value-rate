/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1200; no trusted numerical premise.
theorem cover8_leaf1200_exp_radius : (997997116818776983/1000000000000000000 : ℝ) ≤ Real.exp ((-67273/4194304 : ℝ)/8) ∧ Real.exp ((-67273/4194304 : ℝ)/8) ≤ (124749639602347123/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67273/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1200_exp_lower : (92011357576656797/100000000000000000 : ℝ) ≤ Real.exp ((-10657045073719/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657045073719/16000000000000 : ℝ)/8) ≤ (920113575766567971/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657045073719/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1200_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451910081/500000000000 : ℝ) ≤ 4*Real.exp (8409/65536 : ℝ)*Real.exp (-mu (radius 8 (67273/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451910081/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67273/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1200_exp_radius
  have hrNumeric : (984088808883/1000000000000 : ℝ) ≤ Real.exp (-67273/4194304 : ℝ) ∧ Real.exp (-67273/4194304 : ℝ) ≤ (246022202221/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984088808883/1000000000000 : ℝ) ≤ (radius 8 (67273/524288 : ℝ)) ∧ (radius 8 (67273/524288 : ℝ)) ≤ (246022202221/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67273/524288 : ℝ)) (984088808883/1000000000000 : ℝ) (246022202221/250000000000 : ℝ) (22209660141/125000000000 : ℝ) (35535456227/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67273/524288 : ℝ)) (984088808883/1000000000000 : ℝ) (246022202221/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67273/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984088808883/1000000000000 : ℝ) (246022202221/250000000000 : ℝ) (992044404441/1000000000000 : ℝ) (496022202221/500000000000 : ℝ) (496006252199/500000000000 : ℝ) (2480031261/2500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67273/524288 : ℝ)) 1 (992044404441/1000000000000 : ℝ) (496022202221/500000000000 : ℝ) (496006252199/500000000000 : ℝ) (2480031261/2500000000 : ℝ) (992028454419/1000000000000 : ℝ) (992028454421/1000000000000 : ℝ) (992028454291/1000000000000 : ℝ) (992028454293/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67273/524288 : ℝ)) 2 (992028454419/1000000000000 : ℝ) (992028454421/1000000000000 : ℝ) (992028454291/1000000000000 : ℝ) (992028454293/1000000000000 : ℝ) (198405690871/200000000000 : ℝ) (992028454357/1000000000000 : ℝ) (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67273/524288 : ℝ)) 3 (198405690871/200000000000 : ℝ) (992028454357/1000000000000 : ℝ) (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ) (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ) (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67273/524288 : ℝ)) 4 (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ) (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ) (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ) (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67273/524288 : ℝ)) 5 (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ) (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ) (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ) (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67273/524288 : ℝ)) 6 (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ) (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ) (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ) (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67273/524288 : ℝ)) 7 (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ) (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ) (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ) (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67273/524288 : ℝ))) (22209660141/125000000000 : ℝ) (35535456227/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67273/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22209660141/125000000000 : ℝ) (35535456227/200000000000 : ℝ) (147209660141/250000000000 : ℝ) (73604830071/125000000000 : ℝ) (210758915071/500000000000 : ℝ) (421517830151/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67273/524288 : ℝ))) 1 (147209660141/250000000000 : ℝ) (73604830071/125000000000 : ℝ) (210758915071/500000000000 : ℝ) (421517830151/1000000000000 : ℝ) (505178235353/1000000000000 : ℝ) (3157363971/6250000000 : ℝ) (124550688997/250000000000 : ℝ) (124550688999/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67273/524288 : ℝ))) 2 (505178235353/1000000000000 : ℝ) (3157363971/6250000000 : ℝ) (124550688997/250000000000 : ℝ) (124550688999/250000000000 : ℝ) (50169049567/100000000000 : ℝ) (250845247839/500000000000 : ℝ) (62709796523/125000000000 : ℝ) (501678372193/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67273/524288 : ℝ))) 3 (50169049567/100000000000 : ℝ) (250845247839/500000000000 : ℝ) (62709796523/125000000000 : ℝ) (501678372193/1000000000000 : ℝ) (501684433927/1000000000000 : ℝ) (31355277121/62500000000 : ℝ) (50168443389/100000000000 : ℝ) (501684433899/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67273/524288 : ℝ))) 4 (501684433927/1000000000000 : ℝ) (31355277121/62500000000 : ℝ) (50168443389/100000000000 : ℝ) (501684433899/1000000000000 : ℝ) (125421108477/250000000000 : ℝ) (250842216959/500000000000 : ℝ) (125421108477/250000000000 : ℝ) (250842216959/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67273/524288 : ℝ))) 5 (125421108477/250000000000 : ℝ) (250842216959/500000000000 : ℝ) (125421108477/250000000000 : ℝ) (250842216959/500000000000 : ℝ) (125421108477/250000000000 : ℝ) (250842216959/500000000000 : ℝ) (125421108477/250000000000 : ℝ) (250842216959/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67273/524288 : ℝ))) 6 (125421108477/250000000000 : ℝ) (250842216959/500000000000 : ℝ) (125421108477/250000000000 : ℝ) (250842216959/500000000000 : ℝ) (125421108477/250000000000 : ℝ) (250842216959/500000000000 : ℝ) (125421108477/250000000000 : ℝ) (250842216959/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67273/524288 : ℝ))) 7 (125421108477/250000000000 : ℝ) (250842216959/500000000000 : ℝ) (125421108477/250000000000 : ℝ) (250842216959/500000000000 : ℝ) (125421108477/250000000000 : ℝ) (250842216959/500000000000 : ℝ) (125421108477/250000000000 : ℝ) (250842216959/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67273/524288 : ℝ)) hmem 8 (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ) (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67273/524288 : ℝ))) hcmem 8 (125421108477/250000000000 : ℝ) (250842216959/500000000000 : ℝ) (125421108477/250000000000 : ℝ) (250842216959/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67273/524288 : ℝ)) (496014227177/500000000000 : ℝ) (992028454357/1000000000000 : ℝ) (125421108477/250000000000 : ℝ) (250842216959/500000000000 : ℝ) (158875294863/200000000000 : ℝ) (397188237167/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1200_exp_lower
  have heNumeric : (1027451910081/500000000000 : ℝ)/4 ≤ Real.exp (-10657045073719/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451910081/500000000000 : ℝ)/4 ≤ Real.exp ((8409/65536 : ℝ)-(397188237167/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8409/65536 : ℝ) (67273/524288 : ℝ) (397188237167/500000000000 : ℝ) (1027451910081/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1201; no trusted numerical premise.
theorem cover8_leaf1201_exp_radius : (997997087076145609/1000000000000000000 : ℝ) ≤ Real.exp ((-33637/2097152 : ℝ)/8) ∧ Real.exp ((-33637/2097152 : ℝ)/8) ≤ (99799708707614561/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33637/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1201_exp_lower : (920113576520443799/1000000000000000000 : ℝ) ≤ Real.exp ((-85256359750759/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256359750759/128000000000000 : ℝ)/8) ≤ (4600567882602219/5000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256359750759/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1201_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903833631/1000000000000 : ℝ) ≤ 4*Real.exp (67273/524288 : ℝ)*Real.exp (-mu (radius 8 (33637/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903833631/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33637/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1201_exp_radius
  have hrNumeric : (492044287129/500000000000 : ℝ) ≤ Real.exp (-33637/2097152 : ℝ) ∧ Real.exp (-33637/2097152 : ℝ) ≤ (984088574259/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492044287129/500000000000 : ℝ) ≤ (radius 8 (33637/262144 : ℝ)) ∧ (radius 8 (33637/262144 : ℝ)) ≤ (984088574259/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33637/262144 : ℝ)) (492044287129/500000000000 : ℝ) (984088574259/1000000000000 : ℝ) (11104911289/62500000000 : ℝ) (177678580631/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33637/262144 : ℝ)) (492044287129/500000000000 : ℝ) (984088574259/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33637/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492044287129/500000000000 : ℝ) (984088574259/1000000000000 : ℝ) (992044287129/1000000000000 : ℝ) (99204428713/100000000000 : ℝ) (992012386141/1000000000000 : ℝ) (496006193071/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33637/262144 : ℝ)) 1 (992044287129/1000000000000 : ℝ) (99204428713/100000000000 : ℝ) (992012386141/1000000000000 : ℝ) (496006193071/500000000000 : ℝ) (198405667327/200000000000 : ℝ) (248007084159/250000000000 : ℝ) (496014168253/500000000000 : ℝ) (248007084127/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33637/262144 : ℝ)) 2 (198405667327/200000000000 : ℝ) (248007084159/250000000000 : ℝ) (496014168253/500000000000 : ℝ) (248007084127/250000000000 : ℝ) (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ) (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33637/262144 : ℝ)) 3 (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ) (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ) (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ) (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33637/262144 : ℝ)) 4 (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ) (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ) (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ) (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33637/262144 : ℝ)) 5 (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ) (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ) (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ) (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33637/262144 : ℝ)) 6 (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ) (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ) (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ) (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33637/262144 : ℝ)) 7 (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ) (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ) (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ) (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33637/262144 : ℝ))) (11104911289/62500000000 : ℝ) (177678580631/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33637/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11104911289/62500000000 : ℝ) (177678580631/1000000000000 : ℝ) (73604911289/125000000000 : ℝ) (147209822579/250000000000 : ℝ) (105379842897/250000000000 : ℝ) (421519371597/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33637/262144 : ℝ))) 1 (73604911289/125000000000 : ℝ) (147209822579/250000000000 : ℝ) (105379842897/250000000000 : ℝ) (421519371597/1000000000000 : ℝ) (10103586619/20000000000 : ℝ) (505179330957/1000000000000 : ℝ) (498203941793/1000000000000 : ℝ) (498203941801/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33637/262144 : ℝ))) 2 (10103586619/20000000000 : ℝ) (505179330957/1000000000000 : ℝ) (498203941793/1000000000000 : ℝ) (498203941801/1000000000000 : ℝ) (501691636371/1000000000000 : ℝ) (501691636379/1000000000000 : ℝ) (250839756613/500000000000 : ℝ) (100335902647/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33637/262144 : ℝ))) 3 (501691636371/1000000000000 : ℝ) (501691636379/1000000000000 : ℝ) (250839756613/500000000000 : ℝ) (100335902647/200000000000 : ℝ) (250842787399/500000000000 : ℝ) (501685574807/1000000000000 : ℝ) (501685574761/1000000000000 : ℝ) (501685574771/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33637/262144 : ℝ))) 4 (250842787399/500000000000 : ℝ) (501685574807/1000000000000 : ℝ) (501685574761/1000000000000 : ℝ) (501685574771/1000000000000 : ℝ) (501685574779/1000000000000 : ℝ) (501685574789/1000000000000 : ℝ) (501685574779/1000000000000 : ℝ) (501685574789/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33637/262144 : ℝ))) 5 (501685574779/1000000000000 : ℝ) (501685574789/1000000000000 : ℝ) (501685574779/1000000000000 : ℝ) (501685574789/1000000000000 : ℝ) (501685574779/1000000000000 : ℝ) (501685574789/1000000000000 : ℝ) (501685574779/1000000000000 : ℝ) (501685574789/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33637/262144 : ℝ))) 6 (501685574779/1000000000000 : ℝ) (501685574789/1000000000000 : ℝ) (501685574779/1000000000000 : ℝ) (501685574789/1000000000000 : ℝ) (501685574779/1000000000000 : ℝ) (501685574789/1000000000000 : ℝ) (501685574779/1000000000000 : ℝ) (501685574789/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33637/262144 : ℝ))) 7 (501685574779/1000000000000 : ℝ) (501685574789/1000000000000 : ℝ) (501685574779/1000000000000 : ℝ) (501685574789/1000000000000 : ℝ) (501685574779/1000000000000 : ℝ) (501685574789/1000000000000 : ℝ) (501685574779/1000000000000 : ℝ) (501685574789/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33637/262144 : ℝ)) hmem 8 (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ) (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33637/262144 : ℝ))) hcmem 8 (501685574779/1000000000000 : ℝ) (501685574789/1000000000000 : ℝ) (501685574779/1000000000000 : ℝ) (501685574789/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33637/262144 : ℝ)) (99202833657/100000000000 : ℝ) (248007084143/250000000000 : ℝ) (501685574779/1000000000000 : ℝ) (501685574789/1000000000000 : ℝ) (794378375109/1000000000000 : ℝ) (99297296891/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1201_exp_lower
  have heNumeric : (2054903833631/1000000000000 : ℝ)/4 ≤ Real.exp (-85256359750759/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903833631/1000000000000 : ℝ)/4 ≤ Real.exp ((67273/524288 : ℝ)-(99297296891/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67273/524288 : ℝ) (33637/262144 : ℝ) (99297296891/125000000000 : ℝ) (2054903833631/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1202; no trusted numerical premise.
theorem cover8_leaf1202_exp_radius : (997997057333515121/1000000000000000000 : ℝ) ≤ Real.exp ((-67275/4194304 : ℝ)/8) ∧ Real.exp ((-67275/4194304 : ℝ)/8) ≤ (498998528666757561/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67275/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1202_exp_lower : (920113577276274871/1000000000000000000 : ℝ) ≤ Real.exp ((-8525635890959/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525635890959/12800000000000 : ℝ)/8) ≤ (115014197159534359/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525635890959/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1202_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (64215745223/31250000000 : ℝ) ≤ 4*Real.exp (33637/262144 : ℝ)*Real.exp (-mu (radius 8 (67275/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (64215745223/31250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67275/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1202_exp_radius
  have hrNumeric : (984088339633/1000000000000 : ℝ) ≤ Real.exp (-67275/4194304 : ℝ) ∧ Real.exp (-67275/4194304 : ℝ) ≤ (492044169817/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984088339633/1000000000000 : ℝ) ≤ (radius 8 (67275/524288 : ℝ)) ∧ (radius 8 (67275/524288 : ℝ)) ≤ (492044169817/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67275/524288 : ℝ)) (984088339633/1000000000000 : ℝ) (492044169817/500000000000 : ℝ) (177679880111/1000000000000 : ℝ) (177679880117/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67275/524288 : ℝ)) (984088339633/1000000000000 : ℝ) (492044169817/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67275/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984088339633/1000000000000 : ℝ) (492044169817/500000000000 : ℝ) (124005521227/125000000000 : ℝ) (992044169817/1000000000000 : ℝ) (248003066971/250000000000 : ℝ) (198402453577/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67275/524288 : ℝ)) 1 (124005521227/125000000000 : ℝ) (992044169817/1000000000000 : ℝ) (248003066971/250000000000 : ℝ) (198402453577/200000000000 : ℝ) (19840564377/20000000000 : ℝ) (992028218851/1000000000000 : ℝ) (992028218721/1000000000000 : ℝ) (992028218723/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67275/524288 : ℝ)) 2 (19840564377/20000000000 : ℝ) (992028218851/1000000000000 : ℝ) (992028218721/1000000000000 : ℝ) (992028218723/1000000000000 : ℝ) (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ) (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67275/524288 : ℝ)) 3 (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ) (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ) (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ) (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67275/524288 : ℝ)) 4 (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ) (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ) (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ) (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67275/524288 : ℝ)) 5 (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ) (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ) (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ) (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67275/524288 : ℝ)) 6 (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ) (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ) (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ) (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67275/524288 : ℝ)) 7 (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ) (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ) (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ) (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67275/524288 : ℝ))) (177679880111/1000000000000 : ℝ) (177679880117/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67275/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177679880111/1000000000000 : ℝ) (177679880117/1000000000000 : ℝ) (117767988011/200000000000 : ℝ) (588839940059/1000000000000 : ℝ) (421520913017/1000000000000 : ℝ) (16860836521/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67275/524288 : ℝ))) 1 (117767988011/200000000000 : ℝ) (588839940059/1000000000000 : ℝ) (421520913017/1000000000000 : ℝ) (16860836521/40000000000 : ℝ) (63147553317/125000000000 : ℝ) (252590213271/500000000000 : ℝ) (99641025517/200000000000 : ℝ) (498205127593/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67275/524288 : ℝ))) 2 (63147553317/125000000000 : ℝ) (252590213271/500000000000 : ℝ) (99641025517/200000000000 : ℝ) (498205127593/1000000000000 : ℝ) (25084638853/50000000000 : ℝ) (125423194267/250000000000 : ℝ) (501680654257/1000000000000 : ℝ) (100336130853/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67275/524288 : ℝ))) 3 (25084638853/50000000000 : ℝ) (125423194267/250000000000 : ℝ) (501680654257/1000000000000 : ℝ) (100336130853/200000000000 : ℝ) (250843357829/500000000000 : ℝ) (501686715667/1000000000000 : ℝ) (501686715621/1000000000000 : ℝ) (50168671563/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67275/524288 : ℝ))) 4 (250843357829/500000000000 : ℝ) (501686715667/1000000000000 : ℝ) (501686715621/1000000000000 : ℝ) (50168671563/100000000000 : ℝ) (501686715639/1000000000000 : ℝ) (501686715649/1000000000000 : ℝ) (501686715639/1000000000000 : ℝ) (501686715649/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67275/524288 : ℝ))) 5 (501686715639/1000000000000 : ℝ) (501686715649/1000000000000 : ℝ) (501686715639/1000000000000 : ℝ) (501686715649/1000000000000 : ℝ) (501686715639/1000000000000 : ℝ) (501686715649/1000000000000 : ℝ) (501686715639/1000000000000 : ℝ) (501686715649/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67275/524288 : ℝ))) 6 (501686715639/1000000000000 : ℝ) (501686715649/1000000000000 : ℝ) (501686715639/1000000000000 : ℝ) (501686715649/1000000000000 : ℝ) (501686715639/1000000000000 : ℝ) (501686715649/1000000000000 : ℝ) (501686715639/1000000000000 : ℝ) (501686715649/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67275/524288 : ℝ))) 7 (501686715639/1000000000000 : ℝ) (501686715649/1000000000000 : ℝ) (501686715639/1000000000000 : ℝ) (501686715649/1000000000000 : ℝ) (501686715639/1000000000000 : ℝ) (501686715649/1000000000000 : ℝ) (501686715639/1000000000000 : ℝ) (501686715649/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67275/524288 : ℝ)) hmem 8 (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ) (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67275/524288 : ℝ))) hcmem 8 (501686715639/1000000000000 : ℝ) (501686715649/1000000000000 : ℝ) (501686715639/1000000000000 : ℝ) (501686715649/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67275/524288 : ℝ)) (198405643757/200000000000 : ℝ) (992028218787/1000000000000 : ℝ) (501686715639/1000000000000 : ℝ) (501686715649/1000000000000 : ℝ) (397190137943/500000000000 : ℝ) (158876055181/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1202_exp_lower
  have heNumeric : (64215745223/31250000000 : ℝ)/4 ≤ Real.exp (-8525635890959/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (64215745223/31250000000 : ℝ)/4 ≤ Real.exp ((33637/262144 : ℝ)-(158876055181/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33637/262144 : ℝ) (67275/524288 : ℝ) (158876055181/200000000000 : ℝ) (64215745223/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1203; no trusted numerical premise.
theorem cover8_leaf1203_exp_radius : (12474962844886069/12500000000000000 : ℝ) ≤ Real.exp ((-16819/1048576 : ℝ)/8) ∧ Real.exp ((-16819/1048576 : ℝ)/8) ≤ (997997027590885521/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16819/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1203_exp_lower : (920113578034406227/1000000000000000000 : ℝ) ≤ Real.exp ((-85256358065861/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256358065861/128000000000000 : ℝ)/8) ≤ (230028394508601557/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256358065861/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1203_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903860681/1000000000000 : ℝ) ≤ 4*Real.exp (67275/524288 : ℝ)*Real.exp (-mu (radius 8 (16819/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903860681/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16819/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1203_exp_radius
  have hrNumeric : (61505506563/62500000000 : ℝ) ≤ Real.exp (-16819/1048576 : ℝ) ∧ Real.exp (-16819/1048576 : ℝ) ≤ (984088105009/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61505506563/62500000000 : ℝ) ≤ (radius 8 (16819/131072 : ℝ)) ∧ (radius 8 (16819/131072 : ℝ)) ≤ (984088105009/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16819/131072 : ℝ)) (61505506563/62500000000 : ℝ) (984088105009/1000000000000 : ℝ) (44420294897/250000000000 : ℝ) (88840589797/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16819/131072 : ℝ)) (61505506563/62500000000 : ℝ) (984088105009/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16819/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61505506563/62500000000 : ℝ) (984088105009/1000000000000 : ℝ) (124005506563/125000000000 : ℝ) (198408810501/200000000000 : ℝ) (992012149627/1000000000000 : ℝ) (248003037407/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16819/131072 : ℝ)) 1 (124005506563/125000000000 : ℝ) (198408810501/200000000000 : ℝ) (992012149627/1000000000000 : ℝ) (248003037407/250000000000 : ℝ) (198405620213/200000000000 : ℝ) (992028101067/1000000000000 : ℝ) (992028100937/1000000000000 : ℝ) (992028100939/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16819/131072 : ℝ)) 2 (198405620213/200000000000 : ℝ) (992028101067/1000000000000 : ℝ) (992028100937/1000000000000 : ℝ) (992028100939/1000000000000 : ℝ) (992028101001/1000000000000 : ℝ) (992028101003/1000000000000 : ℝ) (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16819/131072 : ℝ)) 3 (992028101001/1000000000000 : ℝ) (992028101003/1000000000000 : ℝ) (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ) (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ) (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16819/131072 : ℝ)) 4 (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ) (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ) (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ) (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16819/131072 : ℝ)) 5 (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ) (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ) (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ) (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16819/131072 : ℝ)) 6 (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ) (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ) (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ) (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16819/131072 : ℝ)) 7 (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ) (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ) (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ) (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16819/131072 : ℝ))) (44420294897/250000000000 : ℝ) (88840589797/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16819/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44420294897/250000000000 : ℝ) (88840589797/500000000000 : ℝ) (294420294897/500000000000 : ℝ) (588840589797/1000000000000 : ℝ) (421522454429/1000000000000 : ℝ) (421522454437/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16819/131072 : ℝ))) 1 (294420294897/500000000000 : ℝ) (588840589797/1000000000000 : ℝ) (421522454429/1000000000000 : ℝ) (421522454437/1000000000000 : ℝ) (505181522111/1000000000000 : ℝ) (505181522117/1000000000000 : ℝ) (99641262673/200000000000 : ℝ) (124551578343/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16819/131072 : ℝ))) 2 (505181522111/1000000000000 : ℝ) (505181522117/1000000000000 : ℝ) (99641262673/200000000000 : ℝ) (124551578343/250000000000 : ℝ) (250846958869/500000000000 : ℝ) (100338783549/200000000000 : ℝ) (20067271811/40000000000 : ℝ) (501681795283/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16819/131072 : ℝ))) 3 (250846958869/500000000000 : ℝ) (100338783549/200000000000 : ℝ) (20067271811/40000000000 : ℝ) (501681795283/1000000000000 : ℝ) (250843928253/500000000000 : ℝ) (250843928257/500000000000 : ℝ) (501687856469/1000000000000 : ℝ) (250843928239/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16819/131072 : ℝ))) 4 (250843928253/500000000000 : ℝ) (250843928257/500000000000 : ℝ) (501687856469/1000000000000 : ℝ) (250843928239/500000000000 : ℝ) (501687856487/1000000000000 : ℝ) (31355491031/62500000000 : ℝ) (501687856487/1000000000000 : ℝ) (31355491031/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16819/131072 : ℝ))) 5 (501687856487/1000000000000 : ℝ) (31355491031/62500000000 : ℝ) (501687856487/1000000000000 : ℝ) (31355491031/62500000000 : ℝ) (501687856487/1000000000000 : ℝ) (31355491031/62500000000 : ℝ) (501687856487/1000000000000 : ℝ) (31355491031/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16819/131072 : ℝ))) 6 (501687856487/1000000000000 : ℝ) (31355491031/62500000000 : ℝ) (501687856487/1000000000000 : ℝ) (31355491031/62500000000 : ℝ) (501687856487/1000000000000 : ℝ) (31355491031/62500000000 : ℝ) (501687856487/1000000000000 : ℝ) (31355491031/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16819/131072 : ℝ))) 7 (501687856487/1000000000000 : ℝ) (31355491031/62500000000 : ℝ) (501687856487/1000000000000 : ℝ) (31355491031/62500000000 : ℝ) (501687856487/1000000000000 : ℝ) (31355491031/62500000000 : ℝ) (501687856487/1000000000000 : ℝ) (31355491031/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16819/131072 : ℝ)) hmem 8 (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ) (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16819/131072 : ℝ))) hcmem 8 (501687856487/1000000000000 : ℝ) (31355491031/62500000000 : ℝ) (501687856487/1000000000000 : ℝ) (31355491031/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16819/131072 : ℝ)) (992028101/1000000000 : ℝ) (992028101003/1000000000000 : ℝ) (501687856487/1000000000000 : ℝ) (31355491031/62500000000 : ℝ) (198595544161/250000000000 : ℝ) (397191088331/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1203_exp_lower
  have heNumeric : (2054903860681/1000000000000 : ℝ)/4 ≤ Real.exp (-85256358065861/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903860681/1000000000000 : ℝ)/4 ≤ Real.exp ((67275/524288 : ℝ)-(397191088331/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67275/524288 : ℝ) (16819/131072 : ℝ) (397191088331/500000000000 : ℝ) (2054903860681/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1204; no trusted numerical premise.
theorem cover8_leaf1204_exp_radius : (199599399569651361/200000000000000000 : ℝ) ≤ Real.exp ((-67277/4194304 : ℝ)/8) ∧ Real.exp ((-67277/4194304 : ℝ)/8) ≤ (498998498924128403/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67277/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1204_exp_lower : (36804543151779713/40000000000000000 : ℝ) ≤ Real.exp ((-21314089304989/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314089304989/32000000000000 : ℝ)/8) ≤ (460056789397246413/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314089304989/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1204_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903874261/1000000000000 : ℝ) ≤ 4*Real.exp (16819/131072 : ℝ)*Real.exp (-mu (radius 8 (67277/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903874261/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67277/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1204_exp_radius
  have hrNumeric : (984087870383/1000000000000 : ℝ) ≤ Real.exp (-67277/4194304 : ℝ) ∧ Real.exp (-67277/4194304 : ℝ) ≤ (61505491899/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984087870383/1000000000000 : ℝ) ≤ (radius 8 (67277/524288 : ℝ)) ∧ (radius 8 (67277/524288 : ℝ)) ≤ (61505491899/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67277/524288 : ℝ)) (984087870383/1000000000000 : ℝ) (61505491899/62500000000 : ℝ) (88841239527/500000000000 : ℝ) (177682479061/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67277/524288 : ℝ)) (984087870383/1000000000000 : ℝ) (61505491899/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67277/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984087870383/1000000000000 : ℝ) (61505491899/62500000000 : ℝ) (992043935191/1000000000000 : ℝ) (124005491899/125000000000 : ℝ) (99201203137/100000000000 : ℝ) (992012031371/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67277/524288 : ℝ)) 1 (992043935191/1000000000000 : ℝ) (124005491899/125000000000 : ℝ) (99201203137/100000000000 : ℝ) (992012031371/1000000000000 : ℝ) (12400349791/12500000000 : ℝ) (496013991641/500000000000 : ℝ) (62001748947/62500000000 : ℝ) (496013991577/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67277/524288 : ℝ)) 2 (12400349791/12500000000 : ℝ) (496013991641/500000000000 : ℝ) (62001748947/62500000000 : ℝ) (496013991577/500000000000 : ℝ) (62001748951/62500000000 : ℝ) (496013991609/500000000000 : ℝ) (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67277/524288 : ℝ)) 3 (62001748951/62500000000 : ℝ) (496013991609/500000000000 : ℝ) (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ) (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ) (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67277/524288 : ℝ)) 4 (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ) (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ) (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ) (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67277/524288 : ℝ)) 5 (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ) (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ) (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ) (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67277/524288 : ℝ)) 6 (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ) (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ) (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ) (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67277/524288 : ℝ)) 7 (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ) (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ) (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ) (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67277/524288 : ℝ))) (88841239527/500000000000 : ℝ) (177682479061/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67277/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88841239527/500000000000 : ℝ) (177682479061/1000000000000 : ℝ) (588841239527/1000000000000 : ℝ) (588841239531/1000000000000 : ℝ) (210761997911/500000000000 : ℝ) (421523995831/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67277/524288 : ℝ))) 1 (588841239527/1000000000000 : ℝ) (588841239531/1000000000000 : ℝ) (210761997911/500000000000 : ℝ) (421523995831/1000000000000 : ℝ) (252591308837/500000000000 : ℝ) (505182617681/1000000000000 : ℝ) (49820749913/100000000000 : ℝ) (249103749569/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67277/524288 : ℝ))) 2 (252591308837/500000000000 : ℝ) (505182617681/1000000000000 : ℝ) (49820749913/100000000000 : ℝ) (249103749569/500000000000 : ℝ) (250847529201/500000000000 : ℝ) (50169505841/100000000000 : ℝ) (12542073407/25000000000 : ℝ) (501682936289/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67277/524288 : ℝ))) 3 (250847529201/500000000000 : ℝ) (50169505841/100000000000 : ℝ) (12542073407/25000000000 : ℝ) (501682936289/1000000000000 : ℝ) (501688997341/1000000000000 : ℝ) (10033779947/20000000000 : ℝ) (62711124663/125000000000 : ℝ) (501688997313/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67277/524288 : ℝ))) 4 (501688997341/1000000000000 : ℝ) (10033779947/20000000000 : ℝ) (62711124663/125000000000 : ℝ) (501688997313/1000000000000 : ℝ) (250844498661/500000000000 : ℝ) (125422249333/250000000000 : ℝ) (250844498661/500000000000 : ℝ) (125422249333/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67277/524288 : ℝ))) 5 (250844498661/500000000000 : ℝ) (125422249333/250000000000 : ℝ) (250844498661/500000000000 : ℝ) (125422249333/250000000000 : ℝ) (250844498661/500000000000 : ℝ) (125422249333/250000000000 : ℝ) (250844498661/500000000000 : ℝ) (125422249333/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67277/524288 : ℝ))) 6 (250844498661/500000000000 : ℝ) (125422249333/250000000000 : ℝ) (250844498661/500000000000 : ℝ) (125422249333/250000000000 : ℝ) (250844498661/500000000000 : ℝ) (125422249333/250000000000 : ℝ) (250844498661/500000000000 : ℝ) (125422249333/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67277/524288 : ℝ))) 7 (250844498661/500000000000 : ℝ) (125422249333/250000000000 : ℝ) (250844498661/500000000000 : ℝ) (125422249333/250000000000 : ℝ) (250844498661/500000000000 : ℝ) (125422249333/250000000000 : ℝ) (250844498661/500000000000 : ℝ) (125422249333/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67277/524288 : ℝ)) hmem 8 (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ) (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67277/524288 : ℝ))) hcmem 8 (250844498661/500000000000 : ℝ) (125422249333/250000000000 : ℝ) (250844498661/500000000000 : ℝ) (125422249333/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67277/524288 : ℝ)) (198405596643/200000000000 : ℝ) (496013991609/500000000000 : ℝ) (250844498661/500000000000 : ℝ) (125422249333/250000000000 : ℝ) (794384077383/1000000000000 : ℝ) (397192038701/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1204_exp_lower
  have heNumeric : (2054903874261/1000000000000 : ℝ)/4 ≤ Real.exp (-21314089304989/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903874261/1000000000000 : ℝ)/4 ≤ Real.exp ((16819/131072 : ℝ)-(397192038701/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16819/131072 : ℝ) (67277/524288 : ℝ) (397192038701/500000000000 : ℝ) (2054903874261/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1205; no trusted numerical premise.
theorem cover8_leaf1205_exp_radius : (62374810506601811/62500000000000000 : ℝ) ≤ Real.exp ((-33639/2097152 : ℝ)/8) ∧ Real.exp ((-33639/2097152 : ℝ)/8) ≤ (997996968105628977/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33639/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1205_exp_lower : (230028394889478709/250000000000000000 : ℝ) ≤ Real.exp ((-85256356370339/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256356370339/128000000000000 : ℝ)/8) ≤ (920113579557914837/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256356370339/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1205_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903887901/1000000000000 : ℝ) ≤ 4*Real.exp (67277/524288 : ℝ)*Real.exp (-mu (radius 8 (33639/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903887901/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33639/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1205_exp_radius
  have hrNumeric : (984087635759/1000000000000 : ℝ) ≤ Real.exp (-33639/2097152 : ℝ) ∧ Real.exp (-33639/2097152 : ℝ) ≤ (12301095447/12500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984087635759/1000000000000 : ℝ) ≤ (radius 8 (33639/262144 : ℝ)) ∧ (radius 8 (33639/262144 : ℝ)) ≤ (12301095447/12500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33639/262144 : ℝ)) (984087635759/1000000000000 : ℝ) (12301095447/12500000000 : ℝ) (88841889253/500000000000 : ℝ) (11105236157/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33639/262144 : ℝ)) (984087635759/1000000000000 : ℝ) (12301095447/12500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33639/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984087635759/1000000000000 : ℝ) (12301095447/12500000000 : ℝ) (992043817879/1000000000000 : ℝ) (24801095447/25000000000 : ℝ) (992011913113/1000000000000 : ℝ) (496005956557/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33639/262144 : ℝ)) 1 (992043817879/1000000000000 : ℝ) (24801095447/25000000000 : ℝ) (992011913113/1000000000000 : ℝ) (496005956557/500000000000 : ℝ) (124003483187/125000000000 : ℝ) (992027865497/1000000000000 : ℝ) (992027865367/1000000000000 : ℝ) (992027865369/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33639/262144 : ℝ)) 2 (124003483187/125000000000 : ℝ) (992027865497/1000000000000 : ℝ) (992027865367/1000000000000 : ℝ) (992027865369/1000000000000 : ℝ) (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ) (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33639/262144 : ℝ)) 3 (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ) (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ) (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ) (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33639/262144 : ℝ)) 4 (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ) (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ) (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ) (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33639/262144 : ℝ)) 5 (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ) (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ) (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ) (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33639/262144 : ℝ)) 6 (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ) (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ) (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ) (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33639/262144 : ℝ)) 7 (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ) (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ) (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ) (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33639/262144 : ℝ))) (88841889253/500000000000 : ℝ) (11105236157/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33639/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88841889253/500000000000 : ℝ) (11105236157/62500000000 : ℝ) (588841889253/1000000000000 : ℝ) (73605236157/125000000000 : ℝ) (421525537193/1000000000000 : ℝ) (421525537201/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33639/262144 : ℝ))) 1 (588841889253/1000000000000 : ℝ) (73605236157/125000000000 : ℝ) (421525537193/1000000000000 : ℝ) (421525537201/1000000000000 : ℝ) (505183713223/1000000000000 : ℝ) (505183713229/1000000000000 : ℝ) (498208684879/1000000000000 : ℝ) (249104342443/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33639/262144 : ℝ))) 2 (505183713223/1000000000000 : ℝ) (505183713229/1000000000000 : ℝ) (498208684879/1000000000000 : ℝ) (249104342443/500000000000 : ℝ) (501696199051/1000000000000 : ℝ) (250848099529/500000000000 : ℝ) (50168407727/100000000000 : ℝ) (250842038639/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33639/262144 : ℝ))) 3 (501696199051/1000000000000 : ℝ) (250848099529/500000000000 : ℝ) (50168407727/100000000000 : ℝ) (250842038639/500000000000 : ℝ) (6271126727/12500000000 : ℝ) (62711267271/125000000000 : ℝ) (501690138123/1000000000000 : ℝ) (125422534533/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33639/262144 : ℝ))) 4 (6271126727/12500000000 : ℝ) (62711267271/125000000000 : ℝ) (501690138123/1000000000000 : ℝ) (125422534533/250000000000 : ℝ) (501690138141/1000000000000 : ℝ) (10033802763/20000000000 : ℝ) (501690138141/1000000000000 : ℝ) (10033802763/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33639/262144 : ℝ))) 5 (501690138141/1000000000000 : ℝ) (10033802763/20000000000 : ℝ) (501690138141/1000000000000 : ℝ) (10033802763/20000000000 : ℝ) (501690138141/1000000000000 : ℝ) (10033802763/20000000000 : ℝ) (501690138141/1000000000000 : ℝ) (10033802763/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33639/262144 : ℝ))) 6 (501690138141/1000000000000 : ℝ) (10033802763/20000000000 : ℝ) (501690138141/1000000000000 : ℝ) (10033802763/20000000000 : ℝ) (501690138141/1000000000000 : ℝ) (10033802763/20000000000 : ℝ) (501690138141/1000000000000 : ℝ) (10033802763/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33639/262144 : ℝ))) 7 (501690138141/1000000000000 : ℝ) (10033802763/20000000000 : ℝ) (501690138141/1000000000000 : ℝ) (10033802763/20000000000 : ℝ) (501690138141/1000000000000 : ℝ) (10033802763/20000000000 : ℝ) (501690138141/1000000000000 : ℝ) (10033802763/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33639/262144 : ℝ)) hmem 8 (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ) (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33639/262144 : ℝ))) hcmem 8 (501690138141/1000000000000 : ℝ) (10033802763/20000000000 : ℝ) (501690138141/1000000000000 : ℝ) (10033802763/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33639/262144 : ℝ)) (992027865431/1000000000000 : ℝ) (992027865433/1000000000000 : ℝ) (501690138141/1000000000000 : ℝ) (10033802763/20000000000 : ℝ) (49649123631/62500000000 : ℝ) (794385978113/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1205_exp_lower
  have heNumeric : (2054903887901/1000000000000 : ℝ)/4 ≤ Real.exp (-85256356370339/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903887901/1000000000000 : ℝ)/4 ≤ Real.exp ((67277/524288 : ℝ)-(794385978113/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67277/524288 : ℝ) (33639/262144 : ℝ) (794385978113/1000000000000 : ℝ) (2054903887901/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1206; no trusted numerical premise.
theorem cover8_leaf1206_exp_radius : (498998469181501017/500000000000000000 : ℝ) ≤ Real.exp ((-67279/4194304 : ℝ)/8) ∧ Real.exp ((-67279/4194304 : ℝ)/8) ≤ (199599387672600407/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67279/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1206_exp_lower : (920113580322256961/1000000000000000000 : ℝ) ≤ Real.exp ((-42628177759849/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628177759849/64000000000000 : ℝ)/8) ≤ (460056790161128481/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628177759849/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1206_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903901557/1000000000000 : ℝ) ≤ 4*Real.exp (33639/262144 : ℝ)*Real.exp (-mu (radius 8 (67279/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903901557/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67279/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1206_exp_radius
  have hrNumeric : (492043700567/500000000000 : ℝ) ≤ Real.exp (-67279/4194304 : ℝ) ∧ Real.exp (-67279/4194304 : ℝ) ≤ (196817480227/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492043700567/500000000000 : ℝ) ≤ (radius 8 (67279/524288 : ℝ)) ∧ (radius 8 (67279/524288 : ℝ)) ≤ (196817480227/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67279/524288 : ℝ)) (492043700567/500000000000 : ℝ) (196817480227/200000000000 : ℝ) (177685077953/1000000000000 : ℝ) (4442126949/25000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67279/524288 : ℝ)) (492043700567/500000000000 : ℝ) (196817480227/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67279/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492043700567/500000000000 : ℝ) (196817480227/200000000000 : ℝ) (992043700567/1000000000000 : ℝ) (124005462571/125000000000 : ℝ) (124001474357/125000000000 : ℝ) (992011794857/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67279/524288 : ℝ)) 1 (992043700567/1000000000000 : ℝ) (124005462571/125000000000 : ℝ) (124001474357/125000000000 : ℝ) (992011794857/1000000000000 : ℝ) (992027747711/1000000000000 : ℝ) (992027747713/1000000000000 : ℝ) (992027747583/1000000000000 : ℝ) (198405549517/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67279/524288 : ℝ)) 2 (992027747711/1000000000000 : ℝ) (992027747713/1000000000000 : ℝ) (992027747583/1000000000000 : ℝ) (198405549517/200000000000 : ℝ) (992027747647/1000000000000 : ℝ) (992027747649/1000000000000 : ℝ) (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67279/524288 : ℝ)) 3 (992027747647/1000000000000 : ℝ) (992027747649/1000000000000 : ℝ) (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ) (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ) (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67279/524288 : ℝ)) 4 (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ) (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ) (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ) (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67279/524288 : ℝ)) 5 (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ) (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ) (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ) (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67279/524288 : ℝ)) 6 (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ) (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ) (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ) (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67279/524288 : ℝ)) 7 (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ) (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ) (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ) (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67279/524288 : ℝ))) (177685077953/1000000000000 : ℝ) (4442126949/25000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67279/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177685077953/1000000000000 : ℝ) (4442126949/25000000000 : ℝ) (18401329343/31250000000 : ℝ) (29442126949/50000000000 : ℝ) (52690884819/125000000000 : ℝ) (421527078561/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67279/524288 : ℝ))) 1 (18401329343/31250000000 : ℝ) (29442126949/50000000000 : ℝ) (52690884819/125000000000 : ℝ) (421527078561/1000000000000 : ℝ) (126296202191/250000000000 : ℝ) (505184808771/1000000000000 : ℝ) (249104935309/500000000000 : ℝ) (249104935313/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67279/524288 : ℝ))) 2 (126296202191/250000000000 : ℝ) (505184808771/1000000000000 : ℝ) (249104935309/500000000000 : ℝ) (249104935313/500000000000 : ℝ) (501697339691/1000000000000 : ℝ) (501697339699/1000000000000 : ℝ) (501685218251/1000000000000 : ℝ) (25084260913/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67279/524288 : ℝ))) 3 (501697339691/1000000000000 : ℝ) (501697339699/1000000000000 : ℝ) (501685218251/1000000000000 : ℝ) (25084260913/50000000000 : ℝ) (501691278971/1000000000000 : ℝ) (25084563949/50000000000 : ℝ) (250845639467/500000000000 : ℝ) (501691278943/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67279/524288 : ℝ))) 4 (501691278971/1000000000000 : ℝ) (25084563949/50000000000 : ℝ) (250845639467/500000000000 : ℝ) (501691278943/1000000000000 : ℝ) (62711409869/125000000000 : ℝ) (250845639481/500000000000 : ℝ) (62711409869/125000000000 : ℝ) (250845639481/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67279/524288 : ℝ))) 5 (62711409869/125000000000 : ℝ) (250845639481/500000000000 : ℝ) (62711409869/125000000000 : ℝ) (250845639481/500000000000 : ℝ) (62711409869/125000000000 : ℝ) (250845639481/500000000000 : ℝ) (62711409869/125000000000 : ℝ) (250845639481/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67279/524288 : ℝ))) 6 (62711409869/125000000000 : ℝ) (250845639481/500000000000 : ℝ) (62711409869/125000000000 : ℝ) (250845639481/500000000000 : ℝ) (62711409869/125000000000 : ℝ) (250845639481/500000000000 : ℝ) (62711409869/125000000000 : ℝ) (250845639481/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67279/524288 : ℝ))) 7 (62711409869/125000000000 : ℝ) (250845639481/500000000000 : ℝ) (62711409869/125000000000 : ℝ) (250845639481/500000000000 : ℝ) (62711409869/125000000000 : ℝ) (250845639481/500000000000 : ℝ) (62711409869/125000000000 : ℝ) (250845639481/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67279/524288 : ℝ)) hmem 8 (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ) (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67279/524288 : ℝ))) hcmem 8 (62711409869/125000000000 : ℝ) (250845639481/500000000000 : ℝ) (62711409869/125000000000 : ℝ) (250845639481/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67279/524288 : ℝ)) (496013873823/500000000000 : ℝ) (992027747649/1000000000000 : ℝ) (62711409869/125000000000 : ℝ) (250845639481/500000000000 : ℝ) (794387878797/1000000000000 : ℝ) (24824621213/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1206_exp_lower
  have heNumeric : (2054903901557/1000000000000 : ℝ)/4 ≤ Real.exp (-42628177759849/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903901557/1000000000000 : ℝ)/4 ≤ Real.exp ((33639/262144 : ℝ)-(24824621213/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33639/262144 : ℝ) (67279/524288 : ℝ) (24824621213/31250000000 : ℝ) (2054903901557/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1207; no trusted numerical premise.
theorem cover8_leaf1207_exp_radius : (498998454310187989/500000000000000000 : ℝ) ≤ Real.exp ((-4205/262144 : ℝ)/8) ∧ Real.exp ((-4205/262144 : ℝ)/8) ≤ (997996908620375979/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4205/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1207_exp_lower : (460056790544564699/500000000000000000 : ℝ) ≤ Real.exp ((-85256354666241/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256354666241/128000000000000 : ℝ)/8) ≤ (920113581089129399/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256354666241/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1207_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451957629/500000000000 : ℝ) ≤ 4*Real.exp (67279/524288 : ℝ)*Real.exp (-mu (radius 8 (4205/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451957629/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4205/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1207_exp_radius
  have hrNumeric : (984087166509/1000000000000 : ℝ) ≤ Real.exp (-4205/262144 : ℝ) ∧ Real.exp (-4205/262144 : ℝ) ≤ (98408716651/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984087166509/1000000000000 : ℝ) ≤ (radius 8 (4205/32768 : ℝ)) ∧ (radius 8 (4205/32768 : ℝ)) ≤ (98408716651/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4205/32768 : ℝ)) (984087166509/1000000000000 : ℝ) (98408716651/100000000000 : ℝ) (17768637739/100000000000 : ℝ) (177686377397/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4205/32768 : ℝ)) (984087166509/1000000000000 : ℝ) (98408716651/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4205/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984087166509/1000000000000 : ℝ) (98408716651/100000000000 : ℝ) (496021791627/500000000000 : ℝ) (198408716651/200000000000 : ℝ) (992011676599/1000000000000 : ℝ) (4960058383/5000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4205/32768 : ℝ)) 1 (496021791627/500000000000 : ℝ) (198408716651/200000000000 : ℝ) (992011676599/1000000000000 : ℝ) (4960058383/5000000000 : ℝ) (496013814963/500000000000 : ℝ) (124003453741/125000000000 : ℝ) (496013814899/500000000000 : ℝ) (4960138149/5000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4205/32768 : ℝ)) 2 (496013814963/500000000000 : ℝ) (124003453741/125000000000 : ℝ) (496013814899/500000000000 : ℝ) (4960138149/5000000000 : ℝ) (496013814931/500000000000 : ℝ) (124003453733/125000000000 : ℝ) (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4205/32768 : ℝ)) 3 (496013814931/500000000000 : ℝ) (124003453733/125000000000 : ℝ) (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ) (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ) (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4205/32768 : ℝ)) 4 (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ) (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ) (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ) (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4205/32768 : ℝ)) 5 (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ) (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ) (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ) (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4205/32768 : ℝ)) 6 (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ) (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ) (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ) (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4205/32768 : ℝ)) 7 (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ) (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ) (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ) (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4205/32768 : ℝ))) (17768637739/100000000000 : ℝ) (177686377397/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4205/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17768637739/100000000000 : ℝ) (177686377397/1000000000000 : ℝ) (117768637739/200000000000 : ℝ) (588843188699/1000000000000 : ℝ) (210764309947/500000000000 : ℝ) (421528619903/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4205/32768 : ℝ))) 1 (117768637739/200000000000 : ℝ) (588843188699/1000000000000 : ℝ) (210764309947/500000000000 : ℝ) (421528619903/1000000000000 : ℝ) (252592952147/500000000000 : ℝ) (505185904301/1000000000000 : ℝ) (99642211269/200000000000 : ℝ) (498211056353/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4205/32768 : ℝ))) 2 (252592952147/500000000000 : ℝ) (505185904301/1000000000000 : ℝ) (99642211269/200000000000 : ℝ) (498211056353/1000000000000 : ℝ) (501698480319/1000000000000 : ℝ) (501698480327/1000000000000 : ℝ) (501686359221/1000000000000 : ℝ) (501686359229/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4205/32768 : ℝ))) 3 (501698480319/1000000000000 : ℝ) (501698480327/1000000000000 : ℝ) (501686359221/1000000000000 : ℝ) (501686359229/1000000000000 : ℝ) (50169241977/100000000000 : ℝ) (250846209889/500000000000 : ℝ) (501692419733/1000000000000 : ℝ) (250846209871/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4205/32768 : ℝ))) 4 (50169241977/100000000000 : ℝ) (250846209889/500000000000 : ℝ) (501692419733/1000000000000 : ℝ) (250846209871/500000000000 : ℝ) (501692419751/1000000000000 : ℝ) (6271155247/12500000000 : ℝ) (501692419751/1000000000000 : ℝ) (6271155247/12500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4205/32768 : ℝ))) 5 (501692419751/1000000000000 : ℝ) (6271155247/12500000000 : ℝ) (501692419751/1000000000000 : ℝ) (6271155247/12500000000 : ℝ) (501692419751/1000000000000 : ℝ) (6271155247/12500000000 : ℝ) (501692419751/1000000000000 : ℝ) (6271155247/12500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4205/32768 : ℝ))) 6 (501692419751/1000000000000 : ℝ) (6271155247/12500000000 : ℝ) (501692419751/1000000000000 : ℝ) (6271155247/12500000000 : ℝ) (501692419751/1000000000000 : ℝ) (6271155247/12500000000 : ℝ) (501692419751/1000000000000 : ℝ) (6271155247/12500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4205/32768 : ℝ))) 7 (501692419751/1000000000000 : ℝ) (6271155247/12500000000 : ℝ) (501692419751/1000000000000 : ℝ) (6271155247/12500000000 : ℝ) (501692419751/1000000000000 : ℝ) (6271155247/12500000000 : ℝ) (501692419751/1000000000000 : ℝ) (6271155247/12500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4205/32768 : ℝ)) hmem 8 (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ) (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4205/32768 : ℝ))) hcmem 8 (501692419751/1000000000000 : ℝ) (6271155247/12500000000 : ℝ) (501692419751/1000000000000 : ℝ) (6271155247/12500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4205/32768 : ℝ)) (992027629861/1000000000000 : ℝ) (124003453733/125000000000 : ℝ) (501692419751/1000000000000 : ℝ) (6271155247/12500000000 : ℝ) (794389779479/1000000000000 : ℝ) (794389779497/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1207_exp_lower
  have heNumeric : (1027451957629/500000000000 : ℝ)/4 ≤ Real.exp (-85256354666241/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451957629/500000000000 : ℝ)/4 ≤ Real.exp ((67279/524288 : ℝ)-(794389779497/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67279/524288 : ℝ) (4205/32768 : ℝ) (794389779497/1000000000000 : ℝ) (1027451957629/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1208; no trusted numerical premise.
theorem cover8_leaf1208_exp_radius : (498998424567563263/500000000000000000 : ℝ) ≤ Real.exp ((-33641/2097152 : ℝ)/8) ∧ Real.exp ((-33641/2097152 : ℝ)/8) ≤ (997996849135126527/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33641/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1208_exp_lower : (460056681628756641/500000000000000000 : ℝ) ≤ Real.exp ((-213141492731/320000000000 : ℝ)/8) ∧ Real.exp ((-213141492731/320000000000 : ℝ)/8) ≤ (920113363257513283/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-213141492731/320000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1208_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900023367/1000000000000 : ℝ) ≤ 4*Real.exp (4205/32768 : ℝ)*Real.exp (-mu (radius 8 (33641/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900023367/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33641/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1208_exp_radius
  have hrNumeric : (49204334863/50000000000 : ℝ) ≤ Real.exp (-33641/2097152 : ℝ) ∧ Real.exp (-33641/2097152 : ℝ) ≤ (984086697261/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49204334863/50000000000 : ℝ) ≤ (radius 8 (33641/262144 : ℝ)) ∧ (radius 8 (33641/262144 : ℝ)) ≤ (984086697261/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33641/262144 : ℝ)) (49204334863/50000000000 : ℝ) (984086697261/1000000000000 : ℝ) (17768897623/100000000000 : ℝ) (177688976237/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33641/262144 : ℝ)) (49204334863/50000000000 : ℝ) (984086697261/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33641/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49204334863/50000000000 : ℝ) (984086697261/1000000000000 : ℝ) (99204334863/100000000000 : ℝ) (992043348631/1000000000000 : ℝ) (198402288017/200000000000 : ℝ) (496005720043/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33641/262144 : ℝ)) 1 (99204334863/100000000000 : ℝ) (992043348631/1000000000000 : ℝ) (198402288017/200000000000 : ℝ) (496005720043/500000000000 : ℝ) (992027394357/1000000000000 : ℝ) (992027394359/1000000000000 : ℝ) (992027394229/1000000000000 : ℝ) (992027394231/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33641/262144 : ℝ)) 2 (992027394357/1000000000000 : ℝ) (992027394359/1000000000000 : ℝ) (992027394229/1000000000000 : ℝ) (992027394231/1000000000000 : ℝ) (992027394293/1000000000000 : ℝ) (198405478859/200000000000 : ℝ) (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33641/262144 : ℝ)) 3 (992027394293/1000000000000 : ℝ) (198405478859/200000000000 : ℝ) (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ) (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ) (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33641/262144 : ℝ)) 4 (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ) (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ) (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ) (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33641/262144 : ℝ)) 5 (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ) (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ) (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ) (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33641/262144 : ℝ)) 6 (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ) (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ) (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ) (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33641/262144 : ℝ)) 7 (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ) (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ) (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ) (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33641/262144 : ℝ))) (17768897623/100000000000 : ℝ) (177688976237/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33641/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17768897623/100000000000 : ℝ) (177688976237/1000000000000 : ℝ) (117768897623/200000000000 : ℝ) (588844488119/1000000000000 : ℝ) (10538292563/25000000000 : ℝ) (42153170253/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33641/262144 : ℝ))) 1 (117768897623/200000000000 : ℝ) (588844488119/1000000000000 : ℝ) (10538292563/25000000000 : ℝ) (42153170253/100000000000 : ℝ) (505188095317/1000000000000 : ℝ) (20207523813/40000000000 : ℝ) (249106713877/500000000000 : ℝ) (249106713881/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33641/262144 : ℝ))) 2 (505188095317/1000000000000 : ℝ) (20207523813/40000000000 : ℝ) (249106713877/500000000000 : ℝ) (249106713881/500000000000 : ℝ) (100340152307/200000000000 : ℝ) (62712595193/125000000000 : ℝ) (501688641119/1000000000000 : ℝ) (62711080141/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33641/262144 : ℝ))) 3 (100340152307/200000000000 : ℝ) (62712595193/125000000000 : ℝ) (501688641119/1000000000000 : ℝ) (62711080141/125000000000 : ℝ) (501694701327/1000000000000 : ℝ) (62711837667/125000000000 : ℝ) (50169470129/100000000000 : ℝ) (5016947013/10000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33641/262144 : ℝ))) 4 (501694701327/1000000000000 : ℝ) (62711837667/125000000000 : ℝ) (50169470129/100000000000 : ℝ) (5016947013/10000000000 : ℝ) (125423675327/250000000000 : ℝ) (250847350659/500000000000 : ℝ) (125423675327/250000000000 : ℝ) (250847350659/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33641/262144 : ℝ))) 5 (125423675327/250000000000 : ℝ) (250847350659/500000000000 : ℝ) (125423675327/250000000000 : ℝ) (250847350659/500000000000 : ℝ) (125423675327/250000000000 : ℝ) (250847350659/500000000000 : ℝ) (125423675327/250000000000 : ℝ) (250847350659/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33641/262144 : ℝ))) 6 (125423675327/250000000000 : ℝ) (250847350659/500000000000 : ℝ) (125423675327/250000000000 : ℝ) (250847350659/500000000000 : ℝ) (125423675327/250000000000 : ℝ) (250847350659/500000000000 : ℝ) (125423675327/250000000000 : ℝ) (250847350659/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33641/262144 : ℝ))) 7 (125423675327/250000000000 : ℝ) (250847350659/500000000000 : ℝ) (125423675327/250000000000 : ℝ) (250847350659/500000000000 : ℝ) (125423675327/250000000000 : ℝ) (250847350659/500000000000 : ℝ) (125423675327/250000000000 : ℝ) (250847350659/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33641/262144 : ℝ)) hmem 8 (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ) (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33641/262144 : ℝ))) hcmem 8 (125423675327/250000000000 : ℝ) (250847350659/500000000000 : ℝ) (125423675327/250000000000 : ℝ) (250847350659/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33641/262144 : ℝ)) (248006848573/250000000000 : ℝ) (198405478859/200000000000 : ℝ) (125423675327/250000000000 : ℝ) (250847350659/500000000000 : ℝ) (794393580781/1000000000000 : ℝ) (124123997/156250000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1208_exp_lower
  have heNumeric : (2054900023367/1000000000000 : ℝ)/4 ≤ Real.exp (-213141492731/320000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900023367/1000000000000 : ℝ)/4 ≤ Real.exp ((4205/32768 : ℝ)-(124123997/156250000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4205/32768 : ℝ) (33641/262144 : ℝ) (124123997/156250000 : ℝ) (2054900023367/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1209; no trusted numerical premise.
theorem cover8_leaf1209_exp_radius : (997996789649880619/1000000000000000000 : ℝ) ≤ Real.exp ((-16821/1048576 : ℝ)/8) ∧ Real.exp ((-16821/1048576 : ℝ)/8) ≤ (49899839482494031/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16821/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1209_exp_lower : (460056682403507369/500000000000000000 : ℝ) ≤ Real.exp ((-1705131907359/2560000000000 : ℝ)/8) ∧ Real.exp ((-1705131907359/2560000000000 : ℝ)/8) ≤ (920113364807014739/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1705131907359/2560000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1209_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725012763/250000000000 : ℝ) ≤ 4*Real.exp (33641/262144 : ℝ)*Real.exp (-mu (radius 8 (16821/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513725012763/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16821/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1209_exp_radius
  have hrNumeric : (984086228011/1000000000000 : ℝ) ≤ Real.exp (-16821/1048576 : ℝ) ∧ Real.exp (-16821/1048576 : ℝ) ≤ (246021557003/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984086228011/1000000000000 : ℝ) ≤ (radius 8 (16821/131072 : ℝ)) ∧ (radius 8 (16821/131072 : ℝ)) ≤ (246021557003/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16821/131072 : ℝ)) (984086228011/1000000000000 : ℝ) (246021557003/250000000000 : ℝ) (177691575031/1000000000000 : ℝ) (177691575037/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16821/131072 : ℝ)) (984086228011/1000000000000 : ℝ) (246021557003/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16821/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984086228011/1000000000000 : ℝ) (246021557003/250000000000 : ℝ) (198408622801/200000000000 : ℝ) (496021557003/500000000000 : ℝ) (992011203571/1000000000000 : ℝ) (248002800893/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16821/131072 : ℝ)) 1 (198408622801/200000000000 : ℝ) (496021557003/500000000000 : ℝ) (992011203571/1000000000000 : ℝ) (248002800893/250000000000 : ℝ) (248006789697/250000000000 : ℝ) (992027158789/1000000000000 : ℝ) (992027158659/1000000000000 : ℝ) (992027158661/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16821/131072 : ℝ)) 2 (248006789697/250000000000 : ℝ) (992027158789/1000000000000 : ℝ) (992027158659/1000000000000 : ℝ) (992027158661/1000000000000 : ℝ) (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ) (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16821/131072 : ℝ)) 3 (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ) (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ) (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ) (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16821/131072 : ℝ)) 4 (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ) (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ) (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ) (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16821/131072 : ℝ)) 5 (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ) (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ) (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ) (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16821/131072 : ℝ)) 6 (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ) (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ) (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ) (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16821/131072 : ℝ)) 7 (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ) (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ) (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ) (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16821/131072 : ℝ))) (177691575031/1000000000000 : ℝ) (177691575037/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16821/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177691575031/1000000000000 : ℝ) (177691575037/1000000000000 : ℝ) (117769157503/200000000000 : ℝ) (588845787519/1000000000000 : ℝ) (210767392539/500000000000 : ℝ) (210767392543/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16821/131072 : ℝ))) 1 (117769157503/200000000000 : ℝ) (588845787519/1000000000000 : ℝ) (210767392539/500000000000 : ℝ) (210767392543/500000000000 : ℝ) (63148785787/125000000000 : ℝ) (505190286303/1000000000000 : ℝ) (498215799111/1000000000000 : ℝ) (249107899559/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16821/131072 : ℝ))) 2 (63148785787/125000000000 : ℝ) (505190286303/1000000000000 : ℝ) (498215799111/1000000000000 : ℝ) (249107899559/500000000000 : ℝ) (501703042703/1000000000000 : ℝ) (501703042711/1000000000000 : ℝ) (501690922969/1000000000000 : ℝ) (501690922977/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16821/131072 : ℝ))) 3 (501703042703/1000000000000 : ℝ) (501703042711/1000000000000 : ℝ) (501690922969/1000000000000 : ℝ) (501690922977/1000000000000 : ℝ) (125424245709/250000000000 : ℝ) (125424245711/250000000000 : ℝ) (501696982799/1000000000000 : ℝ) (62712122851/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16821/131072 : ℝ))) 4 (125424245709/250000000000 : ℝ) (125424245711/250000000000 : ℝ) (501696982799/1000000000000 : ℝ) (62712122851/125000000000 : ℝ) (501696982817/1000000000000 : ℝ) (250848491413/500000000000 : ℝ) (501696982817/1000000000000 : ℝ) (250848491413/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16821/131072 : ℝ))) 5 (501696982817/1000000000000 : ℝ) (250848491413/500000000000 : ℝ) (501696982817/1000000000000 : ℝ) (250848491413/500000000000 : ℝ) (501696982817/1000000000000 : ℝ) (250848491413/500000000000 : ℝ) (501696982817/1000000000000 : ℝ) (250848491413/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16821/131072 : ℝ))) 6 (501696982817/1000000000000 : ℝ) (250848491413/500000000000 : ℝ) (501696982817/1000000000000 : ℝ) (250848491413/500000000000 : ℝ) (501696982817/1000000000000 : ℝ) (250848491413/500000000000 : ℝ) (501696982817/1000000000000 : ℝ) (250848491413/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16821/131072 : ℝ))) 7 (501696982817/1000000000000 : ℝ) (250848491413/500000000000 : ℝ) (501696982817/1000000000000 : ℝ) (250848491413/500000000000 : ℝ) (501696982817/1000000000000 : ℝ) (250848491413/500000000000 : ℝ) (501696982817/1000000000000 : ℝ) (250848491413/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16821/131072 : ℝ)) hmem 8 (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ) (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16821/131072 : ℝ))) hcmem 8 (501696982817/1000000000000 : ℝ) (250848491413/500000000000 : ℝ) (501696982817/1000000000000 : ℝ) (250848491413/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16821/131072 : ℝ)) (992027158723/1000000000000 : ℝ) (39681086349/40000000000 : ℝ) (501696982817/1000000000000 : ℝ) (250848491413/500000000000 : ℝ) (794397382009/1000000000000 : ℝ) (31775895281/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1209_exp_lower
  have heNumeric : (513725012763/250000000000 : ℝ)/4 ≤ Real.exp (-1705131907359/2560000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725012763/250000000000 : ℝ)/4 ≤ Real.exp ((33641/262144 : ℝ)-(31775895281/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33641/262144 : ℝ) (16821/131072 : ℝ) (31775895281/40000000000 : ℝ) (513725012763/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1210; no trusted numerical premise.
theorem cover8_leaf1210_exp_radius : (997996730164638257/1000000000000000000 : ℝ) ≤ Real.exp ((-33643/2097152 : ℝ)/8) ∧ Real.exp ((-33643/2097152 : ℝ)/8) ≤ (498998365082319129/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33643/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1210_exp_lower : (28753542698899913/31250000000000000 : ℝ) ≤ Real.exp ((-21314148408571/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314148408571/32000000000000 : ℝ)/8) ≤ (920113366364797217/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314148408571/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1210_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725019721/250000000000 : ℝ) ≤ 4*Real.exp (16821/131072 : ℝ)*Real.exp (-mu (radius 8 (33643/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725019721/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33643/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1210_exp_radius
  have hrNumeric : (492042879381/500000000000 : ℝ) ≤ Real.exp (-33643/2097152 : ℝ) ∧ Real.exp (-33643/2097152 : ℝ) ≤ (984085758763/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492042879381/500000000000 : ℝ) ≤ (radius 8 (33643/262144 : ℝ)) ∧ (radius 8 (33643/262144 : ℝ)) ≤ (984085758763/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33643/262144 : ℝ)) (492042879381/500000000000 : ℝ) (984085758763/1000000000000 : ℝ) (5552942931/31250000000 : ℝ) (177694173799/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33643/262144 : ℝ)) (492042879381/500000000000 : ℝ) (984085758763/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33643/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492042879381/500000000000 : ℝ) (984085758763/1000000000000 : ℝ) (992042879381/1000000000000 : ℝ) (496021439691/500000000000 : ℝ) (992010967057/1000000000000 : ℝ) (496005483529/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33643/262144 : ℝ)) 1 (992042879381/1000000000000 : ℝ) (496021439691/500000000000 : ℝ) (992010967057/1000000000000 : ℝ) (496005483529/500000000000 : ℝ) (992026923219/1000000000000 : ℝ) (49601346161/50000000000 : ℝ) (99202692309/100000000000 : ℝ) (248006730773/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33643/262144 : ℝ)) 2 (992026923219/1000000000000 : ℝ) (49601346161/50000000000 : ℝ) (99202692309/100000000000 : ℝ) (248006730773/250000000000 : ℝ) (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ) (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33643/262144 : ℝ)) 3 (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ) (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ) (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ) (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33643/262144 : ℝ)) 4 (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ) (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ) (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ) (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33643/262144 : ℝ)) 5 (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ) (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ) (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ) (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33643/262144 : ℝ)) 6 (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ) (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ) (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ) (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33643/262144 : ℝ)) 7 (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ) (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ) (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ) (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33643/262144 : ℝ))) (5552942931/31250000000 : ℝ) (177694173799/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33643/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5552942931/31250000000 : ℝ) (177694173799/1000000000000 : ℝ) (36802942931/62500000000 : ℝ) (5888470869/10000000000 : ℝ) (84307573513/200000000000 : ℝ) (16861514703/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33643/262144 : ℝ))) 1 (36802942931/62500000000 : ℝ) (5888470869/10000000000 : ℝ) (84307573513/200000000000 : ℝ) (16861514703/40000000000 : ℝ) (50519247723/100000000000 : ℝ) (252596238619/500000000000 : ℝ) (99643634083/200000000000 : ℝ) (498218170423/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33643/262144 : ℝ))) 2 (50519247723/100000000000 : ℝ) (252596238619/500000000000 : ℝ) (99643634083/200000000000 : ℝ) (498218170423/1000000000000 : ℝ) (250852661911/500000000000 : ℝ) (501705323831/1000000000000 : ℝ) (50169320477/100000000000 : ℝ) (501693204779/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33643/262144 : ℝ))) 3 (250852661911/500000000000 : ℝ) (501705323831/1000000000000 : ℝ) (50169320477/100000000000 : ℝ) (501693204779/1000000000000 : ℝ) (62712408037/125000000000 : ℝ) (100339852861/200000000000 : ℝ) (501699264259/1000000000000 : ℝ) (501699264269/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33643/262144 : ℝ))) 4 (62712408037/125000000000 : ℝ) (100339852861/200000000000 : ℝ) (501699264259/1000000000000 : ℝ) (501699264269/1000000000000 : ℝ) (501699264277/1000000000000 : ℝ) (501699264287/1000000000000 : ℝ) (501699264277/1000000000000 : ℝ) (501699264287/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33643/262144 : ℝ))) 5 (501699264277/1000000000000 : ℝ) (501699264287/1000000000000 : ℝ) (501699264277/1000000000000 : ℝ) (501699264287/1000000000000 : ℝ) (501699264277/1000000000000 : ℝ) (501699264287/1000000000000 : ℝ) (501699264277/1000000000000 : ℝ) (501699264287/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33643/262144 : ℝ))) 6 (501699264277/1000000000000 : ℝ) (501699264287/1000000000000 : ℝ) (501699264277/1000000000000 : ℝ) (501699264287/1000000000000 : ℝ) (501699264277/1000000000000 : ℝ) (501699264287/1000000000000 : ℝ) (501699264277/1000000000000 : ℝ) (501699264287/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33643/262144 : ℝ))) 7 (501699264277/1000000000000 : ℝ) (501699264287/1000000000000 : ℝ) (501699264277/1000000000000 : ℝ) (501699264287/1000000000000 : ℝ) (501699264277/1000000000000 : ℝ) (501699264287/1000000000000 : ℝ) (501699264277/1000000000000 : ℝ) (501699264287/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33643/262144 : ℝ)) hmem 8 (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ) (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33643/262144 : ℝ))) hcmem 8 (501699264277/1000000000000 : ℝ) (501699264287/1000000000000 : ℝ) (501699264277/1000000000000 : ℝ) (501699264287/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33643/262144 : ℝ)) (496013461577/500000000000 : ℝ) (248006730789/250000000000 : ℝ) (501699264277/1000000000000 : ℝ) (501699264287/1000000000000 : ℝ) (19860029579/25000000000 : ℝ) (397200591589/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1210_exp_lower
  have heNumeric : (513725019721/250000000000 : ℝ)/4 ≤ Real.exp (-21314148408571/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725019721/250000000000 : ℝ)/4 ≤ Real.exp ((16821/131072 : ℝ)-(397200591589/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16821/131072 : ℝ) (33643/262144 : ℝ) (397200591589/500000000000 : ℝ) (513725019721/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1211; no trusted numerical premise.
theorem cover8_leaf1211_exp_radius : (498998335339699721/500000000000000000 : ℝ) ≤ Real.exp ((-8411/524288 : ℝ)/8) ∧ Real.exp ((-8411/524288 : ℝ)/8) ≤ (997996670679399443/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8411/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1211_exp_lower : (460056683966177951/500000000000000000 : ℝ) ≤ Real.exp ((-42628295944869/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628295944869/64000000000000 : ℝ)/8) ≤ (920113367932355903/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628295944869/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1211_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900106891/1000000000000 : ℝ) ≤ 4*Real.exp (33643/262144 : ℝ)*Real.exp (-mu (radius 8 (8411/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900106891/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8411/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1211_exp_radius
  have hrNumeric : (492042644757/500000000000 : ℝ) ≤ Real.exp (-8411/524288 : ℝ) ∧ Real.exp (-8411/524288 : ℝ) ≤ (196817057903/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492042644757/500000000000 : ℝ) ≤ (radius 8 (8411/65536 : ℝ)) ∧ (radius 8 (8411/65536 : ℝ)) ≤ (196817057903/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8411/65536 : ℝ)) (492042644757/500000000000 : ℝ) (196817057903/200000000000 : ℝ) (177696772509/1000000000000 : ℝ) (35539354503/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8411/65536 : ℝ)) (492042644757/500000000000 : ℝ) (196817057903/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8411/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492042644757/500000000000 : ℝ) (196817057903/200000000000 : ℝ) (992042644757/1000000000000 : ℝ) (496021322379/500000000000 : ℝ) (992010730543/1000000000000 : ℝ) (198402146109/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8411/65536 : ℝ)) 1 (992042644757/1000000000000 : ℝ) (496021322379/500000000000 : ℝ) (992010730543/1000000000000 : ℝ) (198402146109/200000000000 : ℝ) (19840533753/20000000000 : ℝ) (248006671913/250000000000 : ℝ) (992026687521/1000000000000 : ℝ) (248006671881/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8411/65536 : ℝ)) 2 (19840533753/20000000000 : ℝ) (248006671913/250000000000 : ℝ) (992026687521/1000000000000 : ℝ) (248006671881/250000000000 : ℝ) (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ) (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8411/65536 : ℝ)) 3 (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ) (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ) (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ) (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8411/65536 : ℝ)) 4 (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ) (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ) (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ) (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8411/65536 : ℝ)) 5 (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ) (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ) (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ) (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8411/65536 : ℝ)) 6 (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ) (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ) (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ) (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8411/65536 : ℝ)) 7 (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ) (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ) (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ) (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8411/65536 : ℝ))) (177696772509/1000000000000 : ℝ) (35539354503/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8411/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177696772509/1000000000000 : ℝ) (35539354503/200000000000 : ℝ) (294424193127/500000000000 : ℝ) (294424193129/500000000000 : ℝ) (210770474989/500000000000 : ℝ) (210770474993/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8411/65536 : ℝ))) 1 (294424193127/500000000000 : ℝ) (294424193129/500000000000 : ℝ) (210770474989/500000000000 : ℝ) (210770474993/500000000000 : ℝ) (126298667029/250000000000 : ℝ) (252597334061/500000000000 : ℝ) (249110270831/500000000000 : ℝ) (498220541669/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8411/65536 : ℝ))) 2 (126298667029/250000000000 : ℝ) (252597334061/500000000000 : ℝ) (249110270831/500000000000 : ℝ) (498220541669/1000000000000 : ℝ) (501707604889/1000000000000 : ℝ) (15678362653/31250000000 : ℝ) (250847743259/500000000000 : ℝ) (250847743263/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8411/65536 : ℝ))) 3 (501707604889/1000000000000 : ℝ) (15678362653/31250000000 : ℝ) (250847743259/500000000000 : ℝ) (250847743263/500000000000 : ℝ) (501701545703/1000000000000 : ℝ) (501701545711/1000000000000 : ℝ) (250850772833/500000000000 : ℝ) (20068061827/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8411/65536 : ℝ))) 4 (501701545703/1000000000000 : ℝ) (501701545711/1000000000000 : ℝ) (250850772833/500000000000 : ℝ) (20068061827/40000000000 : ℝ) (125425386421/250000000000 : ℝ) (501701545693/1000000000000 : ℝ) (125425386421/250000000000 : ℝ) (501701545693/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8411/65536 : ℝ))) 5 (125425386421/250000000000 : ℝ) (501701545693/1000000000000 : ℝ) (125425386421/250000000000 : ℝ) (501701545693/1000000000000 : ℝ) (125425386421/250000000000 : ℝ) (501701545693/1000000000000 : ℝ) (125425386421/250000000000 : ℝ) (501701545693/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8411/65536 : ℝ))) 6 (125425386421/250000000000 : ℝ) (501701545693/1000000000000 : ℝ) (125425386421/250000000000 : ℝ) (501701545693/1000000000000 : ℝ) (125425386421/250000000000 : ℝ) (501701545693/1000000000000 : ℝ) (125425386421/250000000000 : ℝ) (501701545693/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8411/65536 : ℝ))) 7 (125425386421/250000000000 : ℝ) (501701545693/1000000000000 : ℝ) (125425386421/250000000000 : ℝ) (501701545693/1000000000000 : ℝ) (125425386421/250000000000 : ℝ) (501701545693/1000000000000 : ℝ) (125425386421/250000000000 : ℝ) (501701545693/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8411/65536 : ℝ)) hmem 8 (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ) (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8411/65536 : ℝ))) hcmem 8 (125425386421/250000000000 : ℝ) (501701545693/1000000000000 : ℝ) (125425386421/250000000000 : ℝ) (501701545693/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8411/65536 : ℝ)) (198405337517/200000000000 : ℝ) (248006671897/250000000000 : ℝ) (125425386421/250000000000 : ℝ) (501701545693/1000000000000 : ℝ) (198601246057/250000000000 : ℝ) (397202492123/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1211_exp_lower
  have heNumeric : (2054900106891/1000000000000 : ℝ)/4 ≤ Real.exp (-42628295944869/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900106891/1000000000000 : ℝ)/4 ≤ Real.exp ((33643/262144 : ℝ)-(397202492123/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33643/262144 : ℝ) (8411/65536 : ℝ) (397202492123/500000000000 : ℝ) (2054900106891/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1212; no trusted numerical premise.
theorem cover8_leaf1212_exp_radius : (249499152798541043/250000000000000000 : ℝ) ≤ Real.exp ((-33645/2097152 : ℝ)/8) ∧ Real.exp ((-33645/2097152 : ℝ)/8) ≤ (997996611194164173/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33645/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1212_exp_lower : (920113369507390511/1000000000000000000 : ℝ) ≤ Real.exp ((-10657073767109/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657073767109/16000000000000 : ℝ)/8) ≤ (57507085594211907/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657073767109/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1212_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900135031/1000000000000 : ℝ) ≤ 4*Real.exp (8411/65536 : ℝ)*Real.exp (-mu (radius 8 (33645/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900135031/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33645/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1212_exp_radius
  have hrNumeric : (196816964053/200000000000 : ℝ) ≤ Real.exp (-33645/2097152 : ℝ) ∧ Real.exp (-33645/2097152 : ℝ) ≤ (492042410133/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196816964053/200000000000 : ℝ) ≤ (radius 8 (33645/262144 : ℝ)) ∧ (radius 8 (33645/262144 : ℝ)) ≤ (492042410133/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33645/262144 : ℝ)) (196816964053/200000000000 : ℝ) (492042410133/500000000000 : ℝ) (22212421399/125000000000 : ℝ) (88849685599/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33645/262144 : ℝ)) (196816964053/200000000000 : ℝ) (492042410133/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33645/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196816964053/200000000000 : ℝ) (492042410133/500000000000 : ℝ) (248010602533/250000000000 : ℝ) (992042410133/1000000000000 : ℝ) (992010494029/1000000000000 : ℝ) (992010494031/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33645/262144 : ℝ)) 1 (248010602533/250000000000 : ℝ) (992042410133/1000000000000 : ℝ) (992010494029/1000000000000 : ℝ) (992010494031/1000000000000 : ℝ) (12400330651/12500000000 : ℝ) (496013226041/500000000000 : ℝ) (62001653247/62500000000 : ℝ) (496013225977/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33645/262144 : ℝ)) 2 (12400330651/12500000000 : ℝ) (496013226041/500000000000 : ℝ) (62001653247/62500000000 : ℝ) (496013225977/500000000000 : ℝ) (62001653251/62500000000 : ℝ) (496013226009/500000000000 : ℝ) (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33645/262144 : ℝ)) 3 (62001653251/62500000000 : ℝ) (496013226009/500000000000 : ℝ) (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ) (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ) (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33645/262144 : ℝ)) 4 (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ) (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ) (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ) (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33645/262144 : ℝ)) 5 (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ) (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ) (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ) (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33645/262144 : ℝ)) 6 (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ) (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ) (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ) (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33645/262144 : ℝ)) 7 (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ) (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ) (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ) (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33645/262144 : ℝ))) (22212421399/125000000000 : ℝ) (88849685599/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33645/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22212421399/125000000000 : ℝ) (88849685599/500000000000 : ℝ) (147212421399/250000000000 : ℝ) (588849685599/1000000000000 : ℝ) (52693004041/125000000000 : ℝ) (26346502021/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33645/262144 : ℝ))) 1 (147212421399/250000000000 : ℝ) (588849685599/1000000000000 : ℝ) (52693004041/125000000000 : ℝ) (26346502021/62500000000 : ℝ) (252598429481/500000000000 : ℝ) (63149607371/125000000000 : ℝ) (249111456431/500000000000 : ℝ) (498222912869/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33645/262144 : ℝ))) 2 (252598429481/500000000000 : ℝ) (63149607371/125000000000 : ℝ) (249111456431/500000000000 : ℝ) (498222912869/1000000000000 : ℝ) (62713735739/125000000000 : ℝ) (501709885919/1000000000000 : ℝ) (501697768223/1000000000000 : ℝ) (501697768231/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33645/262144 : ℝ))) 3 (62713735739/125000000000 : ℝ) (501709885919/1000000000000 : ℝ) (501697768223/1000000000000 : ℝ) (501697768231/1000000000000 : ℝ) (501703827067/1000000000000 : ℝ) (20068153083/40000000000 : ℝ) (50170382703/100000000000 : ℝ) (501703827039/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33645/262144 : ℝ))) 4 (501703827067/1000000000000 : ℝ) (20068153083/40000000000 : ℝ) (50170382703/100000000000 : ℝ) (501703827039/1000000000000 : ℝ) (62712978381/125000000000 : ℝ) (501703827057/1000000000000 : ℝ) (62712978381/125000000000 : ℝ) (501703827057/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33645/262144 : ℝ))) 5 (62712978381/125000000000 : ℝ) (501703827057/1000000000000 : ℝ) (62712978381/125000000000 : ℝ) (501703827057/1000000000000 : ℝ) (62712978381/125000000000 : ℝ) (501703827057/1000000000000 : ℝ) (62712978381/125000000000 : ℝ) (501703827057/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33645/262144 : ℝ))) 6 (62712978381/125000000000 : ℝ) (501703827057/1000000000000 : ℝ) (62712978381/125000000000 : ℝ) (501703827057/1000000000000 : ℝ) (62712978381/125000000000 : ℝ) (501703827057/1000000000000 : ℝ) (62712978381/125000000000 : ℝ) (501703827057/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33645/262144 : ℝ))) 7 (62712978381/125000000000 : ℝ) (501703827057/1000000000000 : ℝ) (62712978381/125000000000 : ℝ) (501703827057/1000000000000 : ℝ) (62712978381/125000000000 : ℝ) (501703827057/1000000000000 : ℝ) (62712978381/125000000000 : ℝ) (501703827057/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33645/262144 : ℝ)) hmem 8 (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ) (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33645/262144 : ℝ))) hcmem 8 (62712978381/125000000000 : ℝ) (501703827057/1000000000000 : ℝ) (62712978381/125000000000 : ℝ) (501703827057/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33645/262144 : ℝ)) (198405290403/200000000000 : ℝ) (496013226009/500000000000 : ℝ) (62712978381/125000000000 : ℝ) (501703827057/1000000000000 : ℝ) (49650549077/62500000000 : ℝ) (794408785249/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1212_exp_lower
  have heNumeric : (2054900135031/1000000000000 : ℝ)/4 ≤ Real.exp (-10657073767109/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900135031/1000000000000 : ℝ)/4 ≤ Real.exp ((8411/65536 : ℝ)-(794408785249/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8411/65536 : ℝ) (33645/262144 : ℝ) (794408785249/1000000000000 : ℝ) (2054900135031/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1213; no trusted numerical premise.
theorem cover8_leaf1213_exp_radius : (997996551708932447/1000000000000000000 : ℝ) ≤ Real.exp ((-16823/1048576 : ℝ)/8) ∧ Real.exp ((-16823/1048576 : ℝ)/8) ≤ (31187392240904139/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16823/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1213_exp_lower : (460056685546043157/500000000000000000 : ℝ) ≤ Real.exp ((-42628294186627/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628294186627/64000000000000 : ℝ)/8) ≤ (184022674218417263/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628294186627/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1213_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431260209/62500000000 : ℝ) ≤ 4*Real.exp (33645/262144 : ℝ)*Real.exp (-mu (radius 8 (16823/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (128431260209/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16823/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1213_exp_radius
  have hrNumeric : (984084351017/1000000000000 : ℝ) ≤ Real.exp (-16823/1048576 : ℝ) ∧ Real.exp (-16823/1048576 : ℝ) ≤ (492042175509/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984084351017/1000000000000 : ℝ) ≤ (radius 8 (16823/131072 : ℝ)) ∧ (radius 8 (16823/131072 : ℝ)) ≤ (492042175509/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16823/131072 : ℝ)) (984084351017/1000000000000 : ℝ) (492042175509/500000000000 : ℝ) (17770196983/100000000000 : ℝ) (44425492459/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16823/131072 : ℝ)) (984084351017/1000000000000 : ℝ) (492042175509/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16823/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984084351017/1000000000000 : ℝ) (492042175509/500000000000 : ℝ) (248010543877/250000000000 : ℝ) (992042175509/1000000000000 : ℝ) (248002564379/250000000000 : ℝ) (992010257517/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16823/131072 : ℝ)) 1 (248010543877/250000000000 : ℝ) (992042175509/1000000000000 : ℝ) (248002564379/250000000000 : ℝ) (992010257517/1000000000000 : ℝ) (15500409633/15625000000 : ℝ) (992026216513/1000000000000 : ℝ) (992026216383/1000000000000 : ℝ) (198405243277/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16823/131072 : ℝ)) 2 (15500409633/15625000000 : ℝ) (992026216513/1000000000000 : ℝ) (992026216383/1000000000000 : ℝ) (198405243277/200000000000 : ℝ) (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ) (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16823/131072 : ℝ)) 3 (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ) (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ) (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ) (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16823/131072 : ℝ)) 4 (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ) (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ) (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ) (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16823/131072 : ℝ)) 5 (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ) (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ) (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ) (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16823/131072 : ℝ)) 6 (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ) (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ) (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ) (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16823/131072 : ℝ)) 7 (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ) (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ) (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ) (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16823/131072 : ℝ))) (17770196983/100000000000 : ℝ) (44425492459/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16823/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17770196983/100000000000 : ℝ) (44425492459/250000000000 : ℝ) (117770196983/200000000000 : ℝ) (294425492459/500000000000 : ℝ) (210773557301/500000000000 : ℝ) (42154711461/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16823/131072 : ℝ))) 1 (117770196983/200000000000 : ℝ) (294425492459/500000000000 : ℝ) (210773557301/500000000000 : ℝ) (42154711461/100000000000 : ℝ) (252599524879/500000000000 : ℝ) (126299762441/250000000000 : ℝ) (124556321001/250000000000 : ℝ) (498225284011/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16823/131072 : ℝ))) 2 (252599524879/500000000000 : ℝ) (126299762441/250000000000 : ℝ) (124556321001/250000000000 : ℝ) (498225284011/1000000000000 : ℝ) (501712166881/1000000000000 : ℝ) (62714020861/125000000000 : ℝ) (250850024937/500000000000 : ℝ) (250850024941/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16823/131072 : ℝ))) 3 (501712166881/1000000000000 : ℝ) (62714020861/125000000000 : ℝ) (250850024937/500000000000 : ℝ) (250850024941/500000000000 : ℝ) (501706108377/1000000000000 : ℝ) (100341221677/200000000000 : ℝ) (25085305417/50000000000 : ℝ) (501706108349/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16823/131072 : ℝ))) 4 (501706108377/1000000000000 : ℝ) (100341221677/200000000000 : ℝ) (25085305417/50000000000 : ℝ) (501706108349/1000000000000 : ℝ) (250853054179/500000000000 : ℝ) (501706108367/1000000000000 : ℝ) (250853054179/500000000000 : ℝ) (501706108367/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16823/131072 : ℝ))) 5 (250853054179/500000000000 : ℝ) (501706108367/1000000000000 : ℝ) (250853054179/500000000000 : ℝ) (501706108367/1000000000000 : ℝ) (250853054179/500000000000 : ℝ) (501706108367/1000000000000 : ℝ) (250853054179/500000000000 : ℝ) (501706108367/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16823/131072 : ℝ))) 6 (250853054179/500000000000 : ℝ) (501706108367/1000000000000 : ℝ) (250853054179/500000000000 : ℝ) (501706108367/1000000000000 : ℝ) (250853054179/500000000000 : ℝ) (501706108367/1000000000000 : ℝ) (250853054179/500000000000 : ℝ) (501706108367/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16823/131072 : ℝ))) 7 (250853054179/500000000000 : ℝ) (501706108367/1000000000000 : ℝ) (250853054179/500000000000 : ℝ) (501706108367/1000000000000 : ℝ) (250853054179/500000000000 : ℝ) (501706108367/1000000000000 : ℝ) (250853054179/500000000000 : ℝ) (501706108367/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16823/131072 : ℝ)) hmem 8 (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ) (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16823/131072 : ℝ))) hcmem 8 (250853054179/500000000000 : ℝ) (501706108367/1000000000000 : ℝ) (250853054179/500000000000 : ℝ) (501706108367/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16823/131072 : ℝ)) (992026216447/1000000000000 : ℝ) (992026216449/1000000000000 : ℝ) (250853054179/500000000000 : ℝ) (501706108367/1000000000000 : ℝ) (794412586151/1000000000000 : ℝ) (99301573271/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1213_exp_lower
  have heNumeric : (128431260209/62500000000 : ℝ)/4 ≤ Real.exp (-42628294186627/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431260209/62500000000 : ℝ)/4 ≤ Real.exp ((33645/262144 : ℝ)-(99301573271/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33645/262144 : ℝ) (16823/131072 : ℝ) (99301573271/125000000000 : ℝ) (128431260209/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1214; no trusted numerical premise.
theorem cover8_leaf1214_exp_radius : (249499123055926067/250000000000000000 : ℝ) ≤ Real.exp ((-33647/2097152 : ℝ)/8) ∧ Real.exp ((-33647/2097152 : ℝ)/8) ≤ (997996492223704269/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33647/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1214_exp_lower : (460056686342589077/500000000000000000 : ℝ) ≤ Real.exp ((-21314146650073/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314146650073/32000000000000 : ℝ)/8) ≤ (184022674537035631/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314146650073/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1214_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900191807/1000000000000 : ℝ) ≤ 4*Real.exp (16823/131072 : ℝ)*Real.exp (-mu (radius 8 (33647/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900191807/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33647/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1214_exp_radius
  have hrNumeric : (984083881769/1000000000000 : ℝ) ≤ Real.exp (-33647/2097152 : ℝ) ∧ Real.exp (-33647/2097152 : ℝ) ≤ (98408388177/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984083881769/1000000000000 : ℝ) ≤ (radius 8 (33647/262144 : ℝ)) ∧ (radius 8 (33647/262144 : ℝ)) ≤ (98408388177/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33647/262144 : ℝ)) (984083881769/1000000000000 : ℝ) (98408388177/100000000000 : ℝ) (44426142107/250000000000 : ℝ) (35540913687/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33647/262144 : ℝ)) (984083881769/1000000000000 : ℝ) (98408388177/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33647/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984083881769/1000000000000 : ℝ) (98408388177/100000000000 : ℝ) (248010485221/250000000000 : ℝ) (198408388177/200000000000 : ℝ) (496005010501/500000000000 : ℝ) (992010021003/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33647/262144 : ℝ)) 1 (248010485221/250000000000 : ℝ) (198408388177/200000000000 : ℝ) (496005010501/500000000000 : ℝ) (992010021003/1000000000000 : ℝ) (992025980943/1000000000000 : ℝ) (62001623809/62500000000 : ℝ) (496012990407/500000000000 : ℝ) (62001623801/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33647/262144 : ℝ)) 2 (992025980943/1000000000000 : ℝ) (62001623809/62500000000 : ℝ) (496012990407/500000000000 : ℝ) (62001623801/62500000000 : ℝ) (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ) (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33647/262144 : ℝ)) 3 (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ) (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ) (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ) (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33647/262144 : ℝ)) 4 (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ) (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ) (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ) (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33647/262144 : ℝ)) 5 (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ) (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ) (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ) (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33647/262144 : ℝ)) 6 (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ) (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ) (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ) (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33647/262144 : ℝ)) 7 (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ) (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ) (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ) (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33647/262144 : ℝ))) (44426142107/250000000000 : ℝ) (35540913687/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33647/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44426142107/250000000000 : ℝ) (35540913687/200000000000 : ℝ) (294426142107/500000000000 : ℝ) (294426142109/500000000000 : ℝ) (210775098403/500000000000 : ℝ) (26346887301/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33647/262144 : ℝ))) 1 (294426142107/500000000000 : ℝ) (294426142109/500000000000 : ℝ) (210775098403/500000000000 : ℝ) (26346887301/62500000000 : ℝ) (50520124051/100000000000 : ℝ) (505201240517/1000000000000 : ℝ) (498227655093/1000000000000 : ℝ) (249113827551/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33647/262144 : ℝ))) 2 (50520124051/100000000000 : ℝ) (505201240517/1000000000000 : ℝ) (498227655093/1000000000000 : ℝ) (249113827551/500000000000 : ℝ) (501714447801/1000000000000 : ℝ) (50171444781/100000000000 : ℝ) (125425582869/250000000000 : ℝ) (100340466297/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33647/262144 : ℝ))) 3 (501714447801/1000000000000 : ℝ) (50171444781/100000000000 : ℝ) (125425582869/250000000000 : ℝ) (100340466297/200000000000 : ℝ) (250854194819/500000000000 : ℝ) (31356774353/62500000000 : ℝ) (501708389601/1000000000000 : ℝ) (501708389611/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33647/262144 : ℝ))) 4 (250854194819/500000000000 : ℝ) (31356774353/62500000000 : ℝ) (501708389601/1000000000000 : ℝ) (501708389611/1000000000000 : ℝ) (501708389619/1000000000000 : ℝ) (50170838963/100000000000 : ℝ) (501708389619/1000000000000 : ℝ) (50170838963/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33647/262144 : ℝ))) 5 (501708389619/1000000000000 : ℝ) (50170838963/100000000000 : ℝ) (501708389619/1000000000000 : ℝ) (50170838963/100000000000 : ℝ) (501708389619/1000000000000 : ℝ) (50170838963/100000000000 : ℝ) (501708389619/1000000000000 : ℝ) (50170838963/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33647/262144 : ℝ))) 6 (501708389619/1000000000000 : ℝ) (50170838963/100000000000 : ℝ) (501708389619/1000000000000 : ℝ) (50170838963/100000000000 : ℝ) (501708389619/1000000000000 : ℝ) (50170838963/100000000000 : ℝ) (501708389619/1000000000000 : ℝ) (50170838963/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33647/262144 : ℝ))) 7 (501708389619/1000000000000 : ℝ) (50170838963/100000000000 : ℝ) (501708389619/1000000000000 : ℝ) (50170838963/100000000000 : ℝ) (501708389619/1000000000000 : ℝ) (50170838963/100000000000 : ℝ) (501708389619/1000000000000 : ℝ) (50170838963/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33647/262144 : ℝ)) hmem 8 (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ) (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33647/262144 : ℝ))) hcmem 8 (501708389619/1000000000000 : ℝ) (50170838963/100000000000 : ℝ) (501708389619/1000000000000 : ℝ) (50170838963/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33647/262144 : ℝ)) (496012990439/500000000000 : ℝ) (12400324761/12500000000 : ℝ) (501708389619/1000000000000 : ℝ) (50170838963/100000000000 : ℝ) (397208193497/500000000000 : ℝ) (397208193507/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1214_exp_lower
  have heNumeric : (2054900191807/1000000000000 : ℝ)/4 ≤ Real.exp (-21314146650073/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900191807/1000000000000 : ℝ)/4 ≤ Real.exp ((16823/131072 : ℝ)-(397208193507/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16823/131072 : ℝ) (33647/262144 : ℝ) (397208193507/500000000000 : ℝ) (2054900191807/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1215; no trusted numerical premise.
theorem cover8_leaf1215_exp_radius : (199599286547695927/200000000000000000 : ℝ) ≤ Real.exp ((-2103/131072 : ℝ)/8) ∧ Real.exp ((-2103/131072 : ℝ)/8) ≤ (249499108184619909/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2103/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1215_exp_lower : (920113374288046201/1000000000000000000 : ℝ) ≤ Real.exp ((-1705131696329/2560000000000 : ℝ)/8) ∧ Real.exp ((-1705131696329/2560000000000 : ℝ)/8) ≤ (460056687144023101/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1705131696329/2560000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1215_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725055111/250000000000 : ℝ) ≤ 4*Real.exp (33647/262144 : ℝ)*Real.exp (-mu (radius 8 (2103/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (513725055111/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2103/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1215_exp_radius
  have hrNumeric : (492041706261/500000000000 : ℝ) ≤ Real.exp (-2103/131072 : ℝ) ∧ Real.exp (-2103/131072 : ℝ) ≤ (984083412523/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492041706261/500000000000 : ℝ) ≤ (radius 8 (2103/16384 : ℝ)) ∧ (radius 8 (2103/16384 : ℝ)) ≤ (984083412523/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2103/16384 : ℝ)) (492041706261/500000000000 : ℝ) (984083412523/1000000000000 : ℝ) (88853583491/500000000000 : ℝ) (177707166989/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2103/16384 : ℝ)) (492041706261/500000000000 : ℝ) (984083412523/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2103/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492041706261/500000000000 : ℝ) (984083412523/1000000000000 : ℝ) (992041706261/1000000000000 : ℝ) (496020853131/500000000000 : ℝ) (992009784489/1000000000000 : ℝ) (99200978449/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2103/16384 : ℝ)) 1 (992041706261/1000000000000 : ℝ) (496020853131/500000000000 : ℝ) (992009784489/1000000000000 : ℝ) (99200978449/100000000000 : ℝ) (7936205963/8000000000 : ℝ) (31000804543/31250000000 : ℝ) (496012872623/500000000000 : ℝ) (31000804539/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2103/16384 : ℝ)) 2 (7936205963/8000000000 : ℝ) (31000804543/31250000000 : ℝ) (496012872623/500000000000 : ℝ) (31000804539/31250000000 : ℝ) (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ) (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2103/16384 : ℝ)) 3 (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ) (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ) (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ) (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2103/16384 : ℝ)) 4 (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ) (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ) (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ) (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2103/16384 : ℝ)) 5 (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ) (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ) (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ) (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2103/16384 : ℝ)) 6 (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ) (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ) (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ) (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2103/16384 : ℝ)) 7 (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ) (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ) (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ) (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2103/16384 : ℝ))) (88853583491/500000000000 : ℝ) (177707166989/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2103/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88853583491/500000000000 : ℝ) (177707166989/1000000000000 : ℝ) (588853583491/1000000000000 : ℝ) (117770716699/200000000000 : ℝ) (52694159867/125000000000 : ℝ) (84310655789/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2103/16384 : ℝ))) 1 (588853583491/1000000000000 : ℝ) (117770716699/200000000000 : ℝ) (52694159867/125000000000 : ℝ) (84310655789/200000000000 : ℝ) (505203431213/1000000000000 : ℝ) (25260171561/50000000000 : ℝ) (249115013063/500000000000 : ℝ) (249115013067/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2103/16384 : ℝ))) 2 (505203431213/1000000000000 : ℝ) (25260171561/50000000000 : ℝ) (249115013063/500000000000 : ℝ) (249115013067/500000000000 : ℝ) (501716728669/1000000000000 : ℝ) (501716728677/1000000000000 : ℝ) (250852306513/500000000000 : ℝ) (100340922607/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2103/16384 : ℝ))) 3 (501716728669/1000000000000 : ℝ) (501716728677/1000000000000 : ℝ) (250852306513/500000000000 : ℝ) (100340922607/200000000000 : ℝ) (501710670847/1000000000000 : ℝ) (62713833857/125000000000 : ℝ) (50171067081/100000000000 : ℝ) (25085533541/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2103/16384 : ℝ))) 4 (501710670847/1000000000000 : ℝ) (62713833857/125000000000 : ℝ) (50171067081/100000000000 : ℝ) (25085533541/50000000000 : ℝ) (125427667707/250000000000 : ℝ) (250855335419/500000000000 : ℝ) (125427667707/250000000000 : ℝ) (250855335419/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2103/16384 : ℝ))) 5 (125427667707/250000000000 : ℝ) (250855335419/500000000000 : ℝ) (125427667707/250000000000 : ℝ) (250855335419/500000000000 : ℝ) (125427667707/250000000000 : ℝ) (250855335419/500000000000 : ℝ) (125427667707/250000000000 : ℝ) (250855335419/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2103/16384 : ℝ))) 6 (125427667707/250000000000 : ℝ) (250855335419/500000000000 : ℝ) (125427667707/250000000000 : ℝ) (250855335419/500000000000 : ℝ) (125427667707/250000000000 : ℝ) (250855335419/500000000000 : ℝ) (125427667707/250000000000 : ℝ) (250855335419/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2103/16384 : ℝ))) 7 (125427667707/250000000000 : ℝ) (250855335419/500000000000 : ℝ) (125427667707/250000000000 : ℝ) (250855335419/500000000000 : ℝ) (125427667707/250000000000 : ℝ) (250855335419/500000000000 : ℝ) (125427667707/250000000000 : ℝ) (250855335419/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2103/16384 : ℝ)) hmem 8 (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ) (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2103/16384 : ℝ))) hcmem 8 (125427667707/250000000000 : ℝ) (250855335419/500000000000 : ℝ) (125427667707/250000000000 : ℝ) (250855335419/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2103/16384 : ℝ)) (99202574531/100000000000 : ℝ) (31000804541/31250000000 : ℝ) (125427667707/250000000000 : ℝ) (250855335419/500000000000 : ℝ) (198605046939/250000000000 : ℝ) (31776807511/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1215_exp_lower
  have heNumeric : (513725055111/250000000000 : ℝ)/4 ≤ Real.exp (-1705131696329/2560000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725055111/250000000000 : ℝ)/4 ≤ Real.exp ((33647/262144 : ℝ)-(31776807511/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33647/262144 : ℝ) (2103/16384 : ℝ) (31776807511/40000000000 : ℝ) (513725055111/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1216; no trusted numerical premise.
theorem cover8_leaf1216_exp_radius : (997996373253258547/1000000000000000000 : ℝ) ≤ Real.exp ((-33649/2097152 : ℝ)/8) ∧ Real.exp ((-33649/2097152 : ℝ)/8) ≤ (249499093313314637/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33649/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1216_exp_lower : (230028343974597543/250000000000000000 : ℝ) ≤ Real.exp ((-2664268219509/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664268219509/4000000000000 : ℝ)/8) ≤ (920113375898390173/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664268219509/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1216_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (16053908197/7812500000 : ℝ) ≤ 4*Real.exp (2103/16384 : ℝ)*Real.exp (-mu (radius 8 (33649/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (16053908197/7812500000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33649/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1216_exp_radius
  have hrNumeric : (492041471637/500000000000 : ℝ) ≤ Real.exp (-33649/2097152 : ℝ) ∧ Real.exp (-33649/2097152 : ℝ) ≤ (39363317731/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492041471637/500000000000 : ℝ) ≤ (radius 8 (33649/262144 : ℝ)) ∧ (radius 8 (33649/262144 : ℝ)) ≤ (39363317731/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33649/262144 : ℝ)) (492041471637/500000000000 : ℝ) (39363317731/40000000000 : ℝ) (177709765503/1000000000000 : ℝ) (177709765509/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33649/262144 : ℝ)) (492041471637/500000000000 : ℝ) (39363317731/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33649/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492041471637/500000000000 : ℝ) (39363317731/40000000000 : ℝ) (992041471637/1000000000000 : ℝ) (496020735819/500000000000 : ℝ) (39680381919/40000000000 : ℝ) (124001193497/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33649/262144 : ℝ)) 1 (992041471637/1000000000000 : ℝ) (496020735819/500000000000 : ℝ) (39680381919/40000000000 : ℝ) (124001193497/125000000000 : ℝ) (496012754903/500000000000 : ℝ) (992025509807/1000000000000 : ℝ) (992025509677/1000000000000 : ℝ) (992025509679/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33649/262144 : ℝ)) 2 (496012754903/500000000000 : ℝ) (992025509807/1000000000000 : ℝ) (992025509677/1000000000000 : ℝ) (992025509679/1000000000000 : ℝ) (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ) (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33649/262144 : ℝ)) 3 (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ) (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ) (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ) (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33649/262144 : ℝ)) 4 (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ) (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ) (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ) (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33649/262144 : ℝ)) 5 (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ) (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ) (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ) (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33649/262144 : ℝ)) 6 (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ) (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ) (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ) (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33649/262144 : ℝ)) 7 (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ) (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ) (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ) (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33649/262144 : ℝ))) (177709765503/1000000000000 : ℝ) (177709765509/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33649/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177709765503/1000000000000 : ℝ) (177709765509/1000000000000 : ℝ) (588854882751/1000000000000 : ℝ) (117770976551/200000000000 : ℝ) (105389090251/250000000000 : ℝ) (105389090253/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33649/262144 : ℝ))) 1 (588854882751/1000000000000 : ℝ) (117770976551/200000000000 : ℝ) (105389090251/250000000000 : ℝ) (105389090253/250000000000 : ℝ) (505205621877/1000000000000 : ℝ) (126301405471/250000000000 : ℝ) (498232397111/1000000000000 : ℝ) (498232397119/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33649/262144 : ℝ))) 2 (505205621877/1000000000000 : ℝ) (126301405471/250000000000 : ℝ) (498232397111/1000000000000 : ℝ) (498232397119/1000000000000 : ℝ) (250859504747/500000000000 : ℝ) (250859504751/500000000000 : ℝ) (125426723633/250000000000 : ℝ) (501706894541/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33649/262144 : ℝ))) 3 (250859504747/500000000000 : ℝ) (250859504751/500000000000 : ℝ) (125426723633/250000000000 : ℝ) (501706894541/1000000000000 : ℝ) (501712952013/1000000000000 : ℝ) (250856476011/500000000000 : ℝ) (62714118997/125000000000 : ℝ) (100342590397/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33649/262144 : ℝ))) 4 (501712952013/1000000000000 : ℝ) (250856476011/500000000000 : ℝ) (62714118997/125000000000 : ℝ) (100342590397/200000000000 : ℝ) (250856475997/500000000000 : ℝ) (125428238001/250000000000 : ℝ) (250856475997/500000000000 : ℝ) (125428238001/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33649/262144 : ℝ))) 5 (250856475997/500000000000 : ℝ) (125428238001/250000000000 : ℝ) (250856475997/500000000000 : ℝ) (125428238001/250000000000 : ℝ) (250856475997/500000000000 : ℝ) (125428238001/250000000000 : ℝ) (250856475997/500000000000 : ℝ) (125428238001/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33649/262144 : ℝ))) 6 (250856475997/500000000000 : ℝ) (125428238001/250000000000 : ℝ) (250856475997/500000000000 : ℝ) (125428238001/250000000000 : ℝ) (250856475997/500000000000 : ℝ) (125428238001/250000000000 : ℝ) (250856475997/500000000000 : ℝ) (125428238001/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33649/262144 : ℝ))) 7 (250856475997/500000000000 : ℝ) (125428238001/250000000000 : ℝ) (250856475997/500000000000 : ℝ) (125428238001/250000000000 : ℝ) (250856475997/500000000000 : ℝ) (125428238001/250000000000 : ℝ) (250856475997/500000000000 : ℝ) (125428238001/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33649/262144 : ℝ)) hmem 8 (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ) (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33649/262144 : ℝ))) hcmem 8 (250856475997/500000000000 : ℝ) (125428238001/250000000000 : ℝ) (250856475997/500000000000 : ℝ) (125428238001/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33649/262144 : ℝ)) (992025509741/1000000000000 : ℝ) (992025509743/1000000000000 : ℝ) (250856475997/500000000000 : ℝ) (125428238001/250000000000 : ℝ) (794423988453/1000000000000 : ℝ) (794423988471/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1216_exp_lower
  have heNumeric : (16053908197/7812500000 : ℝ)/4 ≤ Real.exp (-2664268219509/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (16053908197/7812500000 : ℝ)/4 ≤ Real.exp ((2103/16384 : ℝ)-(794423988471/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2103/16384 : ℝ) (33649/262144 : ℝ) (794423988471/1000000000000 : ℝ) (16053908197/7812500000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1217; no trusted numerical premise.
theorem cover8_leaf1217_exp_radius : (199599262753608201/200000000000000000 : ℝ) ≤ Real.exp ((-16825/1048576 : ℝ)/8) ∧ Real.exp ((-16825/1048576 : ℝ)/8) ≤ (498998156884020503/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16825/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1217_exp_lower : (920113377518280323/1000000000000000000 : ℝ) ≤ Real.exp ((-42628290610751/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628290610751/64000000000000 : ℝ)/8) ≤ (230028344379570081/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628290610751/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1217_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900278157/1000000000000 : ℝ) ≤ 4*Real.exp (33649/262144 : ℝ)*Real.exp (-mu (radius 8 (16825/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900278157/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16825/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1217_exp_radius
  have hrNumeric : (984082474027/1000000000000 : ℝ) ≤ Real.exp (-16825/1048576 : ℝ) ∧ Real.exp (-16825/1048576 : ℝ) ≤ (246020618507/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984082474027/1000000000000 : ℝ) ≤ (radius 8 (16825/131072 : ℝ)) ∧ (radius 8 (16825/131072 : ℝ)) ≤ (246020618507/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16825/131072 : ℝ)) (984082474027/1000000000000 : ℝ) (246020618507/250000000000 : ℝ) (88856181989/500000000000 : ℝ) (35542472797/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16825/131072 : ℝ)) (984082474027/1000000000000 : ℝ) (246020618507/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16825/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984082474027/1000000000000 : ℝ) (246020618507/250000000000 : ℝ) (992041237013/1000000000000 : ℝ) (496020618507/500000000000 : ℝ) (992009311461/1000000000000 : ℝ) (992009311463/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16825/131072 : ℝ)) 1 (992041237013/1000000000000 : ℝ) (496020618507/500000000000 : ℝ) (992009311461/1000000000000 : ℝ) (992009311463/1000000000000 : ℝ) (992025274237/1000000000000 : ℝ) (992025274239/1000000000000 : ℝ) (248006318527/250000000000 : ℝ) (992025274111/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16825/131072 : ℝ)) 2 (992025274237/1000000000000 : ℝ) (992025274239/1000000000000 : ℝ) (248006318527/250000000000 : ℝ) (992025274111/1000000000000 : ℝ) (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ) (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16825/131072 : ℝ)) 3 (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ) (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ) (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ) (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16825/131072 : ℝ)) 4 (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ) (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ) (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ) (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16825/131072 : ℝ)) 5 (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ) (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ) (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ) (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16825/131072 : ℝ)) 6 (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ) (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ) (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ) (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16825/131072 : ℝ)) 7 (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ) (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ) (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ) (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16825/131072 : ℝ))) (88856181989/500000000000 : ℝ) (35542472797/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16825/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88856181989/500000000000 : ℝ) (35542472797/200000000000 : ℝ) (588856181989/1000000000000 : ℝ) (588856181993/1000000000000 : ℝ) (210779721497/500000000000 : ℝ) (105389860751/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16825/131072 : ℝ))) 1 (588856181989/1000000000000 : ℝ) (588856181993/1000000000000 : ℝ) (210779721497/500000000000 : ℝ) (105389860751/250000000000 : ℝ) (505207812491/1000000000000 : ℝ) (505207812499/1000000000000 : ℝ) (249117384019/500000000000 : ℝ) (498234768047/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16825/131072 : ℝ))) 2 (505207812491/1000000000000 : ℝ) (505207812499/1000000000000 : ℝ) (249117384019/500000000000 : ℝ) (498234768047/1000000000000 : ℝ) (62715161283/125000000000 : ℝ) (501721290273/1000000000000 : ℝ) (31356823499/62500000000 : ℝ) (250854587997/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16825/131072 : ℝ))) 3 (62715161283/125000000000 : ℝ) (501721290273/1000000000000 : ℝ) (31356823499/62500000000 : ℝ) (250854587997/500000000000 : ℝ) (125428808281/250000000000 : ℝ) (250857616567/500000000000 : ℝ) (501715233087/1000000000000 : ℝ) (501715233097/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16825/131072 : ℝ))) 4 (125428808281/250000000000 : ℝ) (250857616567/500000000000 : ℝ) (501715233087/1000000000000 : ℝ) (501715233097/1000000000000 : ℝ) (100343046621/200000000000 : ℝ) (125428808279/250000000000 : ℝ) (100343046621/200000000000 : ℝ) (125428808279/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16825/131072 : ℝ))) 5 (100343046621/200000000000 : ℝ) (125428808279/250000000000 : ℝ) (100343046621/200000000000 : ℝ) (125428808279/250000000000 : ℝ) (100343046621/200000000000 : ℝ) (125428808279/250000000000 : ℝ) (100343046621/200000000000 : ℝ) (125428808279/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16825/131072 : ℝ))) 6 (100343046621/200000000000 : ℝ) (125428808279/250000000000 : ℝ) (100343046621/200000000000 : ℝ) (125428808279/250000000000 : ℝ) (100343046621/200000000000 : ℝ) (125428808279/250000000000 : ℝ) (100343046621/200000000000 : ℝ) (125428808279/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16825/131072 : ℝ))) 7 (100343046621/200000000000 : ℝ) (125428808279/250000000000 : ℝ) (100343046621/200000000000 : ℝ) (125428808279/250000000000 : ℝ) (100343046621/200000000000 : ℝ) (125428808279/250000000000 : ℝ) (100343046621/200000000000 : ℝ) (125428808279/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16825/131072 : ℝ)) hmem 8 (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ) (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16825/131072 : ℝ))) hcmem 8 (100343046621/200000000000 : ℝ) (125428808279/250000000000 : ℝ) (100343046621/200000000000 : ℝ) (125428808279/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16825/131072 : ℝ)) (248006318543/250000000000 : ℝ) (39681010967/40000000000 : ℝ) (100343046621/200000000000 : ℝ) (125428808279/250000000000 : ℝ) (794427789063/1000000000000 : ℝ) (198606947271/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1217_exp_lower
  have heNumeric : (2054900278157/1000000000000 : ℝ)/4 ≤ Real.exp (-42628290610751/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900278157/1000000000000 : ℝ)/4 ≤ Real.exp ((33649/262144 : ℝ)-(198606947271/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33649/262144 : ℝ) (16825/131072 : ℝ) (198606947271/250000000000 : ℝ) (2054900278157/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1218; no trusted numerical premise.
theorem cover8_leaf1218_exp_radius : (997996254282827009/1000000000000000000 : ℝ) ≤ Real.exp ((-33651/2097152 : ℝ)/8) ∧ Real.exp ((-33651/2097152 : ℝ)/8) ≤ (99799625428282701/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33651/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1218_exp_lower : (920113379147141581/1000000000000000000 : ℝ) ≤ Real.exp ((-21314144852183/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314144852183/32000000000000 : ℝ)/8) ≤ (460056689573570791/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314144852183/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1218_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900307259/1000000000000 : ℝ) ≤ 4*Real.exp (16825/131072 : ℝ)*Real.exp (-mu (radius 8 (33651/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900307259/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33651/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1218_exp_radius
  have hrNumeric : (49204100239/50000000000 : ℝ) ≤ Real.exp (-33651/2097152 : ℝ) ∧ Real.exp (-33651/2097152 : ℝ) ≤ (984082004781/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49204100239/50000000000 : ℝ) ≤ (radius 8 (33651/262144 : ℝ)) ∧ (radius 8 (33651/262144 : ℝ)) ≤ (984082004781/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33651/262144 : ℝ)) (49204100239/50000000000 : ℝ) (984082004781/1000000000000 : ℝ) (35542992483/200000000000 : ℝ) (177714962421/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33651/262144 : ℝ)) (49204100239/50000000000 : ℝ) (984082004781/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33651/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49204100239/50000000000 : ℝ) (984082004781/1000000000000 : ℝ) (99204100239/100000000000 : ℝ) (992041002391/1000000000000 : ℝ) (248002268737/250000000000 : ℝ) (992009074949/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33651/262144 : ℝ)) 1 (99204100239/100000000000 : ℝ) (992041002391/1000000000000 : ℝ) (248002268737/250000000000 : ℝ) (992009074949/1000000000000 : ℝ) (992025038669/1000000000000 : ℝ) (99202503867/100000000000 : ℝ) (49601251927/50000000000 : ℝ) (496012519271/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33651/262144 : ℝ)) 2 (992025038669/1000000000000 : ℝ) (99202503867/100000000000 : ℝ) (49601251927/50000000000 : ℝ) (496012519271/500000000000 : ℝ) (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ) (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33651/262144 : ℝ)) 3 (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ) (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ) (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ) (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33651/262144 : ℝ)) 4 (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ) (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ) (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ) (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33651/262144 : ℝ)) 5 (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ) (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ) (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ) (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33651/262144 : ℝ)) 6 (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ) (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ) (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ) (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33651/262144 : ℝ)) 7 (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ) (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ) (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ) (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33651/262144 : ℝ))) (35542992483/200000000000 : ℝ) (177714962421/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33651/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35542992483/200000000000 : ℝ) (177714962421/1000000000000 : ℝ) (588857481207/1000000000000 : ℝ) (588857481211/1000000000000 : ℝ) (421562524917/1000000000000 : ℝ) (16862500997/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33651/262144 : ℝ))) 1 (588857481207/1000000000000 : ℝ) (588857481211/1000000000000 : ℝ) (421562524917/1000000000000 : ℝ) (16862500997/40000000000 : ℝ) (252605001531/500000000000 : ℝ) (126302500767/250000000000 : ℝ) (249118569457/500000000000 : ℝ) (249118569461/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33651/262144 : ℝ))) 2 (252605001531/500000000000 : ℝ) (126302500767/250000000000 : ℝ) (249118569457/500000000000 : ℝ) (249118569461/500000000000 : ℝ) (125430892747/250000000000 : ℝ) (100344714199/200000000000 : ℝ) (501711457389/1000000000000 : ℝ) (501711457397/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33651/262144 : ℝ))) 3 (125430892747/250000000000 : ℝ) (100344714199/200000000000 : ℝ) (501711457389/1000000000000 : ℝ) (501711457397/1000000000000 : ℝ) (125429378547/250000000000 : ℝ) (125429378549/250000000000 : ℝ) (501717514151/1000000000000 : ℝ) (6271468927/12500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33651/262144 : ℝ))) 4 (125429378547/250000000000 : ℝ) (125429378549/250000000000 : ℝ) (501717514151/1000000000000 : ℝ) (6271468927/12500000000 : ℝ) (501717514169/1000000000000 : ℝ) (250858757089/500000000000 : ℝ) (501717514169/1000000000000 : ℝ) (250858757089/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33651/262144 : ℝ))) 5 (501717514169/1000000000000 : ℝ) (250858757089/500000000000 : ℝ) (501717514169/1000000000000 : ℝ) (250858757089/500000000000 : ℝ) (501717514169/1000000000000 : ℝ) (250858757089/500000000000 : ℝ) (501717514169/1000000000000 : ℝ) (250858757089/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33651/262144 : ℝ))) 6 (501717514169/1000000000000 : ℝ) (250858757089/500000000000 : ℝ) (501717514169/1000000000000 : ℝ) (250858757089/500000000000 : ℝ) (501717514169/1000000000000 : ℝ) (250858757089/500000000000 : ℝ) (501717514169/1000000000000 : ℝ) (250858757089/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33651/262144 : ℝ))) 7 (501717514169/1000000000000 : ℝ) (250858757089/500000000000 : ℝ) (501717514169/1000000000000 : ℝ) (250858757089/500000000000 : ℝ) (501717514169/1000000000000 : ℝ) (250858757089/500000000000 : ℝ) (501717514169/1000000000000 : ℝ) (250858757089/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33651/262144 : ℝ)) hmem 8 (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ) (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33651/262144 : ℝ))) hcmem 8 (501717514169/1000000000000 : ℝ) (250858757089/500000000000 : ℝ) (501717514169/1000000000000 : ℝ) (250858757089/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33651/262144 : ℝ)) (248006259651/250000000000 : ℝ) (496012519303/500000000000 : ℝ) (501717514169/1000000000000 : ℝ) (250858757089/500000000000 : ℝ) (397215794801/500000000000 : ℝ) (794431589619/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1218_exp_lower
  have heNumeric : (2054900307259/1000000000000 : ℝ)/4 ≤ Real.exp (-21314144852183/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900307259/1000000000000 : ℝ)/4 ≤ Real.exp ((16825/131072 : ℝ)-(794431589619/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16825/131072 : ℝ) (33651/262144 : ℝ) (794431589619/1000000000000 : ℝ) (2054900307259/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1219; no trusted numerical premise.
theorem cover8_leaf1219_exp_radius : (498998097398808279/500000000000000000 : ℝ) ≤ Real.exp ((-8413/524288 : ℝ)/8) ∧ Real.exp ((-8413/524288 : ℝ)/8) ≤ (997996194797616559/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8413/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1219_exp_lower : (920113380784283863/1000000000000000000 : ℝ) ≤ Real.exp ((-42628288793373/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628288793373/64000000000000 : ℝ)/8) ≤ (115014172598035483/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628288793373/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1219_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900336509/1000000000000 : ℝ) ≤ 4*Real.exp (33651/262144 : ℝ)*Real.exp (-mu (radius 8 (8413/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900336509/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8413/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1219_exp_radius
  have hrNumeric : (984081535533/1000000000000 : ℝ) ≤ Real.exp (-8413/524288 : ℝ) ∧ Real.exp (-8413/524288 : ℝ) ≤ (492040767767/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984081535533/1000000000000 : ℝ) ≤ (radius 8 (8413/65536 : ℝ)) ∧ (radius 8 (8413/65536 : ℝ)) ≤ (492040767767/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8413/65536 : ℝ)) (984081535533/1000000000000 : ℝ) (492040767767/500000000000 : ℝ) (44429390203/250000000000 : ℝ) (88858780409/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8413/65536 : ℝ)) (984081535533/1000000000000 : ℝ) (492040767767/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8413/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984081535533/1000000000000 : ℝ) (492040767767/500000000000 : ℝ) (496020383883/500000000000 : ℝ) (992040767767/1000000000000 : ℝ) (496004419217/500000000000 : ℝ) (248002209609/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8413/65536 : ℝ)) 1 (496020383883/500000000000 : ℝ) (992040767767/1000000000000 : ℝ) (496004419217/500000000000 : ℝ) (248002209609/250000000000 : ℝ) (9920248031/10000000000 : ℝ) (496012401551/500000000000 : ℝ) (992024802971/1000000000000 : ℝ) (496012401487/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8413/65536 : ℝ)) 2 (9920248031/10000000000 : ℝ) (496012401551/500000000000 : ℝ) (992024802971/1000000000000 : ℝ) (496012401487/500000000000 : ℝ) (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ) (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8413/65536 : ℝ)) 3 (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ) (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ) (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ) (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8413/65536 : ℝ)) 4 (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ) (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ) (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ) (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8413/65536 : ℝ)) 5 (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ) (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ) (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ) (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8413/65536 : ℝ)) 6 (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ) (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ) (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ) (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8413/65536 : ℝ)) 7 (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ) (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ) (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ) (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8413/65536 : ℝ))) (44429390203/250000000000 : ℝ) (88858780409/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8413/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44429390203/250000000000 : ℝ) (88858780409/500000000000 : ℝ) (294429390203/500000000000 : ℝ) (588858780409/1000000000000 : ℝ) (42156560677/100000000000 : ℝ) (210782803389/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8413/65536 : ℝ))) 1 (294429390203/500000000000 : ℝ) (588858780409/1000000000000 : ℝ) (42156560677/100000000000 : ℝ) (210782803389/500000000000 : ℝ) (126303048397/250000000000 : ℝ) (252606096797/500000000000 : ℝ) (498239509737/1000000000000 : ℝ) (31139969359/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8413/65536 : ℝ))) 2 (126303048397/250000000000 : ℝ) (252606096797/500000000000 : ℝ) (498239509737/1000000000000 : ℝ) (31139969359/62500000000 : ℝ) (250862925831/500000000000 : ℝ) (501725851669/1000000000000 : ℝ) (100342747749/200000000000 : ℝ) (501713738753/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8413/65536 : ℝ))) 3 (250862925831/500000000000 : ℝ) (501725851669/1000000000000 : ℝ) (100342747749/200000000000 : ℝ) (501713738753/1000000000000 : ℝ) (501719795203/1000000000000 : ℝ) (501719795211/1000000000000 : ℝ) (250859897583/500000000000 : ℝ) (20068791807/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8413/65536 : ℝ))) 4 (501719795203/1000000000000 : ℝ) (501719795211/1000000000000 : ℝ) (250859897583/500000000000 : ℝ) (20068791807/40000000000 : ℝ) (31357487199/62500000000 : ℝ) (501719795193/1000000000000 : ℝ) (31357487199/62500000000 : ℝ) (501719795193/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8413/65536 : ℝ))) 5 (31357487199/62500000000 : ℝ) (501719795193/1000000000000 : ℝ) (31357487199/62500000000 : ℝ) (501719795193/1000000000000 : ℝ) (31357487199/62500000000 : ℝ) (501719795193/1000000000000 : ℝ) (31357487199/62500000000 : ℝ) (501719795193/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8413/65536 : ℝ))) 6 (31357487199/62500000000 : ℝ) (501719795193/1000000000000 : ℝ) (31357487199/62500000000 : ℝ) (501719795193/1000000000000 : ℝ) (31357487199/62500000000 : ℝ) (501719795193/1000000000000 : ℝ) (31357487199/62500000000 : ℝ) (501719795193/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8413/65536 : ℝ))) 7 (31357487199/62500000000 : ℝ) (501719795193/1000000000000 : ℝ) (31357487199/62500000000 : ℝ) (501719795193/1000000000000 : ℝ) (31357487199/62500000000 : ℝ) (501719795193/1000000000000 : ℝ) (31357487199/62500000000 : ℝ) (501719795193/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8413/65536 : ℝ)) hmem 8 (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ) (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8413/65536 : ℝ))) hcmem 8 (31357487199/62500000000 : ℝ) (501719795193/1000000000000 : ℝ) (31357487199/62500000000 : ℝ) (501719795193/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8413/65536 : ℝ)) (198404960607/200000000000 : ℝ) (496012401519/500000000000 : ℝ) (31357487199/62500000000 : ℝ) (501719795193/1000000000000 : ℝ) (49652211879/62500000000 : ℝ) (397217695041/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1219_exp_lower
  have heNumeric : (2054900336509/1000000000000 : ℝ)/4 ≤ Real.exp (-42628288793373/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900336509/1000000000000 : ℝ)/4 ≤ Real.exp ((33651/262144 : ℝ)-(397217695041/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33651/262144 : ℝ) (8413/65536 : ℝ) (397217695041/500000000000 : ℝ) (2054900336509/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1220; no trusted numerical premise.
theorem cover8_leaf1220_exp_radius : (997996135312409653/1000000000000000000 : ℝ) ≤ Real.exp ((-33653/2097152 : ℝ)/8) ∧ Real.exp ((-33653/2097152 : ℝ)/8) ≤ (498998067656204827/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33653/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1220_exp_lower : (460056691215313641/500000000000000000 : ℝ) ≤ Real.exp ((-2131414393863/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131414393863/3200000000000 : ℝ)/8) ≤ (920113382430627283/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131414393863/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1220_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725091481/250000000000 : ℝ) ≤ 4*Real.exp (8413/65536 : ℝ)*Real.exp (-mu (radius 8 (33653/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725091481/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33653/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1220_exp_radius
  have hrNumeric : (984081066287/1000000000000 : ℝ) ≤ Real.exp (-33653/2097152 : ℝ) ∧ Real.exp (-33653/2097152 : ℝ) ≤ (61505066643/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984081066287/1000000000000 : ℝ) ≤ (radius 8 (33653/262144 : ℝ)) ∧ (radius 8 (33653/262144 : ℝ)) ≤ (61505066643/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33653/262144 : ℝ)) (984081066287/1000000000000 : ℝ) (61505066643/62500000000 : ℝ) (44430039791/250000000000 : ℝ) (177720159171/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33653/262144 : ℝ)) (984081066287/1000000000000 : ℝ) (61505066643/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33653/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984081066287/1000000000000 : ℝ) (61505066643/62500000000 : ℝ) (992040533143/1000000000000 : ℝ) (124005066643/125000000000 : ℝ) (992008601921/1000000000000 : ℝ) (992008601923/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33653/262144 : ℝ)) 1 (992040533143/1000000000000 : ℝ) (124005066643/125000000000 : ℝ) (992008601921/1000000000000 : ℝ) (992008601923/1000000000000 : ℝ) (248006141883/250000000000 : ℝ) (496012283767/500000000000 : ℝ) (992024567403/1000000000000 : ℝ) (496012283703/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33653/262144 : ℝ)) 2 (248006141883/250000000000 : ℝ) (496012283767/500000000000 : ℝ) (992024567403/1000000000000 : ℝ) (496012283703/500000000000 : ℝ) (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ) (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33653/262144 : ℝ)) 3 (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ) (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ) (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ) (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33653/262144 : ℝ)) 4 (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ) (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ) (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ) (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33653/262144 : ℝ)) 5 (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ) (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ) (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ) (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33653/262144 : ℝ)) 6 (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ) (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ) (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ) (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33653/262144 : ℝ)) 7 (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ) (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ) (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ) (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33653/262144 : ℝ))) (44430039791/250000000000 : ℝ) (177720159171/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33653/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44430039791/250000000000 : ℝ) (177720159171/1000000000000 : ℝ) (294430039791/500000000000 : ℝ) (294430039793/500000000000 : ℝ) (421568688547/1000000000000 : ℝ) (421568688557/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33653/262144 : ℝ))) 1 (294430039791/500000000000 : ℝ) (294430039793/500000000000 : ℝ) (421568688547/1000000000000 : ℝ) (421568688557/1000000000000 : ℝ) (7893974751/15625000000 : ℝ) (63151798009/125000000000 : ℝ) (249120940251/500000000000 : ℝ) (498241880511/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33653/262144 : ℝ))) 2 (7893974751/15625000000 : ℝ) (63151798009/125000000000 : ℝ) (249120940251/500000000000 : ℝ) (498241880511/1000000000000 : ℝ) (501728132283/1000000000000 : ℝ) (125432033073/250000000000 : ℝ) (501716020047/1000000000000 : ℝ) (501716020057/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33653/262144 : ℝ))) 3 (501728132283/1000000000000 : ℝ) (125432033073/250000000000 : ℝ) (501716020047/1000000000000 : ℝ) (501716020057/1000000000000 : ℝ) (100344415233/200000000000 : ℝ) (20068883047/40000000000 : ℝ) (15678814879/31250000000 : ℝ) (250861038069/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33653/262144 : ℝ))) 4 (100344415233/200000000000 : ℝ) (20068883047/40000000000 : ℝ) (15678814879/31250000000 : ℝ) (250861038069/500000000000 : ℝ) (250861038073/500000000000 : ℝ) (501722076157/1000000000000 : ℝ) (250861038073/500000000000 : ℝ) (501722076157/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33653/262144 : ℝ))) 5 (250861038073/500000000000 : ℝ) (501722076157/1000000000000 : ℝ) (250861038073/500000000000 : ℝ) (501722076157/1000000000000 : ℝ) (250861038073/500000000000 : ℝ) (501722076157/1000000000000 : ℝ) (250861038073/500000000000 : ℝ) (501722076157/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33653/262144 : ℝ))) 6 (250861038073/500000000000 : ℝ) (501722076157/1000000000000 : ℝ) (250861038073/500000000000 : ℝ) (501722076157/1000000000000 : ℝ) (250861038073/500000000000 : ℝ) (501722076157/1000000000000 : ℝ) (250861038073/500000000000 : ℝ) (501722076157/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33653/262144 : ℝ))) 7 (250861038073/500000000000 : ℝ) (501722076157/1000000000000 : ℝ) (250861038073/500000000000 : ℝ) (501722076157/1000000000000 : ℝ) (250861038073/500000000000 : ℝ) (501722076157/1000000000000 : ℝ) (250861038073/500000000000 : ℝ) (501722076157/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33653/262144 : ℝ)) hmem 8 (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ) (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33653/262144 : ℝ))) hcmem 8 (250861038073/500000000000 : ℝ) (501722076157/1000000000000 : ℝ) (250861038073/500000000000 : ℝ) (501722076157/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33653/262144 : ℝ)) (992024567467/1000000000000 : ℝ) (99202456747/100000000000 : ℝ) (250861038073/500000000000 : ℝ) (501722076157/1000000000000 : ℝ) (198609797611/250000000000 : ℝ) (158887838093/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1220_exp_lower
  have heNumeric : (513725091481/250000000000 : ℝ)/4 ≤ Real.exp (-2131414393863/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725091481/250000000000 : ℝ)/4 ≤ Real.exp ((8413/65536 : ℝ)-(158887838093/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8413/65536 : ℝ) (33653/262144 : ℝ) (158887838093/200000000000 : ℝ) (513725091481/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1221; no trusted numerical premise.
theorem cover8_leaf1221_exp_radius : (997996075827206293/1000000000000000000 : ℝ) ≤ Real.exp ((-16827/1048576 : ℝ)/8) ∧ Real.exp ((-16827/1048576 : ℝ)/8) ≤ (498998037913603147/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16827/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1221_exp_lower : (460056692042683369/500000000000000000 : ℝ) ≤ Real.exp ((-1705131478259/2560000000000 : ℝ)/8) ∧ Real.exp ((-1705131478259/2560000000000 : ℝ)/8) ≤ (920113384085366739/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1705131478259/2560000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1221_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (64215637359/31250000000 : ℝ) ≤ 4*Real.exp (33653/262144 : ℝ)*Real.exp (-mu (radius 8 (16827/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (64215637359/31250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16827/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1221_exp_radius
  have hrNumeric : (12301007463/12500000000 : ℝ) ≤ Real.exp (-16827/1048576 : ℝ) ∧ Real.exp (-16827/1048576 : ℝ) ≤ (984080597041/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (12301007463/12500000000 : ℝ) ≤ (radius 8 (16827/131072 : ℝ)) ∧ (radius 8 (16827/131072 : ℝ)) ≤ (984080597041/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16827/131072 : ℝ)) (12301007463/12500000000 : ℝ) (984080597041/1000000000000 : ℝ) (177722757483/1000000000000 : ℝ) (177722757489/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16827/131072 : ℝ)) (12301007463/12500000000 : ℝ) (984080597041/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16827/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (12301007463/12500000000 : ℝ) (984080597041/1000000000000 : ℝ) (24801007463/25000000000 : ℝ) (992040298521/1000000000000 : ℝ) (31000261419/31250000000 : ℝ) (992008365409/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16827/131072 : ℝ)) 1 (24801007463/25000000000 : ℝ) (992040298521/1000000000000 : ℝ) (31000261419/31250000000 : ℝ) (992008365409/1000000000000 : ℝ) (248006082991/250000000000 : ℝ) (198404866393/200000000000 : ℝ) (198404866367/200000000000 : ℝ) (992024331837/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16827/131072 : ℝ)) 2 (248006082991/250000000000 : ℝ) (198404866393/200000000000 : ℝ) (198404866367/200000000000 : ℝ) (992024331837/1000000000000 : ℝ) (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ) (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16827/131072 : ℝ)) 3 (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ) (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ) (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ) (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16827/131072 : ℝ)) 4 (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ) (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ) (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ) (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16827/131072 : ℝ)) 5 (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ) (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ) (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ) (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16827/131072 : ℝ)) 6 (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ) (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ) (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ) (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16827/131072 : ℝ)) 7 (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ) (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ) (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ) (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16827/131072 : ℝ))) (177722757483/1000000000000 : ℝ) (177722757489/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16827/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177722757483/1000000000000 : ℝ) (177722757489/1000000000000 : ℝ) (588861378741/1000000000000 : ℝ) (117772275749/200000000000 : ℝ) (421571770263/1000000000000 : ℝ) (421571770271/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16827/131072 : ℝ))) 1 (588861378741/1000000000000 : ℝ) (117772275749/200000000000 : ℝ) (421571770263/1000000000000 : ℝ) (421571770271/1000000000000 : ℝ) (252608287251/500000000000 : ℝ) (126304143627/250000000000 : ℝ) (498244251221/1000000000000 : ℝ) (498244251229/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16827/131072 : ℝ))) 2 (252608287251/500000000000 : ℝ) (126304143627/250000000000 : ℝ) (498244251221/1000000000000 : ℝ) (498244251229/1000000000000 : ℝ) (501730412861/1000000000000 : ℝ) (501730412869/1000000000000 : ℝ) (501718301307/1000000000000 : ℝ) (100343660263/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16827/131072 : ℝ))) 3 (501730412861/1000000000000 : ℝ) (501730412869/1000000000000 : ℝ) (501718301307/1000000000000 : ℝ) (100343660263/200000000000 : ℝ) (125431089271/250000000000 : ℝ) (125431089273/250000000000 : ℝ) (501724357047/1000000000000 : ℝ) (7839443079/15625000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16827/131072 : ℝ))) 4 (125431089271/250000000000 : ℝ) (125431089273/250000000000 : ℝ) (501724357047/1000000000000 : ℝ) (7839443079/15625000000 : ℝ) (100344871413/200000000000 : ℝ) (250862178537/500000000000 : ℝ) (100344871413/200000000000 : ℝ) (250862178537/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16827/131072 : ℝ))) 5 (100344871413/200000000000 : ℝ) (250862178537/500000000000 : ℝ) (100344871413/200000000000 : ℝ) (250862178537/500000000000 : ℝ) (100344871413/200000000000 : ℝ) (250862178537/500000000000 : ℝ) (100344871413/200000000000 : ℝ) (250862178537/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16827/131072 : ℝ))) 6 (100344871413/200000000000 : ℝ) (250862178537/500000000000 : ℝ) (100344871413/200000000000 : ℝ) (250862178537/500000000000 : ℝ) (100344871413/200000000000 : ℝ) (250862178537/500000000000 : ℝ) (100344871413/200000000000 : ℝ) (250862178537/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16827/131072 : ℝ))) 7 (100344871413/200000000000 : ℝ) (250862178537/500000000000 : ℝ) (100344871413/200000000000 : ℝ) (250862178537/500000000000 : ℝ) (100344871413/200000000000 : ℝ) (250862178537/500000000000 : ℝ) (100344871413/200000000000 : ℝ) (250862178537/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16827/131072 : ℝ)) hmem 8 (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ) (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16827/131072 : ℝ))) hcmem 8 (100344871413/200000000000 : ℝ) (250862178537/500000000000 : ℝ) (100344871413/200000000000 : ℝ) (250862178537/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16827/131072 : ℝ)) (992024331899/1000000000000 : ℝ) (992024331901/1000000000000 : ℝ) (100344871413/200000000000 : ℝ) (250862178537/500000000000 : ℝ) (794442990759/1000000000000 : ℝ) (31777719631/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1221_exp_lower
  have heNumeric : (64215637359/31250000000 : ℝ)/4 ≤ Real.exp (-1705131478259/2560000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (64215637359/31250000000 : ℝ)/4 ≤ Real.exp ((33653/262144 : ℝ)-(31777719631/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33653/262144 : ℝ) (16827/131072 : ℝ) (31777719631/40000000000 : ℝ) (64215637359/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1222; no trusted numerical premise.
theorem cover8_leaf1222_exp_radius : (997996016342006479/1000000000000000000 : ℝ) ≤ Real.exp ((-33655/2097152 : ℝ)/8) ∧ Real.exp ((-33655/2097152 : ℝ)/8) ≤ (12474950204275081/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33655/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1222_exp_lower : (920113385749077303/1000000000000000000 : ℝ) ≤ Real.exp ((-21314143015349/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314143015349/32000000000000 : ℝ)/8) ≤ (115014173218634663/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314143015349/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1222_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900425213/1000000000000 : ℝ) ≤ 4*Real.exp (16827/131072 : ℝ)*Real.exp (-mu (radius 8 (33655/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900425213/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33655/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1222_exp_radius
  have hrNumeric : (492040063897/500000000000 : ℝ) ≤ Real.exp (-33655/2097152 : ℝ) ∧ Real.exp (-33655/2097152 : ℝ) ≤ (196816025559/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492040063897/500000000000 : ℝ) ≤ (radius 8 (33655/262144 : ℝ)) ∧ (radius 8 (33655/262144 : ℝ)) ≤ (196816025559/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33655/262144 : ℝ)) (492040063897/500000000000 : ℝ) (196816025559/200000000000 : ℝ) (177725355757/1000000000000 : ℝ) (177725355763/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33655/262144 : ℝ)) (492040063897/500000000000 : ℝ) (196816025559/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33655/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492040063897/500000000000 : ℝ) (196816025559/200000000000 : ℝ) (992040063897/1000000000000 : ℝ) (496020031949/500000000000 : ℝ) (198401625779/200000000000 : ℝ) (7750063507/7812500000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33655/262144 : ℝ)) 1 (992040063897/1000000000000 : ℝ) (496020031949/500000000000 : ℝ) (198401625779/200000000000 : ℝ) (7750063507/7812500000 : ℝ) (248006024099/250000000000 : ℝ) (992024096397/1000000000000 : ℝ) (992024096267/1000000000000 : ℝ) (992024096269/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33655/262144 : ℝ)) 2 (248006024099/250000000000 : ℝ) (992024096397/1000000000000 : ℝ) (992024096267/1000000000000 : ℝ) (992024096269/1000000000000 : ℝ) (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ) (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33655/262144 : ℝ)) 3 (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ) (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ) (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ) (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33655/262144 : ℝ)) 4 (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ) (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ) (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ) (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33655/262144 : ℝ)) 5 (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ) (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ) (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ) (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33655/262144 : ℝ)) 6 (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ) (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ) (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ) (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33655/262144 : ℝ)) 7 (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ) (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ) (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ) (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33655/262144 : ℝ))) (177725355757/1000000000000 : ℝ) (177725355763/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33655/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177725355757/1000000000000 : ℝ) (177725355763/1000000000000 : ℝ) (294431338939/500000000000 : ℝ) (294431338941/500000000000 : ℝ) (210787425951/500000000000 : ℝ) (421574851911/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33655/262144 : ℝ))) 1 (294431338939/500000000000 : ℝ) (294431338941/500000000000 : ℝ) (210787425951/500000000000 : ℝ) (421574851911/1000000000000 : ℝ) (50521876489/100000000000 : ℝ) (505218764897/1000000000000 : ℝ) (249123310941/500000000000 : ℝ) (49824662189/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33655/262144 : ℝ))) 2 (50521876489/100000000000 : ℝ) (505218764897/1000000000000 : ℝ) (249123310941/500000000000 : ℝ) (49824662189/100000000000 : ℝ) (250866346693/500000000000 : ℝ) (250866346697/500000000000 : ℝ) (501720582513/1000000000000 : ℝ) (250860291261/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33655/262144 : ℝ))) 3 (250866346693/500000000000 : ℝ) (250866346697/500000000000 : ℝ) (501720582513/1000000000000 : ℝ) (250860291261/500000000000 : ℝ) (501726637949/1000000000000 : ℝ) (250863318979/500000000000 : ℝ) (62715829739/125000000000 : ℝ) (250863318961/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33655/262144 : ℝ))) 4 (501726637949/1000000000000 : ℝ) (250863318979/500000000000 : ℝ) (62715829739/125000000000 : ℝ) (250863318961/500000000000 : ℝ) (50172663793/100000000000 : ℝ) (25086331897/50000000000 : ℝ) (50172663793/100000000000 : ℝ) (25086331897/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33655/262144 : ℝ))) 5 (50172663793/100000000000 : ℝ) (25086331897/50000000000 : ℝ) (50172663793/100000000000 : ℝ) (25086331897/50000000000 : ℝ) (50172663793/100000000000 : ℝ) (25086331897/50000000000 : ℝ) (50172663793/100000000000 : ℝ) (25086331897/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33655/262144 : ℝ))) 6 (50172663793/100000000000 : ℝ) (25086331897/50000000000 : ℝ) (50172663793/100000000000 : ℝ) (25086331897/50000000000 : ℝ) (50172663793/100000000000 : ℝ) (25086331897/50000000000 : ℝ) (50172663793/100000000000 : ℝ) (25086331897/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33655/262144 : ℝ))) 7 (50172663793/100000000000 : ℝ) (25086331897/50000000000 : ℝ) (50172663793/100000000000 : ℝ) (25086331897/50000000000 : ℝ) (50172663793/100000000000 : ℝ) (25086331897/50000000000 : ℝ) (50172663793/100000000000 : ℝ) (25086331897/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33655/262144 : ℝ)) hmem 8 (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ) (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33655/262144 : ℝ))) hcmem 8 (50172663793/100000000000 : ℝ) (25086331897/50000000000 : ℝ) (50172663793/100000000000 : ℝ) (25086331897/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33655/262144 : ℝ)) (992024096331/1000000000000 : ℝ) (992024096333/1000000000000 : ℝ) (50172663793/100000000000 : ℝ) (25086331897/50000000000 : ℝ) (794446790989/1000000000000 : ℝ) (794446791007/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1222_exp_lower
  have heNumeric : (2054900425213/1000000000000 : ℝ)/4 ≤ Real.exp (-21314143015349/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900425213/1000000000000 : ℝ)/4 ≤ Real.exp ((16827/131072 : ℝ)-(794446791007/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16827/131072 : ℝ) (33655/262144 : ℝ) (794446791007/1000000000000 : ℝ) (2054900425213/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1223; no trusted numerical premise.
theorem cover8_leaf1223_exp_radius : (99799595685681021/100000000000000000 : ℝ) ≤ Real.exp ((-4207/262144 : ℝ)/8) ∧ Real.exp ((-4207/262144 : ℝ)/8) ≤ (997995956856810211/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4207/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1223_exp_lower : (92011338742267909/100000000000000000 : ℝ) ≤ Real.exp ((-42628285099417/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628285099417/64000000000000 : ℝ)/8) ≤ (920113387422679091/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628285099417/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1223_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450227557/500000000000 : ℝ) ≤ 4*Real.exp (33655/262144 : ℝ)*Real.exp (-mu (radius 8 (4207/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450227557/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4207/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1223_exp_radius
  have hrNumeric : (984079658549/1000000000000 : ℝ) ≤ Real.exp (-4207/262144 : ℝ) ∧ Real.exp (-4207/262144 : ℝ) ≤ (19681593171/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984079658549/1000000000000 : ℝ) ≤ (radius 8 (4207/32768 : ℝ)) ∧ (radius 8 (4207/32768 : ℝ)) ≤ (19681593171/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4207/32768 : ℝ)) (984079658549/1000000000000 : ℝ) (19681593171/20000000000 : ℝ) (88863976993/500000000000 : ℝ) (22215994249/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4207/32768 : ℝ)) (984079658549/1000000000000 : ℝ) (19681593171/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4207/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984079658549/1000000000000 : ℝ) (19681593171/20000000000 : ℝ) (496019914637/500000000000 : ℝ) (39681593171/40000000000 : ℝ) (496003946191/500000000000 : ℝ) (992007892383/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4207/32768 : ℝ)) 1 (496019914637/500000000000 : ℝ) (39681593171/40000000000 : ℝ) (496003946191/500000000000 : ℝ) (992007892383/1000000000000 : ℝ) (248005965207/250000000000 : ℝ) (992023860829/1000000000000 : ℝ) (992023860699/1000000000000 : ℝ) (992023860701/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4207/32768 : ℝ)) 2 (248005965207/250000000000 : ℝ) (992023860829/1000000000000 : ℝ) (992023860699/1000000000000 : ℝ) (992023860701/1000000000000 : ℝ) (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ) (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4207/32768 : ℝ)) 3 (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ) (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ) (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ) (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4207/32768 : ℝ)) 4 (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ) (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ) (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ) (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4207/32768 : ℝ)) 5 (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ) (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ) (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ) (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4207/32768 : ℝ)) 6 (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ) (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ) (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ) (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4207/32768 : ℝ)) 7 (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ) (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ) (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ) (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4207/32768 : ℝ))) (88863976993/500000000000 : ℝ) (22215994249/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4207/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88863976993/500000000000 : ℝ) (22215994249/125000000000 : ℝ) (588863976993/1000000000000 : ℝ) (147215994249/250000000000 : ℝ) (210788966733/500000000000 : ℝ) (210788966737/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4207/32768 : ℝ))) 1 (588863976993/1000000000000 : ℝ) (147215994249/250000000000 : ℝ) (210788966733/500000000000 : ℝ) (210788966737/500000000000 : ℝ) (505220955229/1000000000000 : ℝ) (101044191047/200000000000 : ℝ) (99649798497/200000000000 : ℝ) (124562248123/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4207/32768 : ℝ))) 2 (505220955229/1000000000000 : ℝ) (101044191047/200000000000 : ℝ) (99649798497/200000000000 : ℝ) (124562248123/250000000000 : ℝ) (501734973857/1000000000000 : ℝ) (62716871733/125000000000 : ℝ) (100344572733/200000000000 : ℝ) (501722863673/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4207/32768 : ℝ))) 3 (501734973857/1000000000000 : ℝ) (62716871733/125000000000 : ℝ) (100344572733/200000000000 : ℝ) (501722863673/1000000000000 : ℝ) (501728918761/1000000000000 : ℝ) (501728918769/1000000000000 : ℝ) (125432229681/250000000000 : ℝ) (125432229683/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4207/32768 : ℝ))) 4 (501728918761/1000000000000 : ℝ) (501728918769/1000000000000 : ℝ) (125432229681/250000000000 : ℝ) (125432229683/250000000000 : ℝ) (250864459371/500000000000 : ℝ) (501728918751/1000000000000 : ℝ) (250864459371/500000000000 : ℝ) (501728918751/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4207/32768 : ℝ))) 5 (250864459371/500000000000 : ℝ) (501728918751/1000000000000 : ℝ) (250864459371/500000000000 : ℝ) (501728918751/1000000000000 : ℝ) (250864459371/500000000000 : ℝ) (501728918751/1000000000000 : ℝ) (250864459371/500000000000 : ℝ) (501728918751/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4207/32768 : ℝ))) 6 (250864459371/500000000000 : ℝ) (501728918751/1000000000000 : ℝ) (250864459371/500000000000 : ℝ) (501728918751/1000000000000 : ℝ) (250864459371/500000000000 : ℝ) (501728918751/1000000000000 : ℝ) (250864459371/500000000000 : ℝ) (501728918751/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4207/32768 : ℝ))) 7 (250864459371/500000000000 : ℝ) (501728918751/1000000000000 : ℝ) (250864459371/500000000000 : ℝ) (501728918751/1000000000000 : ℝ) (250864459371/500000000000 : ℝ) (501728918751/1000000000000 : ℝ) (250864459371/500000000000 : ℝ) (501728918751/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4207/32768 : ℝ)) hmem 8 (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ) (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4207/32768 : ℝ))) hcmem 8 (250864459371/500000000000 : ℝ) (501728918751/1000000000000 : ℝ) (250864459371/500000000000 : ℝ) (501728918751/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4207/32768 : ℝ)) (992023860763/1000000000000 : ℝ) (198404772153/200000000000 : ℝ) (250864459371/500000000000 : ℝ) (501728918751/1000000000000 : ℝ) (24826580973/31250000000 : ℝ) (794450591153/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1223_exp_lower
  have heNumeric : (1027450227557/500000000000 : ℝ)/4 ≤ Real.exp (-42628285099417/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450227557/500000000000 : ℝ)/4 ≤ Real.exp ((33655/262144 : ℝ)-(794450591153/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33655/262144 : ℝ) (4207/32768 : ℝ) (794450591153/1000000000000 : ℝ) (1027450227557/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1224; no trusted numerical premise.
theorem cover8_leaf1224_exp_radius : (997995897371617487/1000000000000000000 : ℝ) ≤ Real.exp ((-33657/2097152 : ℝ)/8) ∧ Real.exp ((-33657/2097152 : ℝ)/8) ≤ (62374743585726093/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33657/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1224_exp_lower : (920113389103641787/1000000000000000000 : ℝ) ≤ Real.exp ((-1065707104101/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065707104101/1600000000000 : ℝ)/8) ≤ (230028347275910447/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065707104101/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1224_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900485147/1000000000000 : ℝ) ≤ 4*Real.exp (4207/32768 : ℝ)*Real.exp (-mu (radius 8 (33657/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900485147/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33657/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1224_exp_radius
  have hrNumeric : (984079189303/1000000000000 : ℝ) ≤ Real.exp (-33657/2097152 : ℝ) ∧ Real.exp (-33657/2097152 : ℝ) ≤ (123009898663/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984079189303/1000000000000 : ℝ) ≤ (radius 8 (33657/262144 : ℝ)) ∧ (radius 8 (33657/262144 : ℝ)) ≤ (123009898663/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33657/262144 : ℝ)) (984079189303/1000000000000 : ℝ) (123009898663/125000000000 : ℝ) (177730552181/1000000000000 : ℝ) (44432638047/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33657/262144 : ℝ)) (984079189303/1000000000000 : ℝ) (123009898663/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33657/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984079189303/1000000000000 : ℝ) (123009898663/125000000000 : ℝ) (992039594651/1000000000000 : ℝ) (248009898663/250000000000 : ℝ) (992007655869/1000000000000 : ℝ) (99200765587/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33657/262144 : ℝ)) 1 (992039594651/1000000000000 : ℝ) (248009898663/250000000000 : ℝ) (992007655869/1000000000000 : ℝ) (99200765587/100000000000 : ℝ) (49601181263/50000000000 : ℝ) (992023625261/1000000000000 : ℝ) (992023625131/1000000000000 : ℝ) (992023625133/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33657/262144 : ℝ)) 2 (49601181263/50000000000 : ℝ) (992023625261/1000000000000 : ℝ) (992023625131/1000000000000 : ℝ) (992023625133/1000000000000 : ℝ) (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ) (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33657/262144 : ℝ)) 3 (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ) (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ) (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ) (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33657/262144 : ℝ)) 4 (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ) (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ) (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ) (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33657/262144 : ℝ)) 5 (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ) (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ) (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ) (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33657/262144 : ℝ)) 6 (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ) (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ) (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ) (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33657/262144 : ℝ)) 7 (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ) (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ) (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ) (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33657/262144 : ℝ))) (177730552181/1000000000000 : ℝ) (44432638047/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33657/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177730552181/1000000000000 : ℝ) (44432638047/250000000000 : ℝ) (58886527609/100000000000 : ℝ) (294432638047/500000000000 : ℝ) (421581014967/1000000000000 : ℝ) (6587203359/15625000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33657/262144 : ℝ))) 1 (58886527609/100000000000 : ℝ) (294432638047/500000000000 : ℝ) (421581014967/1000000000000 : ℝ) (6587203359/15625000000 : ℝ) (63152893191/125000000000 : ℝ) (101044629107/200000000000 : ℝ) (498251363041/1000000000000 : ℝ) (498251363049/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33657/262144 : ℝ))) 2 (63152893191/125000000000 : ℝ) (101044629107/200000000000 : ℝ) (498251363041/1000000000000 : ℝ) (498251363049/1000000000000 : ℝ) (125434313571/250000000000 : ℝ) (125434313573/250000000000 : ℝ) (250862572387/500000000000 : ℝ) (501725144783/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33657/262144 : ℝ))) 3 (125434313571/250000000000 : ℝ) (125434313573/250000000000 : ℝ) (250862572387/500000000000 : ℝ) (501725144783/1000000000000 : ℝ) (501731199529/1000000000000 : ℝ) (250865599769/500000000000 : ℝ) (125432799873/250000000000 : ℝ) (501731199501/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33657/262144 : ℝ))) 4 (501731199529/1000000000000 : ℝ) (250865599769/500000000000 : ℝ) (125432799873/250000000000 : ℝ) (501731199501/1000000000000 : ℝ) (50173119951/100000000000 : ℝ) (3135819997/6250000000 : ℝ) (50173119951/100000000000 : ℝ) (3135819997/6250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33657/262144 : ℝ))) 5 (50173119951/100000000000 : ℝ) (3135819997/6250000000 : ℝ) (50173119951/100000000000 : ℝ) (3135819997/6250000000 : ℝ) (50173119951/100000000000 : ℝ) (3135819997/6250000000 : ℝ) (50173119951/100000000000 : ℝ) (3135819997/6250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33657/262144 : ℝ))) 6 (50173119951/100000000000 : ℝ) (3135819997/6250000000 : ℝ) (50173119951/100000000000 : ℝ) (3135819997/6250000000 : ℝ) (50173119951/100000000000 : ℝ) (3135819997/6250000000 : ℝ) (50173119951/100000000000 : ℝ) (3135819997/6250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33657/262144 : ℝ))) 7 (50173119951/100000000000 : ℝ) (3135819997/6250000000 : ℝ) (50173119951/100000000000 : ℝ) (3135819997/6250000000 : ℝ) (50173119951/100000000000 : ℝ) (3135819997/6250000000 : ℝ) (50173119951/100000000000 : ℝ) (3135819997/6250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33657/262144 : ℝ)) hmem 8 (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ) (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33657/262144 : ℝ))) hcmem 8 (50173119951/100000000000 : ℝ) (3135819997/6250000000 : ℝ) (50173119951/100000000000 : ℝ) (3135819997/6250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33657/262144 : ℝ)) (198404725039/200000000000 : ℝ) (992023625197/1000000000000 : ℝ) (50173119951/100000000000 : ℝ) (3135819997/6250000000 : ℝ) (49653399451/62500000000 : ℝ) (158890878247/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1224_exp_lower
  have heNumeric : (2054900485147/1000000000000 : ℝ)/4 ≤ Real.exp (-1065707104101/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900485147/1000000000000 : ℝ)/4 ≤ Real.exp ((4207/32768 : ℝ)-(158890878247/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4207/32768 : ℝ) (33657/262144 : ℝ) (158890878247/200000000000 : ℝ) (2054900485147/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1200_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1200_certificate
#check SmaleRate.Proofs.cover8_leaf1201_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1201_certificate
#check SmaleRate.Proofs.cover8_leaf1202_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1202_certificate
#check SmaleRate.Proofs.cover8_leaf1203_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1203_certificate
#check SmaleRate.Proofs.cover8_leaf1204_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1204_certificate
#check SmaleRate.Proofs.cover8_leaf1205_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1205_certificate
#check SmaleRate.Proofs.cover8_leaf1206_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1206_certificate
#check SmaleRate.Proofs.cover8_leaf1207_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1207_certificate
#check SmaleRate.Proofs.cover8_leaf1208_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1208_certificate
#check SmaleRate.Proofs.cover8_leaf1209_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1209_certificate
#check SmaleRate.Proofs.cover8_leaf1210_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1210_certificate
#check SmaleRate.Proofs.cover8_leaf1211_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1211_certificate
#check SmaleRate.Proofs.cover8_leaf1212_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1212_certificate
#check SmaleRate.Proofs.cover8_leaf1213_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1213_certificate
#check SmaleRate.Proofs.cover8_leaf1214_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1214_certificate
#check SmaleRate.Proofs.cover8_leaf1215_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1215_certificate
#check SmaleRate.Proofs.cover8_leaf1216_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1216_certificate
#check SmaleRate.Proofs.cover8_leaf1217_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1217_certificate
#check SmaleRate.Proofs.cover8_leaf1218_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1218_certificate
#check SmaleRate.Proofs.cover8_leaf1219_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1219_certificate
#check SmaleRate.Proofs.cover8_leaf1220_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1220_certificate
#check SmaleRate.Proofs.cover8_leaf1221_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1221_certificate
#check SmaleRate.Proofs.cover8_leaf1222_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1222_certificate
#check SmaleRate.Proofs.cover8_leaf1223_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1223_certificate
#check SmaleRate.Proofs.cover8_leaf1224_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1224_certificate
