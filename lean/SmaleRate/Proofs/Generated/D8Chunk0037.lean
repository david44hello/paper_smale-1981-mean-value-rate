/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0925; no trusted numerical premise.
theorem cover8_leaf0925_exp_radius : (998005296076043847/1000000000000000000 : ℝ) ≤ Real.exp ((-33499/2097152 : ℝ)/8) ∧ Real.exp ((-33499/2097152 : ℝ)/8) ≤ (124750662009505481/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33499/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0925_exp_lower : (920113452318845577/1000000000000000000 : ℝ) ≤ Real.exp ((-85256497975483/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256497975483/128000000000000 : ℝ)/8) ≤ (460056726159422789/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256497975483/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0925_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450807291/500000000000 : ℝ) ≤ 4*Real.exp (66997/524288 : ℝ)*Real.exp (-mu (radius 8 (33499/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450807291/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33499/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0925_exp_radius
  have hrNumeric : (984153332889/1000000000000 : ℝ) ≤ Real.exp (-33499/2097152 : ℝ) ∧ Real.exp (-33499/2097152 : ℝ) ≤ (98415333289/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984153332889/1000000000000 : ℝ) ≤ (radius 8 (33499/262144 : ℝ)) ∧ (radius 8 (33499/262144 : ℝ)) ≤ (98415333289/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33499/262144 : ℝ)) (984153332889/1000000000000 : ℝ) (98415333289/100000000000 : ℝ) (17731953463/100000000000 : ℝ) (44329883659/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33499/262144 : ℝ)) (984153332889/1000000000000 : ℝ) (98415333289/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33499/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984153332889/1000000000000 : ℝ) (98415333289/100000000000 : ℝ) (248019166611/250000000000 : ℝ) (198415333289/200000000000 : ℝ) (198409005127/200000000000 : ℝ) (992045025637/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33499/262144 : ℝ)) 1 (248019166611/250000000000 : ℝ) (198415333289/200000000000 : ℝ) (198409005127/200000000000 : ℝ) (992045025637/1000000000000 : ℝ) (992060846039/1000000000000 : ℝ) (992060846041/1000000000000 : ℝ) (992060845913/1000000000000 : ℝ) (198412169183/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33499/262144 : ℝ)) 2 (992060846039/1000000000000 : ℝ) (992060846041/1000000000000 : ℝ) (992060845913/1000000000000 : ℝ) (198412169183/200000000000 : ℝ) (124007605747/125000000000 : ℝ) (496030422989/500000000000 : ℝ) (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33499/262144 : ℝ)) 3 (124007605747/125000000000 : ℝ) (496030422989/500000000000 : ℝ) (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ) (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ) (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33499/262144 : ℝ)) 4 (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ) (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ) (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ) (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33499/262144 : ℝ)) 5 (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ) (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ) (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ) (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33499/262144 : ℝ)) 6 (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ) (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ) (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ) (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33499/262144 : ℝ)) 7 (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ) (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ) (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ) (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33499/262144 : ℝ))) (17731953463/100000000000 : ℝ) (44329883659/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33499/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17731953463/100000000000 : ℝ) (44329883659/250000000000 : ℝ) (117731953463/200000000000 : ℝ) (294329883659/500000000000 : ℝ) (210546630601/500000000000 : ℝ) (42109326121/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33499/262144 : ℝ))) 1 (117731953463/200000000000 : ℝ) (294329883659/500000000000 : ℝ) (210546630601/500000000000 : ℝ) (42109326121/100000000000 : ℝ) (252438257129/500000000000 : ℝ) (63109564283/125000000000 : ℝ) (24893807521/50000000000 : ℝ) (497876150427/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33499/262144 : ℝ))) 2 (252438257129/500000000000 : ℝ) (63109564283/125000000000 : ℝ) (24893807521/50000000000 : ℝ) (497876150427/1000000000000 : ℝ) (501376332339/1000000000000 : ℝ) (250688166173/500000000000 : ℝ) (501364114547/1000000000000 : ℝ) (100272822911/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33499/262144 : ℝ))) 3 (501376332339/1000000000000 : ℝ) (250688166173/500000000000 : ℝ) (501364114547/1000000000000 : ℝ) (100272822911/200000000000 : ℝ) (501370223443/1000000000000 : ℝ) (501370223451/1000000000000 : ℝ) (100274044681/200000000000 : ℝ) (250685111707/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33499/262144 : ℝ))) 4 (501370223443/1000000000000 : ℝ) (501370223451/1000000000000 : ℝ) (100274044681/200000000000 : ℝ) (250685111707/500000000000 : ℝ) (7833909741/15625000000 : ℝ) (501370223433/1000000000000 : ℝ) (501370223423/1000000000000 : ℝ) (501370223433/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33499/262144 : ℝ))) 5 (7833909741/15625000000 : ℝ) (501370223433/1000000000000 : ℝ) (501370223423/1000000000000 : ℝ) (501370223433/1000000000000 : ℝ) (501370223423/1000000000000 : ℝ) (501370223433/1000000000000 : ℝ) (501370223423/1000000000000 : ℝ) (501370223433/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33499/262144 : ℝ))) 6 (501370223423/1000000000000 : ℝ) (501370223433/1000000000000 : ℝ) (501370223423/1000000000000 : ℝ) (501370223433/1000000000000 : ℝ) (501370223423/1000000000000 : ℝ) (501370223433/1000000000000 : ℝ) (501370223423/1000000000000 : ℝ) (501370223433/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33499/262144 : ℝ))) 7 (501370223423/1000000000000 : ℝ) (501370223433/1000000000000 : ℝ) (501370223423/1000000000000 : ℝ) (501370223433/1000000000000 : ℝ) (501370223423/1000000000000 : ℝ) (501370223433/1000000000000 : ℝ) (501370223423/1000000000000 : ℝ) (501370223433/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33499/262144 : ℝ)) hmem 8 (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ) (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33499/262144 : ℝ))) hcmem 8 (501370223423/1000000000000 : ℝ) (501370223433/1000000000000 : ℝ) (501370223423/1000000000000 : ℝ) (501370223433/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33499/262144 : ℝ)) (39682433839/40000000000 : ℝ) (496030422989/500000000000 : ℝ) (501370223423/1000000000000 : ℝ) (501370223433/1000000000000 : ℝ) (793853026767/1000000000000 : ℝ) (396926513393/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0925_exp_lower
  have heNumeric : (1027450807291/500000000000 : ℝ)/4 ≤ Real.exp (-85256497975483/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450807291/500000000000 : ℝ)/4 ≤ Real.exp ((66997/524288 : ℝ)-(396926513393/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66997/524288 : ℝ) (33499/262144 : ℝ) (396926513393/500000000000 : ℝ) (1027450807291/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0926; no trusted numerical premise.
theorem cover8_leaf0926_exp_radius : (124750658291646089/125000000000000000 : ℝ) ≤ Real.exp ((-66999/4194304 : ℝ)/8) ∧ Real.exp ((-66999/4194304 : ℝ)/8) ≤ (998005266333168713/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66999/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0926_exp_lower : (230028363115959057/250000000000000000 : ℝ) ≤ Real.exp ((-42628248907061/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628248907061/64000000000000 : ℝ)/8) ≤ (920113452463836229/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628248907061/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0926_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725404293/250000000000 : ℝ) ≤ 4*Real.exp (33499/262144 : ℝ)*Real.exp (-mu (radius 8 (66999/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725404293/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66999/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0926_exp_radius
  have hrNumeric : (123019137281/125000000000 : ℝ) ≤ Real.exp (-66999/4194304 : ℝ) ∧ Real.exp (-66999/4194304 : ℝ) ≤ (984153098249/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123019137281/125000000000 : ℝ) ≤ (radius 8 (66999/524288 : ℝ)) ∧ (radius 8 (66999/524288 : ℝ)) ≤ (984153098249/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66999/524288 : ℝ)) (123019137281/125000000000 : ℝ) (984153098249/1000000000000 : ℝ) (88660418461/500000000000 : ℝ) (177320836929/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66999/524288 : ℝ)) (123019137281/125000000000 : ℝ) (984153098249/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66999/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123019137281/125000000000 : ℝ) (984153098249/1000000000000 : ℝ) (248019137281/250000000000 : ℝ) (7936612393/8000000000 : ℝ) (496022453687/500000000000 : ℝ) (62002806711/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66999/524288 : ℝ)) 1 (248019137281/250000000000 : ℝ) (7936612393/8000000000 : ℝ) (496022453687/500000000000 : ℝ) (62002806711/62500000000 : ℝ) (992060728249/1000000000000 : ℝ) (992060728251/1000000000000 : ℝ) (496030364061/500000000000 : ℝ) (317459433/320000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66999/524288 : ℝ)) 2 (992060728249/1000000000000 : ℝ) (992060728251/1000000000000 : ℝ) (496030364061/500000000000 : ℝ) (317459433/320000000 : ℝ) (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ) (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66999/524288 : ℝ)) 3 (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ) (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ) (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ) (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66999/524288 : ℝ)) 4 (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ) (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ) (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ) (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66999/524288 : ℝ)) 5 (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ) (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ) (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ) (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66999/524288 : ℝ)) 6 (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ) (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ) (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ) (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66999/524288 : ℝ)) 7 (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ) (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ) (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ) (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66999/524288 : ℝ))) (88660418461/500000000000 : ℝ) (177320836929/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66999/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88660418461/500000000000 : ℝ) (177320836929/1000000000000 : ℝ) (588660418461/1000000000000 : ℝ) (117732083693/200000000000 : ℝ) (210547403761/500000000000 : ℝ) (421094807531/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66999/524288 : ℝ))) 1 (588660418461/1000000000000 : ℝ) (117732083693/200000000000 : ℝ) (210547403761/500000000000 : ℝ) (421094807531/1000000000000 : ℝ) (504877612991/1000000000000 : ℝ) (252438806499/500000000000 : ℝ) (497877339921/1000000000000 : ℝ) (497877339929/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66999/524288 : ℝ))) 2 (504877612991/1000000000000 : ℝ) (252438806499/500000000000 : ℝ) (497877339921/1000000000000 : ℝ) (497877339929/1000000000000 : ℝ) (62672184557/125000000000 : ℝ) (31336092279/62500000000 : ℝ) (501365259009/1000000000000 : ℝ) (501365259017/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66999/524288 : ℝ))) 3 (62672184557/125000000000 : ℝ) (31336092279/62500000000 : ℝ) (501365259009/1000000000000 : ℝ) (501365259017/1000000000000 : ℝ) (125342841933/250000000000 : ℝ) (501371367741/1000000000000 : ℝ) (100274273539/200000000000 : ℝ) (62671420963/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66999/524288 : ℝ))) 4 (125342841933/250000000000 : ℝ) (501371367741/1000000000000 : ℝ) (100274273539/200000000000 : ℝ) (62671420963/125000000000 : ℝ) (501371367713/1000000000000 : ℝ) (501371367723/1000000000000 : ℝ) (501371367713/1000000000000 : ℝ) (501371367723/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66999/524288 : ℝ))) 5 (501371367713/1000000000000 : ℝ) (501371367723/1000000000000 : ℝ) (501371367713/1000000000000 : ℝ) (501371367723/1000000000000 : ℝ) (501371367713/1000000000000 : ℝ) (501371367723/1000000000000 : ℝ) (501371367713/1000000000000 : ℝ) (501371367723/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66999/524288 : ℝ))) 6 (501371367713/1000000000000 : ℝ) (501371367723/1000000000000 : ℝ) (501371367713/1000000000000 : ℝ) (501371367723/1000000000000 : ℝ) (501371367713/1000000000000 : ℝ) (501371367723/1000000000000 : ℝ) (501371367713/1000000000000 : ℝ) (501371367723/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66999/524288 : ℝ))) 7 (501371367713/1000000000000 : ℝ) (501371367723/1000000000000 : ℝ) (501371367713/1000000000000 : ℝ) (501371367723/1000000000000 : ℝ) (501371367713/1000000000000 : ℝ) (501371367723/1000000000000 : ℝ) (501371367713/1000000000000 : ℝ) (501371367723/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66999/524288 : ℝ)) hmem 8 (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ) (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66999/524288 : ℝ))) hcmem 8 (501371367713/1000000000000 : ℝ) (501371367723/1000000000000 : ℝ) (501371367713/1000000000000 : ℝ) (501371367723/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66999/524288 : ℝ)) (198412145637/200000000000 : ℝ) (248015182047/250000000000 : ℝ) (501371367713/1000000000000 : ℝ) (501371367723/1000000000000 : ℝ) (396927466427/500000000000 : ℝ) (396927466437/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0926_exp_lower
  have heNumeric : (513725404293/250000000000 : ℝ)/4 ≤ Real.exp (-42628248907061/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725404293/250000000000 : ℝ)/4 ≤ Real.exp ((33499/262144 : ℝ)-(396927466437/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33499/262144 : ℝ) (66999/524288 : ℝ) (396927466437/500000000000 : ℝ) (513725404293/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0927; no trusted numerical premise.
theorem cover8_leaf0927_exp_radius : (15593831821723351/15625000000000000 : ℝ) ≤ Real.exp ((-8375/524288 : ℝ)/8) ∧ Real.exp ((-8375/524288 : ℝ)/8) ≤ (199601047318058893/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8375/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0927_exp_lower : (920113452612047277/1000000000000000000 : ℝ) ≤ Real.exp ((-85256497649177/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256497649177/128000000000000 : ℝ)/8) ≤ (460056726306023639/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256497649177/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0927_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745080991/50000000000 : ℝ) ≤ 4*Real.exp (66999/524288 : ℝ)*Real.exp (-mu (radius 8 (8375/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (102745080991/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8375/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0927_exp_radius
  have hrNumeric : (123019107951/125000000000 : ℝ) ≤ Real.exp (-8375/524288 : ℝ) ∧ Real.exp (-8375/524288 : ℝ) ≤ (984152863609/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123019107951/125000000000 : ℝ) ≤ (radius 8 (8375/65536 : ℝ)) ∧ (radius 8 (8375/65536 : ℝ)) ≤ (984152863609/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8375/65536 : ℝ)) (123019107951/125000000000 : ℝ) (984152863609/1000000000000 : ℝ) (177322139199/1000000000000 : ℝ) (35464427841/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8375/65536 : ℝ)) (123019107951/125000000000 : ℝ) (984152863609/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8375/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123019107951/125000000000 : ℝ) (984152863609/1000000000000 : ℝ) (248019107951/250000000000 : ℝ) (198415286361/200000000000 : ℝ) (992044789113/1000000000000 : ℝ) (198408957823/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8375/65536 : ℝ)) 1 (248019107951/250000000000 : ℝ) (198415286361/200000000000 : ℝ) (992044789113/1000000000000 : ℝ) (198408957823/200000000000 : ℝ) (496030305229/500000000000 : ℝ) (49603030523/50000000000 : ℝ) (248015152583/250000000000 : ℝ) (496030305167/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8375/65536 : ℝ)) 2 (496030305229/500000000000 : ℝ) (49603030523/50000000000 : ℝ) (248015152583/250000000000 : ℝ) (496030305167/500000000000 : ℝ) (198412122079/200000000000 : ℝ) (992060610397/1000000000000 : ℝ) (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8375/65536 : ℝ)) 3 (198412122079/200000000000 : ℝ) (992060610397/1000000000000 : ℝ) (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ) (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ) (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8375/65536 : ℝ)) 4 (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ) (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ) (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ) (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8375/65536 : ℝ)) 5 (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ) (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ) (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ) (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8375/65536 : ℝ)) 6 (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ) (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ) (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ) (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8375/65536 : ℝ)) 7 (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ) (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ) (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ) (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8375/65536 : ℝ))) (177322139199/1000000000000 : ℝ) (35464427841/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8375/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177322139199/1000000000000 : ℝ) (35464427841/200000000000 : ℝ) (588661069599/1000000000000 : ℝ) (588661069603/1000000000000 : ℝ) (210548176909/500000000000 : ℝ) (210548176913/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8375/65536 : ℝ))) 1 (588661069599/1000000000000 : ℝ) (588661069603/1000000000000 : ℝ) (210548176909/500000000000 : ℝ) (210548176913/500000000000 : ℝ) (126219677927/250000000000 : ℝ) (100975742343/200000000000 : ℝ) (99575705881/200000000000 : ℝ) (124469632353/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8375/65536 : ℝ))) 2 (126219677927/250000000000 : ℝ) (100975742343/200000000000 : ℝ) (99575705881/200000000000 : ℝ) (124469632353/250000000000 : ℝ) (125344655139/250000000000 : ℝ) (125344655141/250000000000 : ℝ) (250683201727/500000000000 : ℝ) (250683201731/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8375/65536 : ℝ))) 3 (125344655139/250000000000 : ℝ) (125344655141/250000000000 : ℝ) (250683201727/500000000000 : ℝ) (250683201731/500000000000 : ℝ) (100274502401/200000000000 : ℝ) (501372512013/1000000000000 : ℝ) (501372511967/1000000000000 : ℝ) (62671563997/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8375/65536 : ℝ))) 4 (100274502401/200000000000 : ℝ) (501372512013/1000000000000 : ℝ) (501372511967/1000000000000 : ℝ) (62671563997/125000000000 : ℝ) (250686255993/500000000000 : ℝ) (100274502399/200000000000 : ℝ) (100274502397/200000000000 : ℝ) (100274502399/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8375/65536 : ℝ))) 5 (250686255993/500000000000 : ℝ) (100274502399/200000000000 : ℝ) (100274502397/200000000000 : ℝ) (100274502399/200000000000 : ℝ) (100274502397/200000000000 : ℝ) (100274502399/200000000000 : ℝ) (100274502397/200000000000 : ℝ) (100274502399/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8375/65536 : ℝ))) 6 (100274502397/200000000000 : ℝ) (100274502399/200000000000 : ℝ) (100274502397/200000000000 : ℝ) (100274502399/200000000000 : ℝ) (100274502397/200000000000 : ℝ) (100274502399/200000000000 : ℝ) (100274502397/200000000000 : ℝ) (100274502399/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8375/65536 : ℝ))) 7 (100274502397/200000000000 : ℝ) (100274502399/200000000000 : ℝ) (100274502397/200000000000 : ℝ) (100274502399/200000000000 : ℝ) (100274502397/200000000000 : ℝ) (100274502399/200000000000 : ℝ) (100274502397/200000000000 : ℝ) (100274502399/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8375/65536 : ℝ)) hmem 8 (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ) (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8375/65536 : ℝ))) hcmem 8 (100274502397/200000000000 : ℝ) (100274502399/200000000000 : ℝ) (100274502397/200000000000 : ℝ) (100274502399/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8375/65536 : ℝ)) (496030305197/500000000000 : ℝ) (992060610397/1000000000000 : ℝ) (100274502397/200000000000 : ℝ) (100274502399/200000000000 : ℝ) (158771367783/200000000000 : ℝ) (396928419467/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0927_exp_lower
  have heNumeric : (102745080991/50000000000 : ℝ)/4 ≤ Real.exp (-85256497649177/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745080991/50000000000 : ℝ)/4 ≤ Real.exp ((66999/524288 : ℝ)-(396928419467/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66999/524288 : ℝ) (8375/65536 : ℝ) (396928419467/500000000000 : ℝ) (102745080991/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0928; no trusted numerical premise.
theorem cover8_leaf0928_exp_radius : (998005206847421101/1000000000000000000 : ℝ) ≤ Real.exp ((-67001/4194304 : ℝ)/8) ∧ Real.exp ((-67001/4194304 : ℝ)/8) ≤ (499002603423710551/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67001/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0928_exp_lower : (46005672638116429/50000000000000000 : ℝ) ≤ Real.exp ((-10657062185241/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657062185241/16000000000000 : ℝ)/8) ≤ (920113452762328581/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657062185241/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0928_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980324501/200000000000 : ℝ) ≤ 4*Real.exp (8375/65536 : ℝ)*Real.exp (-mu (radius 8 (67001/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980324501/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67001/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0928_exp_radius
  have hrNumeric : (123019078621/125000000000 : ℝ) ≤ Real.exp (-67001/4194304 : ℝ) ∧ Real.exp (-67001/4194304 : ℝ) ≤ (984152628969/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123019078621/125000000000 : ℝ) ≤ (radius 8 (67001/524288 : ℝ)) ∧ (radius 8 (67001/524288 : ℝ)) ≤ (984152628969/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67001/524288 : ℝ)) (123019078621/125000000000 : ℝ) (984152628969/1000000000000 : ℝ) (88661720733/500000000000 : ℝ) (2770678773/15625000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67001/524288 : ℝ)) (123019078621/125000000000 : ℝ) (984152628969/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67001/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123019078621/125000000000 : ℝ) (984152628969/1000000000000 : ℝ) (248019078621/250000000000 : ℝ) (198415262897/200000000000 : ℝ) (992044670853/1000000000000 : ℝ) (496022335427/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67001/524288 : ℝ)) 1 (248019078621/250000000000 : ℝ) (198415262897/200000000000 : ℝ) (992044670853/1000000000000 : ℝ) (496022335427/500000000000 : ℝ) (248015123167/250000000000 : ℝ) (99206049267/100000000000 : ℝ) (496030246271/500000000000 : ℝ) (3875236299/3906250000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67001/524288 : ℝ)) 2 (248015123167/250000000000 : ℝ) (99206049267/100000000000 : ℝ) (496030246271/500000000000 : ℝ) (3875236299/3906250000 : ℝ) (198412098521/200000000000 : ℝ) (992060492607/1000000000000 : ℝ) (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67001/524288 : ℝ)) 3 (198412098521/200000000000 : ℝ) (992060492607/1000000000000 : ℝ) (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ) (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ) (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67001/524288 : ℝ)) 4 (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ) (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ) (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ) (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67001/524288 : ℝ)) 5 (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ) (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ) (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ) (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67001/524288 : ℝ)) 6 (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ) (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ) (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ) (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67001/524288 : ℝ)) 7 (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ) (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ) (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ) (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67001/524288 : ℝ))) (88661720733/500000000000 : ℝ) (2770678773/15625000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67001/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88661720733/500000000000 : ℝ) (2770678773/15625000000 : ℝ) (588661720733/1000000000000 : ℝ) (18395678773/31250000000 : ℝ) (6579654689/15625000000 : ℝ) (84219580021/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67001/524288 : ℝ))) 1 (588661720733/1000000000000 : ℝ) (18395678773/31250000000 : ℝ) (6579654689/15625000000 : ℝ) (84219580021/200000000000 : ℝ) (252439905207/500000000000 : ℝ) (504879810421/1000000000000 : ℝ) (3983037751/8000000000 : ℝ) (497879718883/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67001/524288 : ℝ))) 2 (252439905207/500000000000 : ℝ) (504879810421/1000000000000 : ℝ) (3983037751/8000000000 : ℝ) (497879718883/1000000000000 : ℝ) (125344941161/250000000000 : ℝ) (125344941163/250000000000 : ℝ) (501367547887/1000000000000 : ℝ) (100273509579/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67001/524288 : ℝ))) 3 (125344941161/250000000000 : ℝ) (125344941163/250000000000 : ℝ) (501367547887/1000000000000 : ℝ) (100273509579/200000000000 : ℝ) (100274731253/200000000000 : ℝ) (250686828137/500000000000 : ℝ) (125343414057/250000000000 : ℝ) (501373656237/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67001/524288 : ℝ))) 4 (100274731253/200000000000 : ℝ) (250686828137/500000000000 : ℝ) (125343414057/250000000000 : ℝ) (501373656237/1000000000000 : ℝ) (250686828123/500000000000 : ℝ) (7833963379/15625000000 : ℝ) (250686828123/500000000000 : ℝ) (7833963379/15625000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67001/524288 : ℝ))) 5 (250686828123/500000000000 : ℝ) (7833963379/15625000000 : ℝ) (250686828123/500000000000 : ℝ) (7833963379/15625000000 : ℝ) (250686828123/500000000000 : ℝ) (7833963379/15625000000 : ℝ) (250686828123/500000000000 : ℝ) (7833963379/15625000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67001/524288 : ℝ))) 6 (250686828123/500000000000 : ℝ) (7833963379/15625000000 : ℝ) (250686828123/500000000000 : ℝ) (7833963379/15625000000 : ℝ) (250686828123/500000000000 : ℝ) (7833963379/15625000000 : ℝ) (250686828123/500000000000 : ℝ) (7833963379/15625000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67001/524288 : ℝ))) 7 (250686828123/500000000000 : ℝ) (7833963379/15625000000 : ℝ) (250686828123/500000000000 : ℝ) (7833963379/15625000000 : ℝ) (250686828123/500000000000 : ℝ) (7833963379/15625000000 : ℝ) (250686828123/500000000000 : ℝ) (7833963379/15625000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67001/524288 : ℝ)) hmem 8 (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ) (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67001/524288 : ℝ))) hcmem 8 (250686828123/500000000000 : ℝ) (7833963379/15625000000 : ℝ) (250686828123/500000000000 : ℝ) (7833963379/15625000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67001/524288 : ℝ)) (248015123151/250000000000 : ℝ) (992060492607/1000000000000 : ℝ) (250686828123/500000000000 : ℝ) (7833963379/15625000000 : ℝ) (793858744957/1000000000000 : ℝ) (49616171561/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0928_exp_lower
  have heNumeric : (410980324501/200000000000 : ℝ)/4 ≤ Real.exp (-10657062185241/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980324501/200000000000 : ℝ)/4 ≤ Real.exp ((8375/65536 : ℝ)-(49616171561/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8375/65536 : ℝ) (67001/524288 : ℝ) (49616171561/62500000000 : ℝ) (410980324501/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0929; no trusted numerical premise.
theorem cover8_leaf0929_exp_radius : (499002588552274313/500000000000000000 : ℝ) ≤ Real.exp ((-33501/2097152 : ℝ)/8) ∧ Real.exp ((-33501/2097152 : ℝ)/8) ≤ (998005177104548627/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33501/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0929_exp_lower : (5750709080711719/6250000000000000 : ℝ) ≤ Real.exp ((-85256497313271/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256497313271/128000000000000 : ℝ)/8) ≤ (920113452913875041/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256497313271/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0929_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901625213/1000000000000 : ℝ) ≤ 4*Real.exp (67001/524288 : ℝ)*Real.exp (-mu (radius 8 (33501/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901625213/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33501/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0929_exp_radius
  have hrNumeric : (984152394327/1000000000000 : ℝ) ≤ Real.exp (-33501/2097152 : ℝ) ∧ Real.exp (-33501/2097152 : ℝ) ≤ (123019049291/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984152394327/1000000000000 : ℝ) ≤ (radius 8 (33501/262144 : ℝ)) ∧ (radius 8 (33501/262144 : ℝ)) ≤ (123019049291/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33501/262144 : ℝ)) (984152394327/1000000000000 : ℝ) (123019049291/125000000000 : ℝ) (11082796483/62500000000 : ℝ) (35464948747/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33501/262144 : ℝ)) (984152394327/1000000000000 : ℝ) (123019049291/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33501/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984152394327/1000000000000 : ℝ) (123019049291/125000000000 : ℝ) (992076197163/1000000000000 : ℝ) (248019049291/250000000000 : ℝ) (992044552591/1000000000000 : ℝ) (992044552593/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33501/262144 : ℝ)) 1 (992076197163/1000000000000 : ℝ) (248019049291/250000000000 : ℝ) (992044552591/1000000000000 : ℝ) (992044552593/1000000000000 : ℝ) (992060374877/1000000000000 : ℝ) (992060374879/1000000000000 : ℝ) (3968241499/4000000000 : ℝ) (992060374753/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33501/262144 : ℝ)) 2 (992060374877/1000000000000 : ℝ) (992060374879/1000000000000 : ℝ) (3968241499/4000000000 : ℝ) (992060374753/1000000000000 : ℝ) (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ) (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33501/262144 : ℝ)) 3 (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ) (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ) (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ) (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33501/262144 : ℝ)) 4 (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ) (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ) (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ) (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33501/262144 : ℝ)) 5 (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ) (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ) (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ) (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33501/262144 : ℝ)) 6 (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ) (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ) (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ) (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33501/262144 : ℝ)) 7 (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ) (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ) (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ) (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33501/262144 : ℝ))) (11082796483/62500000000 : ℝ) (35464948747/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33501/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11082796483/62500000000 : ℝ) (35464948747/200000000000 : ℝ) (73582796483/125000000000 : ℝ) (147165592967/250000000000 : ℝ) (421099446363/1000000000000 : ℝ) (421099446373/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33501/262144 : ℝ))) 1 (73582796483/125000000000 : ℝ) (147165592967/250000000000 : ℝ) (421099446363/1000000000000 : ℝ) (421099446373/1000000000000 : ℝ) (504880909113/1000000000000 : ℝ) (504880909121/1000000000000 : ℝ) (497880908337/1000000000000 : ℝ) (99576181669/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33501/262144 : ℝ))) 2 (504880909113/1000000000000 : ℝ) (504880909121/1000000000000 : ℝ) (497880908337/1000000000000 : ℝ) (99576181669/200000000000 : ℝ) (20055236349/40000000000 : ℝ) (501380908733/1000000000000 : ℝ) (62671086539/125000000000 : ℝ) (501368692321/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33501/262144 : ℝ))) 3 (20055236349/40000000000 : ℝ) (501380908733/1000000000000 : ℝ) (62671086539/125000000000 : ℝ) (501368692321/1000000000000 : ℝ) (250687400259/500000000000 : ℝ) (501374800527/1000000000000 : ℝ) (501374800481/1000000000000 : ℝ) (50137480049/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33501/262144 : ℝ))) 4 (250687400259/500000000000 : ℝ) (501374800527/1000000000000 : ℝ) (501374800481/1000000000000 : ℝ) (50137480049/100000000000 : ℝ) (501374800499/1000000000000 : ℝ) (501374800509/1000000000000 : ℝ) (501374800499/1000000000000 : ℝ) (501374800509/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33501/262144 : ℝ))) 5 (501374800499/1000000000000 : ℝ) (501374800509/1000000000000 : ℝ) (501374800499/1000000000000 : ℝ) (501374800509/1000000000000 : ℝ) (501374800499/1000000000000 : ℝ) (501374800509/1000000000000 : ℝ) (501374800499/1000000000000 : ℝ) (501374800509/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33501/262144 : ℝ))) 6 (501374800499/1000000000000 : ℝ) (501374800509/1000000000000 : ℝ) (501374800499/1000000000000 : ℝ) (501374800509/1000000000000 : ℝ) (501374800499/1000000000000 : ℝ) (501374800509/1000000000000 : ℝ) (501374800499/1000000000000 : ℝ) (501374800509/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33501/262144 : ℝ))) 7 (501374800499/1000000000000 : ℝ) (501374800509/1000000000000 : ℝ) (501374800499/1000000000000 : ℝ) (501374800509/1000000000000 : ℝ) (501374800499/1000000000000 : ℝ) (501374800509/1000000000000 : ℝ) (501374800499/1000000000000 : ℝ) (501374800509/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33501/262144 : ℝ)) hmem 8 (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ) (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33501/262144 : ℝ))) hcmem 8 (501374800499/1000000000000 : ℝ) (501374800509/1000000000000 : ℝ) (501374800499/1000000000000 : ℝ) (501374800509/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33501/262144 : ℝ)) (992060374813/1000000000000 : ℝ) (31001886713/31250000000 : ℝ) (501374800499/1000000000000 : ℝ) (501374800509/1000000000000 : ℝ) (198465162747/250000000000 : ℝ) (793860651007/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0929_exp_lower
  have heNumeric : (2054901625213/1000000000000 : ℝ)/4 ≤ Real.exp (-85256497313271/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901625213/1000000000000 : ℝ)/4 ≤ Real.exp ((67001/524288 : ℝ)-(793860651007/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67001/524288 : ℝ) (33501/262144 : ℝ) (793860651007/1000000000000 : ℝ) (2054901625213/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0930; no trusted numerical premise.
theorem cover8_leaf0930_exp_radius : (249501286840419259/250000000000000000 : ℝ) ≤ Real.exp ((-67003/4194304 : ℝ)/8) ∧ Real.exp ((-67003/4194304 : ℝ)/8) ≤ (998005147361677037/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67003/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0930_exp_lower : (230028363267102967/250000000000000000 : ℝ) ≤ Real.exp ((-42628248570643/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628248570643/64000000000000 : ℝ)/8) ≤ (920113453068411869/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628248570643/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0930_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450813987/500000000000 : ℝ) ≤ 4*Real.exp (33501/262144 : ℝ)*Real.exp (-mu (radius 8 (67003/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450813987/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67003/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0930_exp_radius
  have hrNumeric : (984152159687/1000000000000 : ℝ) ≤ Real.exp (-67003/4194304 : ℝ) ∧ Real.exp (-67003/4194304 : ℝ) ≤ (123019019961/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984152159687/1000000000000 : ℝ) ≤ (radius 8 (67003/524288 : ℝ)) ∧ (radius 8 (67003/524288 : ℝ)) ≤ (123019019961/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67003/524288 : ℝ)) (984152159687/1000000000000 : ℝ) (123019019961/125000000000 : ℝ) (7093041839/40000000000 : ℝ) (88663022991/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67003/524288 : ℝ)) (984152159687/1000000000000 : ℝ) (123019019961/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67003/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984152159687/1000000000000 : ℝ) (123019019961/125000000000 : ℝ) (992076079843/1000000000000 : ℝ) (248019019961/250000000000 : ℝ) (99204443433/100000000000 : ℝ) (248011108583/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67003/524288 : ℝ)) 1 (992076079843/1000000000000 : ℝ) (248019019961/250000000000 : ℝ) (99204443433/100000000000 : ℝ) (248011108583/250000000000 : ℝ) (496030128543/500000000000 : ℝ) (15500941517/15625000000 : ℝ) (3100188303/3125000000 : ℝ) (496030128481/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67003/524288 : ℝ)) 2 (496030128543/500000000000 : ℝ) (15500941517/15625000000 : ℝ) (3100188303/3125000000 : ℝ) (496030128481/500000000000 : ℝ) (992060257023/1000000000000 : ℝ) (39682410281/40000000000 : ℝ) (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67003/524288 : ℝ)) 3 (992060257023/1000000000000 : ℝ) (39682410281/40000000000 : ℝ) (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ) (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ) (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67003/524288 : ℝ)) 4 (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ) (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ) (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ) (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67003/524288 : ℝ)) 5 (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ) (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ) (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ) (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67003/524288 : ℝ)) 6 (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ) (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ) (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ) (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67003/524288 : ℝ)) 7 (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ) (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ) (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ) (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67003/524288 : ℝ))) (7093041839/40000000000 : ℝ) (88663022991/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67003/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7093041839/40000000000 : ℝ) (88663022991/500000000000 : ℝ) (588663022987/1000000000000 : ℝ) (588663022991/1000000000000 : ℝ) (421100992607/1000000000000 : ℝ) (52637624077/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67003/524288 : ℝ))) 1 (588663022987/1000000000000 : ℝ) (588663022991/1000000000000 : ℝ) (421100992607/1000000000000 : ℝ) (52637624077/125000000000 : ℝ) (504882007797/1000000000000 : ℝ) (126220501951/250000000000 : ℝ) (497882097781/1000000000000 : ℝ) (497882097789/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67003/524288 : ℝ))) 2 (504882007797/1000000000000 : ℝ) (126220501951/250000000000 : ℝ) (497882097781/1000000000000 : ℝ) (497882097789/1000000000000 : ℝ) (501382052789/1000000000000 : ℝ) (501382052797/1000000000000 : ℝ) (501369836721/1000000000000 : ℝ) (501369836729/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67003/524288 : ℝ))) 3 (501382052789/1000000000000 : ℝ) (501382052797/1000000000000 : ℝ) (501369836721/1000000000000 : ℝ) (501369836729/1000000000000 : ℝ) (100275188951/200000000000 : ℝ) (501375944763/1000000000000 : ℝ) (501375944717/1000000000000 : ℝ) (250687972363/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67003/524288 : ℝ))) 4 (100275188951/200000000000 : ℝ) (501375944763/1000000000000 : ℝ) (501375944717/1000000000000 : ℝ) (250687972363/500000000000 : ℝ) (15667998273/31250000000 : ℝ) (100275188949/200000000000 : ℝ) (100275188947/200000000000 : ℝ) (100275188949/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67003/524288 : ℝ))) 5 (15667998273/31250000000 : ℝ) (100275188949/200000000000 : ℝ) (100275188947/200000000000 : ℝ) (100275188949/200000000000 : ℝ) (100275188947/200000000000 : ℝ) (100275188949/200000000000 : ℝ) (100275188947/200000000000 : ℝ) (100275188949/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67003/524288 : ℝ))) 6 (100275188947/200000000000 : ℝ) (100275188949/200000000000 : ℝ) (100275188947/200000000000 : ℝ) (100275188949/200000000000 : ℝ) (100275188947/200000000000 : ℝ) (100275188949/200000000000 : ℝ) (100275188947/200000000000 : ℝ) (100275188949/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67003/524288 : ℝ))) 7 (100275188947/200000000000 : ℝ) (100275188949/200000000000 : ℝ) (100275188947/200000000000 : ℝ) (100275188949/200000000000 : ℝ) (100275188947/200000000000 : ℝ) (100275188949/200000000000 : ℝ) (100275188947/200000000000 : ℝ) (100275188949/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67003/524288 : ℝ)) hmem 8 (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ) (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67003/524288 : ℝ))) hcmem 8 (100275188947/200000000000 : ℝ) (100275188949/200000000000 : ℝ) (100275188947/200000000000 : ℝ) (100275188949/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67003/524288 : ℝ)) (496030128511/500000000000 : ℝ) (39682410281/40000000000 : ℝ) (100275188947/200000000000 : ℝ) (100275188949/200000000000 : ℝ) (793862556993/1000000000000 : ℝ) (198465639253/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0930_exp_lower
  have heNumeric : (1027450813987/500000000000 : ℝ)/4 ≤ Real.exp (-42628248570643/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450813987/500000000000 : ℝ)/4 ≤ Real.exp ((33501/262144 : ℝ)-(198465639253/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33501/262144 : ℝ) (67003/524288 : ℝ) (198465639253/250000000000 : ℝ) (1027450813987/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0931; no trusted numerical premise.
theorem cover8_leaf0931_exp_radius : (998005117618806333/1000000000000000000 : ℝ) ≤ Real.exp ((-16751/1048576 : ℝ)/8) ∧ Real.exp ((-16751/1048576 : ℝ)/8) ≤ (499002558809403167/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16751/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0931_exp_lower : (46005672661262449/50000000000000000 : ℝ) ≤ Real.exp ((-85256496966741/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256496966741/128000000000000 : ℝ)/8) ≤ (920113453225248981/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256496966741/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0931_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862703847/125000000000 : ℝ) ≤ 4*Real.exp (67003/524288 : ℝ)*Real.exp (-mu (radius 8 (16751/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (256862703847/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16751/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0931_exp_radius
  have hrNumeric : (984151925047/1000000000000 : ℝ) ≤ Real.exp (-16751/1048576 : ℝ) ∧ Real.exp (-16751/1048576 : ℝ) ≤ (123018990631/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984151925047/1000000000000 : ℝ) ≤ (radius 8 (16751/131072 : ℝ)) ∧ (radius 8 (16751/131072 : ℝ)) ≤ (123018990631/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16751/131072 : ℝ)) (984151925047/1000000000000 : ℝ) (123018990631/125000000000 : ℝ) (177327348213/1000000000000 : ℝ) (177327348219/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16751/131072 : ℝ)) (984151925047/1000000000000 : ℝ) (123018990631/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16751/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984151925047/1000000000000 : ℝ) (123018990631/125000000000 : ℝ) (992075962523/1000000000000 : ℝ) (248018990631/250000000000 : ℝ) (99204431607/100000000000 : ℝ) (992044316071/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16751/131072 : ℝ)) 1 (992075962523/1000000000000 : ℝ) (248018990631/250000000000 : ℝ) (99204431607/100000000000 : ℝ) (992044316071/1000000000000 : ℝ) (31001879353/31250000000 : ℝ) (496030069649/500000000000 : ℝ) (99206013917/100000000000 : ℝ) (248015034793/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16751/131072 : ℝ)) 2 (31001879353/31250000000 : ℝ) (496030069649/500000000000 : ℝ) (99206013917/100000000000 : ℝ) (248015034793/250000000000 : ℝ) (992060139233/1000000000000 : ℝ) (198412027847/200000000000 : ℝ) (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16751/131072 : ℝ)) 3 (992060139233/1000000000000 : ℝ) (198412027847/200000000000 : ℝ) (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ) (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ) (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16751/131072 : ℝ)) 4 (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ) (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ) (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ) (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16751/131072 : ℝ)) 5 (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ) (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ) (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ) (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16751/131072 : ℝ)) 6 (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ) (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ) (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ) (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16751/131072 : ℝ)) 7 (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ) (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ) (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ) (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16751/131072 : ℝ))) (177327348213/1000000000000 : ℝ) (177327348219/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16751/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177327348213/1000000000000 : ℝ) (177327348219/1000000000000 : ℝ) (294331837053/500000000000 : ℝ) (58866367411/100000000000 : ℝ) (210551269417/500000000000 : ℝ) (210551269421/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16751/131072 : ℝ))) 1 (294331837053/500000000000 : ℝ) (58866367411/100000000000 : ℝ) (210551269417/500000000000 : ℝ) (210551269421/500000000000 : ℝ) (50488310647/100000000000 : ℝ) (126220776619/250000000000 : ℝ) (124470821803/250000000000 : ℝ) (497883287219/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16751/131072 : ℝ))) 2 (50488310647/100000000000 : ℝ) (126220776619/250000000000 : ℝ) (124470821803/250000000000 : ℝ) (497883287219/1000000000000 : ℝ) (501383196841/1000000000000 : ℝ) (31336449803/62500000000 : ℝ) (501370981117/1000000000000 : ℝ) (4010967849/8000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16751/131072 : ℝ))) 3 (501383196841/1000000000000 : ℝ) (31336449803/62500000000 : ℝ) (501370981117/1000000000000 : ℝ) (4010967849/8000000000 : ℝ) (501377088979/1000000000000 : ℝ) (501377088987/1000000000000 : ℝ) (501377088941/1000000000000 : ℝ) (10027541779/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16751/131072 : ℝ))) 4 (501377088979/1000000000000 : ℝ) (501377088987/1000000000000 : ℝ) (501377088941/1000000000000 : ℝ) (10027541779/20000000000 : ℝ) (1566803403/3125000000 : ℝ) (501377088969/1000000000000 : ℝ) (501377088959/1000000000000 : ℝ) (501377088969/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16751/131072 : ℝ))) 5 (1566803403/3125000000 : ℝ) (501377088969/1000000000000 : ℝ) (501377088959/1000000000000 : ℝ) (501377088969/1000000000000 : ℝ) (501377088959/1000000000000 : ℝ) (501377088969/1000000000000 : ℝ) (501377088959/1000000000000 : ℝ) (501377088969/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16751/131072 : ℝ))) 6 (501377088959/1000000000000 : ℝ) (501377088969/1000000000000 : ℝ) (501377088959/1000000000000 : ℝ) (501377088969/1000000000000 : ℝ) (501377088959/1000000000000 : ℝ) (501377088969/1000000000000 : ℝ) (501377088959/1000000000000 : ℝ) (501377088969/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16751/131072 : ℝ))) 7 (501377088959/1000000000000 : ℝ) (501377088969/1000000000000 : ℝ) (501377088959/1000000000000 : ℝ) (501377088969/1000000000000 : ℝ) (501377088959/1000000000000 : ℝ) (501377088969/1000000000000 : ℝ) (501377088959/1000000000000 : ℝ) (501377088969/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16751/131072 : ℝ)) hmem 8 (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ) (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16751/131072 : ℝ))) hcmem 8 (501377088959/1000000000000 : ℝ) (501377088969/1000000000000 : ℝ) (501377088959/1000000000000 : ℝ) (501377088969/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16751/131072 : ℝ)) (31001879351/31250000000 : ℝ) (198412027847/200000000000 : ℝ) (501377088959/1000000000000 : ℝ) (501377088969/1000000000000 : ℝ) (396932231489/500000000000 : ℝ) (793864462997/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0931_exp_lower
  have heNumeric : (256862703847/125000000000 : ℝ)/4 ≤ Real.exp (-85256496966741/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862703847/125000000000 : ℝ)/4 ≤ Real.exp ((67003/524288 : ℝ)-(793864462997/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67003/524288 : ℝ) (16751/131072 : ℝ) (793864462997/1000000000000 : ℝ) (256862703847/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0932; no trusted numerical premise.
theorem cover8_leaf0932_exp_radius : (249501271968984129/250000000000000000 : ℝ) ≤ Real.exp ((-67005/4194304 : ℝ)/8) ∧ Real.exp ((-67005/4194304 : ℝ)/8) ≤ (998005087875936517/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67005/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0932_exp_lower : (920113453384156347/1000000000000000000 : ℝ) ≤ Real.exp ((-21314124197473/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314124197473/32000000000000 : ℝ)/8) ≤ (230028363346039087/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314124197473/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0932_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980326723/200000000000 : ℝ) ≤ 4*Real.exp (16751/131072 : ℝ)*Real.exp (-mu (radius 8 (67005/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980326723/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67005/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0932_exp_radius
  have hrNumeric : (984151690407/1000000000000 : ℝ) ≤ Real.exp (-67005/4194304 : ℝ) ∧ Real.exp (-67005/4194304 : ℝ) ≤ (123018961301/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984151690407/1000000000000 : ℝ) ≤ (radius 8 (67005/524288 : ℝ)) ∧ (radius 8 (67005/524288 : ℝ)) ≤ (123018961301/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67005/524288 : ℝ)) (984151690407/1000000000000 : ℝ) (123018961301/125000000000 : ℝ) (4433216261/25000000000 : ℝ) (177328650447/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67005/524288 : ℝ)) (984151690407/1000000000000 : ℝ) (123018961301/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67005/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984151690407/1000000000000 : ℝ) (123018961301/125000000000 : ℝ) (992075845203/1000000000000 : ℝ) (248018961301/250000000000 : ℝ) (992044197809/1000000000000 : ℝ) (99204419781/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67005/524288 : ℝ)) 1 (992075845203/1000000000000 : ℝ) (248018961301/250000000000 : ℝ) (992044197809/1000000000000 : ℝ) (99204419781/100000000000 : ℝ) (496030010753/500000000000 : ℝ) (992060021507/1000000000000 : ℝ) (992060021379/1000000000000 : ℝ) (992060021381/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67005/524288 : ℝ)) 2 (496030010753/500000000000 : ℝ) (992060021507/1000000000000 : ℝ) (992060021379/1000000000000 : ℝ) (992060021381/1000000000000 : ℝ) (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ) (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67005/524288 : ℝ)) 3 (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ) (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ) (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ) (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67005/524288 : ℝ)) 4 (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ) (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ) (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ) (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67005/524288 : ℝ)) 5 (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ) (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ) (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ) (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67005/524288 : ℝ)) 6 (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ) (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ) (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ) (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67005/524288 : ℝ)) 7 (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ) (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ) (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ) (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67005/524288 : ℝ))) (4433216261/25000000000 : ℝ) (177328650447/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67005/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4433216261/25000000000 : ℝ) (177328650447/1000000000000 : ℝ) (29433216261/50000000000 : ℝ) (73583040653/125000000000 : ℝ) (421104085043/1000000000000 : ℝ) (105276021263/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67005/524288 : ℝ))) 1 (29433216261/50000000000 : ℝ) (73583040653/125000000000 : ℝ) (421104085043/1000000000000 : ℝ) (105276021263/250000000000 : ℝ) (504884205131/1000000000000 : ℝ) (252442102569/500000000000 : ℝ) (49788447663/100000000000 : ℝ) (248942238319/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67005/524288 : ℝ))) 2 (504884205131/1000000000000 : ℝ) (252442102569/500000000000 : ℝ) (49788447663/100000000000 : ℝ) (248942238319/500000000000 : ℝ) (6267304261/12500000000 : ℝ) (62673042611/125000000000 : ℝ) (250686062751/500000000000 : ℝ) (50137212551/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67005/524288 : ℝ))) 3 (6267304261/12500000000 : ℝ) (62673042611/125000000000 : ℝ) (250686062751/500000000000 : ℝ) (50137212551/100000000000 : ℝ) (501378233191/1000000000000 : ℝ) (501378233199/1000000000000 : ℝ) (501378233153/1000000000000 : ℝ) (250689116581/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67005/524288 : ℝ))) 4 (501378233191/1000000000000 : ℝ) (501378233199/1000000000000 : ℝ) (501378233153/1000000000000 : ℝ) (250689116581/500000000000 : ℝ) (125344558293/250000000000 : ℝ) (501378233181/1000000000000 : ℝ) (501378233171/1000000000000 : ℝ) (501378233181/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67005/524288 : ℝ))) 5 (125344558293/250000000000 : ℝ) (501378233181/1000000000000 : ℝ) (501378233171/1000000000000 : ℝ) (501378233181/1000000000000 : ℝ) (501378233171/1000000000000 : ℝ) (501378233181/1000000000000 : ℝ) (501378233171/1000000000000 : ℝ) (501378233181/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67005/524288 : ℝ))) 6 (501378233171/1000000000000 : ℝ) (501378233181/1000000000000 : ℝ) (501378233171/1000000000000 : ℝ) (501378233181/1000000000000 : ℝ) (501378233171/1000000000000 : ℝ) (501378233181/1000000000000 : ℝ) (501378233171/1000000000000 : ℝ) (501378233181/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67005/524288 : ℝ))) 7 (501378233171/1000000000000 : ℝ) (501378233181/1000000000000 : ℝ) (501378233171/1000000000000 : ℝ) (501378233181/1000000000000 : ℝ) (501378233171/1000000000000 : ℝ) (501378233181/1000000000000 : ℝ) (501378233171/1000000000000 : ℝ) (501378233181/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67005/524288 : ℝ)) hmem 8 (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ) (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67005/524288 : ℝ))) hcmem 8 (501378233171/1000000000000 : ℝ) (501378233181/1000000000000 : ℝ) (501378233171/1000000000000 : ℝ) (501378233181/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67005/524288 : ℝ)) (496030010721/500000000000 : ℝ) (248015005361/250000000000 : ℝ) (501378233171/1000000000000 : ℝ) (501378233181/1000000000000 : ℝ) (158773273789/200000000000 : ℝ) (198466592241/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0932_exp_lower
  have heNumeric : (410980326723/200000000000 : ℝ)/4 ≤ Real.exp (-21314124197473/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980326723/200000000000 : ℝ)/4 ≤ Real.exp ((16751/131072 : ℝ)-(198466592241/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16751/131072 : ℝ) (67005/524288 : ℝ) (198466592241/250000000000 : ℝ) (410980326723/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0933; no trusted numerical premise.
theorem cover8_leaf0933_exp_radius : (499002529066533793/500000000000000000 : ℝ) ≤ Real.exp ((-33503/2097152 : ℝ)/8) ∧ Real.exp ((-33503/2097152 : ℝ)/8) ≤ (998005058133067587/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33503/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0933_exp_lower : (460056726772681999/500000000000000000 : ℝ) ≤ Real.exp ((-85256496610483/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256496610483/128000000000000 : ℝ)/8) ≤ (920113453545363999/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256496610483/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0933_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980327299/200000000000 : ℝ) ≤ 4*Real.exp (67005/524288 : ℝ)*Real.exp (-mu (radius 8 (33503/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980327299/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33503/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0933_exp_radius
  have hrNumeric : (984151455767/1000000000000 : ℝ) ≤ Real.exp (-33503/2097152 : ℝ) ∧ Real.exp (-33503/2097152 : ℝ) ≤ (123018931971/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984151455767/1000000000000 : ℝ) ≤ (radius 8 (33503/262144 : ℝ)) ∧ (radius 8 (33503/262144 : ℝ)) ≤ (123018931971/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33503/262144 : ℝ)) (984151455767/1000000000000 : ℝ) (123018931971/125000000000 : ℝ) (88664976329/500000000000 : ℝ) (22166244083/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33503/262144 : ℝ)) (984151455767/1000000000000 : ℝ) (123018931971/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33503/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984151455767/1000000000000 : ℝ) (123018931971/125000000000 : ℝ) (992075727883/1000000000000 : ℝ) (248018931971/250000000000 : ℝ) (248011019887/250000000000 : ℝ) (992044079549/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33503/262144 : ℝ)) 1 (992075727883/1000000000000 : ℝ) (248018931971/250000000000 : ℝ) (248011019887/250000000000 : ℝ) (992044079549/1000000000000 : ℝ) (198411980743/200000000000 : ℝ) (992059903717/1000000000000 : ℝ) (992059903589/1000000000000 : ℝ) (992059903591/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33503/262144 : ℝ)) 2 (198411980743/200000000000 : ℝ) (992059903717/1000000000000 : ℝ) (992059903589/1000000000000 : ℝ) (992059903591/1000000000000 : ℝ) (248014975913/250000000000 : ℝ) (496029951827/500000000000 : ℝ) (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33503/262144 : ℝ)) 3 (248014975913/250000000000 : ℝ) (496029951827/500000000000 : ℝ) (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ) (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ) (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33503/262144 : ℝ)) 4 (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ) (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ) (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ) (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33503/262144 : ℝ)) 5 (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ) (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ) (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ) (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33503/262144 : ℝ)) 6 (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ) (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ) (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ) (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33503/262144 : ℝ)) 7 (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ) (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ) (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ) (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33503/262144 : ℝ))) (88664976329/500000000000 : ℝ) (22166244083/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33503/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88664976329/500000000000 : ℝ) (22166244083/125000000000 : ℝ) (588664976329/1000000000000 : ℝ) (147166244083/250000000000 : ℝ) (84221126247/200000000000 : ℝ) (421105631243/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33503/262144 : ℝ))) 1 (588664976329/1000000000000 : ℝ) (147166244083/250000000000 : ℝ) (84221126247/200000000000 : ℝ) (421105631243/1000000000000 : ℝ) (252442651891/500000000000 : ℝ) (126221325947/250000000000 : ℝ) (248942833017/500000000000 : ℝ) (497885666041/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33503/262144 : ℝ))) 2 (252442651891/500000000000 : ℝ) (126221325947/250000000000 : ℝ) (248942833017/500000000000 : ℝ) (497885666041/1000000000000 : ℝ) (125346371227/250000000000 : ℝ) (100277096983/200000000000 : ℝ) (250686634937/500000000000 : ℝ) (501373269881/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33503/262144 : ℝ))) 3 (125346371227/250000000000 : ℝ) (100277096983/200000000000 : ℝ) (250686634937/500000000000 : ℝ) (501373269881/1000000000000 : ℝ) (501379377391/1000000000000 : ℝ) (250689688699/500000000000 : ℝ) (501379377353/1000000000000 : ℝ) (501379377361/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33503/262144 : ℝ))) 4 (501379377391/1000000000000 : ℝ) (250689688699/500000000000 : ℝ) (501379377353/1000000000000 : ℝ) (501379377361/1000000000000 : ℝ) (125344844343/250000000000 : ℝ) (25068968869/50000000000 : ℝ) (501379377371/1000000000000 : ℝ) (25068968869/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33503/262144 : ℝ))) 5 (125344844343/250000000000 : ℝ) (25068968869/50000000000 : ℝ) (501379377371/1000000000000 : ℝ) (25068968869/50000000000 : ℝ) (501379377371/1000000000000 : ℝ) (25068968869/50000000000 : ℝ) (501379377371/1000000000000 : ℝ) (25068968869/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33503/262144 : ℝ))) 6 (501379377371/1000000000000 : ℝ) (25068968869/50000000000 : ℝ) (501379377371/1000000000000 : ℝ) (25068968869/50000000000 : ℝ) (501379377371/1000000000000 : ℝ) (25068968869/50000000000 : ℝ) (501379377371/1000000000000 : ℝ) (25068968869/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33503/262144 : ℝ))) 7 (501379377371/1000000000000 : ℝ) (25068968869/50000000000 : ℝ) (501379377371/1000000000000 : ℝ) (25068968869/50000000000 : ℝ) (501379377371/1000000000000 : ℝ) (25068968869/50000000000 : ℝ) (501379377371/1000000000000 : ℝ) (25068968869/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33503/262144 : ℝ)) hmem 8 (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ) (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33503/262144 : ℝ))) hcmem 8 (501379377371/1000000000000 : ℝ) (25068968869/50000000000 : ℝ) (501379377371/1000000000000 : ℝ) (25068968869/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33503/262144 : ℝ)) (992059903651/1000000000000 : ℝ) (496029951827/500000000000 : ℝ) (501379377371/1000000000000 : ℝ) (25068968869/50000000000 : ℝ) (793868274893/1000000000000 : ℝ) (793868274911/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0933_exp_lower
  have heNumeric : (410980327299/200000000000 : ℝ)/4 ≤ Real.exp (-85256496610483/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980327299/200000000000 : ℝ)/4 ≤ Real.exp ((67005/524288 : ℝ)-(793868274911/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67005/524288 : ℝ) (33503/262144 : ℝ) (793868274911/1000000000000 : ℝ) (410980327299/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0934; no trusted numerical premise.
theorem cover8_leaf0934_exp_radius : (499002514195099771/500000000000000000 : ℝ) ≤ Real.exp ((-67007/4194304 : ℝ)/8) ∧ Real.exp ((-67007/4194304 : ℝ)/8) ≤ (998005028390199543/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67007/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0934_exp_lower : (184022690741728381/200000000000000000 : ℝ) ≤ Real.exp ((-8525649642877/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525649642877/12800000000000 : ℝ)/8) ≤ (460056726854320953/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525649642877/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0934_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901639413/1000000000000 : ℝ) ≤ 4*Real.exp (33503/262144 : ℝ)*Real.exp (-mu (radius 8 (67007/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901639413/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67007/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0934_exp_radius
  have hrNumeric : (984151221127/1000000000000 : ℝ) ≤ Real.exp (-67007/4194304 : ℝ) ∧ Real.exp (-67007/4194304 : ℝ) ≤ (123018902641/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984151221127/1000000000000 : ℝ) ≤ (radius 8 (67007/524288 : ℝ)) ∧ (radius 8 (67007/524288 : ℝ)) ≤ (123018902641/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67007/524288 : ℝ)) (984151221127/1000000000000 : ℝ) (123018902641/125000000000 : ℝ) (35466250973/200000000000 : ℝ) (22166406859/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67007/524288 : ℝ)) (984151221127/1000000000000 : ℝ) (123018902641/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67007/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984151221127/1000000000000 : ℝ) (123018902641/125000000000 : ℝ) (992075610563/1000000000000 : ℝ) (248018902641/250000000000 : ℝ) (992043961287/1000000000000 : ℝ) (992043961289/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67007/524288 : ℝ)) 1 (992075610563/1000000000000 : ℝ) (248018902641/250000000000 : ℝ) (992043961287/1000000000000 : ℝ) (992043961289/1000000000000 : ℝ) (39682391437/40000000000 : ℝ) (992059785927/1000000000000 : ℝ) (496029892899/500000000000 : ℝ) (992059785801/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67007/524288 : ℝ)) 2 (39682391437/40000000000 : ℝ) (992059785927/1000000000000 : ℝ) (496029892899/500000000000 : ℝ) (992059785801/1000000000000 : ℝ) (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ) (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67007/524288 : ℝ)) 3 (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ) (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ) (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ) (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67007/524288 : ℝ)) 4 (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ) (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ) (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ) (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67007/524288 : ℝ)) 5 (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ) (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ) (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ) (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67007/524288 : ℝ)) 6 (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ) (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ) (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ) (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67007/524288 : ℝ)) 7 (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ) (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ) (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ) (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67007/524288 : ℝ))) (35466250973/200000000000 : ℝ) (22166406859/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67007/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35466250973/200000000000 : ℝ) (22166406859/125000000000 : ℝ) (73583203429/125000000000 : ℝ) (147166406859/250000000000 : ℝ) (6579799647/15625000000 : ℝ) (421107177417/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67007/524288 : ℝ))) 1 (73583203429/125000000000 : ℝ) (147166406859/250000000000 : ℝ) (6579799647/15625000000 : ℝ) (421107177417/1000000000000 : ℝ) (25244320121/50000000000 : ℝ) (504886402427/1000000000000 : ℝ) (19915474217/40000000000 : ℝ) (497886855433/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67007/524288 : ℝ))) 2 (25244320121/50000000000 : ℝ) (504886402427/1000000000000 : ℝ) (19915474217/40000000000 : ℝ) (497886855433/1000000000000 : ℝ) (250693314461/500000000000 : ℝ) (50138662893/100000000000 : ℝ) (501374414233/1000000000000 : ℝ) (501374414241/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67007/524288 : ℝ))) 3 (250693314461/500000000000 : ℝ) (50138662893/100000000000 : ℝ) (501374414233/1000000000000 : ℝ) (501374414241/1000000000000 : ℝ) (501380521577/1000000000000 : ℝ) (250690260793/500000000000 : ℝ) (25069026077/50000000000 : ℝ) (501380521549/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67007/524288 : ℝ))) 4 (501380521577/1000000000000 : ℝ) (250690260793/500000000000 : ℝ) (25069026077/50000000000 : ℝ) (501380521549/1000000000000 : ℝ) (250690260779/500000000000 : ℝ) (15668141299/31250000000 : ℝ) (250690260779/500000000000 : ℝ) (15668141299/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67007/524288 : ℝ))) 5 (250690260779/500000000000 : ℝ) (15668141299/31250000000 : ℝ) (250690260779/500000000000 : ℝ) (15668141299/31250000000 : ℝ) (250690260779/500000000000 : ℝ) (15668141299/31250000000 : ℝ) (250690260779/500000000000 : ℝ) (15668141299/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67007/524288 : ℝ))) 6 (250690260779/500000000000 : ℝ) (15668141299/31250000000 : ℝ) (250690260779/500000000000 : ℝ) (15668141299/31250000000 : ℝ) (250690260779/500000000000 : ℝ) (15668141299/31250000000 : ℝ) (250690260779/500000000000 : ℝ) (15668141299/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67007/524288 : ℝ))) 7 (250690260779/500000000000 : ℝ) (15668141299/31250000000 : ℝ) (250690260779/500000000000 : ℝ) (15668141299/31250000000 : ℝ) (250690260779/500000000000 : ℝ) (15668141299/31250000000 : ℝ) (250690260779/500000000000 : ℝ) (15668141299/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67007/524288 : ℝ)) hmem 8 (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ) (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67007/524288 : ℝ))) hcmem 8 (250690260779/500000000000 : ℝ) (15668141299/31250000000 : ℝ) (250690260779/500000000000 : ℝ) (15668141299/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67007/524288 : ℝ)) (992059785861/1000000000000 : ℝ) (124007473233/125000000000 : ℝ) (250690260779/500000000000 : ℝ) (15668141299/31250000000 : ℝ) (793870180821/1000000000000 : ℝ) (19846754521/25000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0934_exp_lower
  have heNumeric : (2054901639413/1000000000000 : ℝ)/4 ≤ Real.exp (-8525649642877/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901639413/1000000000000 : ℝ)/4 ≤ Real.exp ((33503/262144 : ℝ)-(19846754521/25000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33503/262144 : ℝ) (67007/524288 : ℝ) (19846754521/25000000000 : ℝ) (2054901639413/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0935; no trusted numerical premise.
theorem cover8_leaf0935_exp_radius : (199600999729466477/200000000000000000 : ℝ) ≤ Real.exp ((-1047/65536 : ℝ)/8) ∧ Real.exp ((-1047/65536 : ℝ)/8) ≤ (499002499323666193/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1047/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0935_exp_lower : (460056726936995033/500000000000000000 : ℝ) ≤ Real.exp ((-85256496244753/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256496244753/128000000000000 : ℝ)/8) ≤ (920113453873990067/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256496244753/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0935_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901642367/1000000000000 : ℝ) ≤ 4*Real.exp (67007/524288 : ℝ)*Real.exp (-mu (radius 8 (1047/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901642367/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1047/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0935_exp_radius
  have hrNumeric : (984150986487/1000000000000 : ℝ) ≤ Real.exp (-1047/65536 : ℝ) ∧ Real.exp (-1047/65536 : ℝ) ≤ (123018873311/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984150986487/1000000000000 : ℝ) ≤ (radius 8 (1047/8192 : ℝ)) ∧ (radius 8 (1047/8192 : ℝ)) ≤ (123018873311/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1047/8192 : ℝ)) (984150986487/1000000000000 : ℝ) (123018873311/125000000000 : ℝ) (177332557063/1000000000000 : ℝ) (17733255707/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1047/8192 : ℝ)) (984150986487/1000000000000 : ℝ) (123018873311/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1047/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984150986487/1000000000000 : ℝ) (123018873311/125000000000 : ℝ) (992075493243/1000000000000 : ℝ) (248018873311/250000000000 : ℝ) (496021921513/500000000000 : ℝ) (248010960757/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1047/8192 : ℝ)) 1 (992075493243/1000000000000 : ℝ) (248018873311/250000000000 : ℝ) (496021921513/500000000000 : ℝ) (248010960757/250000000000 : ℝ) (496029834067/500000000000 : ℝ) (124007458517/125000000000 : ℝ) (124007458501/125000000000 : ℝ) (99205966801/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1047/8192 : ℝ)) 2 (496029834067/500000000000 : ℝ) (124007458517/125000000000 : ℝ) (124007458501/125000000000 : ℝ) (99205966801/100000000000 : ℝ) (992059668071/1000000000000 : ℝ) (992059668073/1000000000000 : ℝ) (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1047/8192 : ℝ)) 3 (992059668071/1000000000000 : ℝ) (992059668073/1000000000000 : ℝ) (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ) (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ) (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1047/8192 : ℝ)) 4 (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ) (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ) (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ) (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1047/8192 : ℝ)) 5 (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ) (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ) (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ) (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1047/8192 : ℝ)) 6 (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ) (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ) (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ) (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1047/8192 : ℝ)) 7 (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ) (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ) (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ) (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1047/8192 : ℝ))) (177332557063/1000000000000 : ℝ) (17733255707/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1047/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177332557063/1000000000000 : ℝ) (17733255707/100000000000 : ℝ) (588666278531/1000000000000 : ℝ) (117733255707/200000000000 : ℝ) (84221744713/200000000000 : ℝ) (210554361787/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1047/8192 : ℝ))) 1 (588666278531/1000000000000 : ℝ) (117733255707/200000000000 : ℝ) (84221744713/200000000000 : ℝ) (210554361787/500000000000 : ℝ) (63110937631/125000000000 : ℝ) (100977500211/200000000000 : ℝ) (497888044803/1000000000000 : ℝ) (497888044811/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1047/8192 : ℝ))) 2 (63110937631/125000000000 : ℝ) (100977500211/200000000000 : ℝ) (497888044803/1000000000000 : ℝ) (497888044811/1000000000000 : ℝ) (20055510917/40000000000 : ℝ) (501387772933/1000000000000 : ℝ) (25068777929/50000000000 : ℝ) (501375558589/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1047/8192 : ℝ))) 3 (20055510917/40000000000 : ℝ) (501387772933/1000000000000 : ℝ) (25068777929/50000000000 : ℝ) (501375558589/1000000000000 : ℝ) (62672708219/125000000000 : ℝ) (501381665761/1000000000000 : ℝ) (100276333143/200000000000 : ℝ) (125345416431/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1047/8192 : ℝ))) 4 (62672708219/125000000000 : ℝ) (501381665761/1000000000000 : ℝ) (100276333143/200000000000 : ℝ) (125345416431/250000000000 : ℝ) (501381665733/1000000000000 : ℝ) (501381665743/1000000000000 : ℝ) (501381665733/1000000000000 : ℝ) (501381665743/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1047/8192 : ℝ))) 5 (501381665733/1000000000000 : ℝ) (501381665743/1000000000000 : ℝ) (501381665733/1000000000000 : ℝ) (501381665743/1000000000000 : ℝ) (501381665733/1000000000000 : ℝ) (501381665743/1000000000000 : ℝ) (501381665733/1000000000000 : ℝ) (501381665743/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1047/8192 : ℝ))) 6 (501381665733/1000000000000 : ℝ) (501381665743/1000000000000 : ℝ) (501381665733/1000000000000 : ℝ) (501381665743/1000000000000 : ℝ) (501381665733/1000000000000 : ℝ) (501381665743/1000000000000 : ℝ) (501381665733/1000000000000 : ℝ) (501381665743/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1047/8192 : ℝ))) 7 (501381665733/1000000000000 : ℝ) (501381665743/1000000000000 : ℝ) (501381665733/1000000000000 : ℝ) (501381665743/1000000000000 : ℝ) (501381665733/1000000000000 : ℝ) (501381665743/1000000000000 : ℝ) (501381665733/1000000000000 : ℝ) (501381665743/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1047/8192 : ℝ)) hmem 8 (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ) (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1047/8192 : ℝ))) hcmem 8 (501381665733/1000000000000 : ℝ) (501381665743/1000000000000 : ℝ) (501381665733/1000000000000 : ℝ) (501381665743/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1047/8192 : ℝ)) (99205966807/100000000000 : ℝ) (992059668073/1000000000000 : ℝ) (501381665733/1000000000000 : ℝ) (501381665743/1000000000000 : ℝ) (793872086731/1000000000000 : ℝ) (793872086751/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0935_exp_lower
  have heNumeric : (2054901642367/1000000000000 : ℝ)/4 ≤ Real.exp (-85256496244753/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901642367/1000000000000 : ℝ)/4 ≤ Real.exp ((67007/524288 : ℝ)-(793872086751/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67007/524288 : ℝ) (1047/8192 : ℝ) (793872086751/1000000000000 : ℝ) (2054901642367/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0936; no trusted numerical premise.
theorem cover8_leaf0936_exp_radius : (499002484452233057/500000000000000000 : ℝ) ≤ Real.exp ((-67009/4194304 : ℝ)/8) ∧ Real.exp ((-67009/4194304 : ℝ)/8) ≤ (199600993780893223/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67009/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0936_exp_lower : (920113454041638511/1000000000000000000 : ℝ) ≤ Real.exp ((-1332132750909/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332132750909/2000000000000 : ℝ)/8) ≤ (57507090877602407/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332132750909/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0936_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450822681/500000000000 : ℝ) ≤ 4*Real.exp (1047/8192 : ℝ)*Real.exp (-mu (radius 8 (67009/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450822681/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67009/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0936_exp_radius
  have hrNumeric : (984150751847/1000000000000 : ℝ) ≤ Real.exp (-67009/4194304 : ℝ) ∧ Real.exp (-67009/4194304 : ℝ) ≤ (123018843981/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984150751847/1000000000000 : ℝ) ≤ (radius 8 (67009/524288 : ℝ)) ∧ (radius 8 (67009/524288 : ℝ)) ≤ (123018843981/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67009/524288 : ℝ)) (984150751847/1000000000000 : ℝ) (123018843981/125000000000 : ℝ) (177333859251/1000000000000 : ℝ) (88666929629/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67009/524288 : ℝ)) (984150751847/1000000000000 : ℝ) (123018843981/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67009/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984150751847/1000000000000 : ℝ) (123018843981/125000000000 : ℝ) (992075375923/1000000000000 : ℝ) (248018843981/250000000000 : ℝ) (198408744953/200000000000 : ℝ) (992043724767/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67009/524288 : ℝ)) 1 (992075375923/1000000000000 : ℝ) (248018843981/250000000000 : ℝ) (198408744953/200000000000 : ℝ) (992043724767/1000000000000 : ℝ) (124007443793/125000000000 : ℝ) (496029775173/500000000000 : ℝ) (992059550217/1000000000000 : ℝ) (49602977511/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67009/524288 : ℝ)) 2 (124007443793/125000000000 : ℝ) (496029775173/500000000000 : ℝ) (992059550217/1000000000000 : ℝ) (49602977511/50000000000 : ℝ) (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ) (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67009/524288 : ℝ)) 3 (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ) (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ) (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ) (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67009/524288 : ℝ)) 4 (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ) (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ) (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ) (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67009/524288 : ℝ)) 5 (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ) (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ) (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ) (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67009/524288 : ℝ)) 6 (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ) (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ) (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ) (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67009/524288 : ℝ)) 7 (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ) (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ) (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ) (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67009/524288 : ℝ))) (177333859251/1000000000000 : ℝ) (88666929629/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67009/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177333859251/1000000000000 : ℝ) (88666929629/500000000000 : ℝ) (4709335437/8000000000 : ℝ) (588666929629/1000000000000 : ℝ) (52638783713/125000000000 : ℝ) (210555134857/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67009/524288 : ℝ))) 1 (4709335437/8000000000 : ℝ) (588666929629/1000000000000 : ℝ) (52638783713/125000000000 : ℝ) (210555134857/500000000000 : ℝ) (31555537479/62500000000 : ℝ) (63111074959/125000000000 : ℝ) (497889234167/1000000000000 : ℝ) (1944879821/3906250000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67009/524288 : ℝ))) 2 (31555537479/62500000000 : ℝ) (63111074959/125000000000 : ℝ) (497889234167/1000000000000 : ℝ) (1944879821/3906250000 : ℝ) (100277783383/200000000000 : ℝ) (125347229231/250000000000 : ℝ) (100275340583/200000000000 : ℝ) (125344175731/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67009/524288 : ℝ))) 3 (100277783383/200000000000 : ℝ) (125347229231/250000000000 : ℝ) (100275340583/200000000000 : ℝ) (125344175731/250000000000 : ℝ) (100276561983/200000000000 : ℝ) (125345702481/250000000000 : ℝ) (501382809877/1000000000000 : ℝ) (501382809887/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67009/524288 : ℝ))) 4 (100276561983/200000000000 : ℝ) (125345702481/250000000000 : ℝ) (501382809877/1000000000000 : ℝ) (501382809887/1000000000000 : ℝ) (62672851237/125000000000 : ℝ) (250691404953/500000000000 : ℝ) (100276561979/200000000000 : ℝ) (250691404953/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67009/524288 : ℝ))) 5 (62672851237/125000000000 : ℝ) (250691404953/500000000000 : ℝ) (100276561979/200000000000 : ℝ) (250691404953/500000000000 : ℝ) (100276561979/200000000000 : ℝ) (250691404953/500000000000 : ℝ) (100276561979/200000000000 : ℝ) (250691404953/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67009/524288 : ℝ))) 6 (100276561979/200000000000 : ℝ) (250691404953/500000000000 : ℝ) (100276561979/200000000000 : ℝ) (250691404953/500000000000 : ℝ) (100276561979/200000000000 : ℝ) (250691404953/500000000000 : ℝ) (100276561979/200000000000 : ℝ) (250691404953/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67009/524288 : ℝ))) 7 (100276561979/200000000000 : ℝ) (250691404953/500000000000 : ℝ) (100276561979/200000000000 : ℝ) (250691404953/500000000000 : ℝ) (100276561979/200000000000 : ℝ) (250691404953/500000000000 : ℝ) (100276561979/200000000000 : ℝ) (250691404953/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67009/524288 : ℝ)) hmem 8 (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ) (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67009/524288 : ℝ))) hcmem 8 (100276561979/200000000000 : ℝ) (250691404953/500000000000 : ℝ) (100276561979/200000000000 : ℝ) (250691404953/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67009/524288 : ℝ)) (24801488757/25000000000 : ℝ) (992059550283/1000000000000 : ℝ) (100276561979/200000000000 : ℝ) (250691404953/500000000000 : ℝ) (793873992621/1000000000000 : ℝ) (396936996321/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0936_exp_lower
  have heNumeric : (1027450822681/500000000000 : ℝ)/4 ≤ Real.exp (-1332132750909/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450822681/500000000000 : ℝ)/4 ≤ Real.exp ((1047/8192 : ℝ)-(396936996321/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1047/8192 : ℝ) (67009/524288 : ℝ) (396936996321/500000000000 : ℝ) (1027450822681/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0937; no trusted numerical premise.
theorem cover8_leaf0937_exp_radius : (998004939161600729/1000000000000000000 : ℝ) ≤ Real.exp ((-33505/2097152 : ℝ)/8) ∧ Real.exp ((-33505/2097152 : ℝ)/8) ≤ (99800493916160073/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33505/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0937_exp_lower : (460056727105621099/500000000000000000 : ℝ) ≤ Real.exp ((-85256495869423/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256495869423/128000000000000 : ℝ)/8) ≤ (920113454211242199/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256495869423/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0937_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862706049/125000000000 : ℝ) ≤ 4*Real.exp (67009/524288 : ℝ)*Real.exp (-mu (radius 8 (33505/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256862706049/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33505/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0937_exp_radius
  have hrNumeric : (984150517207/1000000000000 : ℝ) ≤ Real.exp (-33505/2097152 : ℝ) ∧ Real.exp (-33505/2097152 : ℝ) ≤ (123018814651/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984150517207/1000000000000 : ℝ) ≤ (radius 8 (33505/262144 : ℝ)) ∧ (radius 8 (33505/262144 : ℝ)) ≤ (123018814651/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33505/262144 : ℝ)) (984150517207/1000000000000 : ℝ) (123018814651/125000000000 : ℝ) (177335161429/1000000000000 : ℝ) (44333790359/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33505/262144 : ℝ)) (984150517207/1000000000000 : ℝ) (123018814651/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33505/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984150517207/1000000000000 : ℝ) (123018814651/125000000000 : ℝ) (992075258603/1000000000000 : ℝ) (248018814651/250000000000 : ℝ) (124005450813/125000000000 : ℝ) (496021803253/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33505/262144 : ℝ)) 1 (992075258603/1000000000000 : ℝ) (248018814651/250000000000 : ℝ) (124005450813/125000000000 : ℝ) (496021803253/500000000000 : ℝ) (992059432553/1000000000000 : ℝ) (198411886511/200000000000 : ℝ) (992059432427/1000000000000 : ℝ) (992059432429/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33505/262144 : ℝ)) 2 (992059432553/1000000000000 : ℝ) (198411886511/200000000000 : ℝ) (992059432427/1000000000000 : ℝ) (992059432429/1000000000000 : ℝ) (99205943249/100000000000 : ℝ) (248014858123/250000000000 : ℝ) (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33505/262144 : ℝ)) 3 (99205943249/100000000000 : ℝ) (248014858123/250000000000 : ℝ) (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ) (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ) (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33505/262144 : ℝ)) 4 (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ) (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ) (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ) (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33505/262144 : ℝ)) 5 (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ) (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ) (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ) (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33505/262144 : ℝ)) 6 (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ) (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ) (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ) (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33505/262144 : ℝ)) 7 (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ) (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ) (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ) (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33505/262144 : ℝ))) (177335161429/1000000000000 : ℝ) (44333790359/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33505/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177335161429/1000000000000 : ℝ) (44333790359/250000000000 : ℝ) (294333790357/500000000000 : ℝ) (294333790359/500000000000 : ℝ) (210555907913/500000000000 : ℝ) (105277953959/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33505/262144 : ℝ))) 1 (294333790357/500000000000 : ℝ) (294333790359/500000000000 : ℝ) (210555907913/500000000000 : ℝ) (105277953959/250000000000 : ℝ) (50488969827/100000000000 : ℝ) (504889698277/1000000000000 : ℝ) (497890423519/1000000000000 : ℝ) (62236302941/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33505/262144 : ℝ))) 2 (50488969827/100000000000 : ℝ) (504889698277/1000000000000 : ℝ) (497890423519/1000000000000 : ℝ) (62236302941/125000000000 : ℝ) (250695030447/500000000000 : ℝ) (501390060903/1000000000000 : ℝ) (501377847239/1000000000000 : ℝ) (31336115453/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33505/262144 : ℝ))) 3 (250695030447/500000000000 : ℝ) (501390060903/1000000000000 : ℝ) (501377847239/1000000000000 : ℝ) (31336115453/62500000000 : ℝ) (250691977033/500000000000 : ℝ) (125345988519/250000000000 : ℝ) (501383954029/1000000000000 : ℝ) (501383954039/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33505/262144 : ℝ))) 4 (250691977033/500000000000 : ℝ) (125345988519/250000000000 : ℝ) (501383954029/1000000000000 : ℝ) (501383954039/1000000000000 : ℝ) (501383954047/1000000000000 : ℝ) (250691977029/500000000000 : ℝ) (501383954047/1000000000000 : ℝ) (250691977029/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33505/262144 : ℝ))) 5 (501383954047/1000000000000 : ℝ) (250691977029/500000000000 : ℝ) (501383954047/1000000000000 : ℝ) (250691977029/500000000000 : ℝ) (501383954047/1000000000000 : ℝ) (250691977029/500000000000 : ℝ) (501383954047/1000000000000 : ℝ) (250691977029/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33505/262144 : ℝ))) 6 (501383954047/1000000000000 : ℝ) (250691977029/500000000000 : ℝ) (501383954047/1000000000000 : ℝ) (250691977029/500000000000 : ℝ) (501383954047/1000000000000 : ℝ) (250691977029/500000000000 : ℝ) (501383954047/1000000000000 : ℝ) (250691977029/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33505/262144 : ℝ))) 7 (501383954047/1000000000000 : ℝ) (250691977029/500000000000 : ℝ) (501383954047/1000000000000 : ℝ) (250691977029/500000000000 : ℝ) (501383954047/1000000000000 : ℝ) (250691977029/500000000000 : ℝ) (501383954047/1000000000000 : ℝ) (250691977029/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33505/262144 : ℝ)) hmem 8 (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ) (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33505/262144 : ℝ))) hcmem 8 (501383954047/1000000000000 : ℝ) (250691977029/500000000000 : ℝ) (501383954047/1000000000000 : ℝ) (250691977029/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33505/262144 : ℝ)) (992059432489/1000000000000 : ℝ) (248014858123/250000000000 : ℝ) (501383954047/1000000000000 : ℝ) (250691977029/500000000000 : ℝ) (158775179699/200000000000 : ℝ) (198468974629/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0937_exp_lower
  have heNumeric : (256862706049/125000000000 : ℝ)/4 ≤ Real.exp (-85256495869423/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862706049/125000000000 : ℝ)/4 ≤ Real.exp ((67009/524288 : ℝ)-(198468974629/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67009/524288 : ℝ) (33505/262144 : ℝ) (198468974629/250000000000 : ℝ) (256862706049/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0938; no trusted numerical premise.
theorem cover8_leaf0938_exp_radius : (998004909418736231/1000000000000000000 : ℝ) ≤ Real.exp ((-67011/4194304 : ℝ)/8) ∧ Real.exp ((-67011/4194304 : ℝ)/8) ≤ (124750613677342029/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67011/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0938_exp_lower : (460056727192263169/500000000000000000 : ℝ) ≤ Real.exp ((-42628247838287/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628247838287/64000000000000 : ℝ)/8) ≤ (920113454384526339/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628247838287/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0938_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (64215676609/31250000000 : ℝ) ≤ 4*Real.exp (33505/262144 : ℝ)*Real.exp (-mu (radius 8 (67011/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (64215676609/31250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67011/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0938_exp_radius
  have hrNumeric : (123018785321/125000000000 : ℝ) ≤ Real.exp (-67011/4194304 : ℝ) ∧ Real.exp (-67011/4194304 : ℝ) ≤ (984150282569/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123018785321/125000000000 : ℝ) ≤ (radius 8 (67011/524288 : ℝ)) ∧ (radius 8 (67011/524288 : ℝ)) ≤ (984150282569/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67011/524288 : ℝ)) (123018785321/125000000000 : ℝ) (984150282569/1000000000000 : ℝ) (22167057949/125000000000 : ℝ) (88668231799/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67011/524288 : ℝ)) (123018785321/125000000000 : ℝ) (984150282569/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67011/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123018785321/125000000000 : ℝ) (984150282569/1000000000000 : ℝ) (248018785321/250000000000 : ℝ) (198415028257/200000000000 : ℝ) (248010872061/250000000000 : ℝ) (198408697649/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67011/524288 : ℝ)) 1 (248018785321/250000000000 : ℝ) (198415028257/200000000000 : ℝ) (248010872061/250000000000 : ℝ) (198408697649/200000000000 : ℝ) (248014828691/250000000000 : ℝ) (198411862953/200000000000 : ℝ) (992059314637/1000000000000 : ℝ) (992059314639/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67011/524288 : ℝ)) 2 (248014828691/250000000000 : ℝ) (198411862953/200000000000 : ℝ) (992059314637/1000000000000 : ℝ) (992059314639/1000000000000 : ℝ) (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ) (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67011/524288 : ℝ)) 3 (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ) (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ) (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ) (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67011/524288 : ℝ)) 4 (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ) (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ) (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ) (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67011/524288 : ℝ)) 5 (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ) (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ) (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ) (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67011/524288 : ℝ)) 6 (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ) (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ) (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ) (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67011/524288 : ℝ)) 7 (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ) (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ) (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ) (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67011/524288 : ℝ))) (22167057949/125000000000 : ℝ) (88668231799/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67011/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22167057949/125000000000 : ℝ) (88668231799/500000000000 : ℝ) (147167057949/250000000000 : ℝ) (588668231799/1000000000000 : ℝ) (16844534477/40000000000 : ℝ) (421113361933/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67011/524288 : ℝ))) 1 (147167057949/250000000000 : ℝ) (588668231799/1000000000000 : ℝ) (16844534477/40000000000 : ℝ) (421113361933/1000000000000 : ℝ) (25244539843/50000000000 : ℝ) (252445398433/500000000000 : ℝ) (497891612853/1000000000000 : ℝ) (24894580643/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67011/524288 : ℝ))) 2 (25244539843/50000000000 : ℝ) (252445398433/500000000000 : ℝ) (497891612853/1000000000000 : ℝ) (24894580643/50000000000 : ℝ) (62673900607/125000000000 : ℝ) (501391204863/1000000000000 : ℝ) (100275798309/200000000000 : ℝ) (501378991553/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67011/524288 : ℝ))) 3 (62673900607/125000000000 : ℝ) (501391204863/1000000000000 : ℝ) (100275798309/200000000000 : ℝ) (501378991553/1000000000000 : ℝ) (2506925491/5000000000 : ℝ) (15668284319/31250000000 : ℝ) (501385098163/1000000000000 : ℝ) (501385098171/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67011/524288 : ℝ))) 4 (2506925491/5000000000 : ℝ) (15668284319/31250000000 : ℝ) (501385098163/1000000000000 : ℝ) (501385098171/1000000000000 : ℝ) (501385098181/1000000000000 : ℝ) (50138509819/100000000000 : ℝ) (501385098181/1000000000000 : ℝ) (50138509819/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67011/524288 : ℝ))) 5 (501385098181/1000000000000 : ℝ) (50138509819/100000000000 : ℝ) (501385098181/1000000000000 : ℝ) (50138509819/100000000000 : ℝ) (501385098181/1000000000000 : ℝ) (50138509819/100000000000 : ℝ) (501385098181/1000000000000 : ℝ) (50138509819/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67011/524288 : ℝ))) 6 (501385098181/1000000000000 : ℝ) (50138509819/100000000000 : ℝ) (501385098181/1000000000000 : ℝ) (50138509819/100000000000 : ℝ) (501385098181/1000000000000 : ℝ) (50138509819/100000000000 : ℝ) (501385098181/1000000000000 : ℝ) (50138509819/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67011/524288 : ℝ))) 7 (501385098181/1000000000000 : ℝ) (50138509819/100000000000 : ℝ) (501385098181/1000000000000 : ℝ) (50138509819/100000000000 : ℝ) (501385098181/1000000000000 : ℝ) (50138509819/100000000000 : ℝ) (501385098181/1000000000000 : ℝ) (50138509819/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67011/524288 : ℝ)) hmem 8 (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ) (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67011/524288 : ℝ))) hcmem 8 (501385098181/1000000000000 : ℝ) (50138509819/100000000000 : ℝ) (501385098181/1000000000000 : ℝ) (50138509819/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67011/524288 : ℝ)) (9920593147/10000000000 : ℝ) (496029657351/500000000000 : ℝ) (501385098181/1000000000000 : ℝ) (50138509819/100000000000 : ℝ) (793877804341/1000000000000 : ℝ) (396938902179/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0938_exp_lower
  have heNumeric : (64215676609/31250000000 : ℝ)/4 ≤ Real.exp (-42628247838287/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (64215676609/31250000000 : ℝ)/4 ≤ Real.exp ((33505/262144 : ℝ)-(396938902179/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33505/262144 : ℝ) (67011/524288 : ℝ) (396938902179/500000000000 : ℝ) (64215676609/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0939; no trusted numerical premise.
theorem cover8_leaf0939_exp_radius : (998004879675872619/1000000000000000000 : ℝ) ≤ Real.exp ((-16753/1048576 : ℝ)/8) ∧ Real.exp ((-16753/1048576 : ℝ)/8) ≤ (49900243983793631/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16753/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0939_exp_lower : (920113454558615577/1000000000000000000 : ℝ) ≤ Real.exp ((-85256495482829/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256495482829/128000000000000 : ℝ)/8) ≤ (460056727279307789/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256495482829/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0939_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901654599/1000000000000 : ℝ) ≤ 4*Real.exp (67011/524288 : ℝ)*Real.exp (-mu (radius 8 (16753/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901654599/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16753/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0939_exp_radius
  have hrNumeric : (123018755991/125000000000 : ℝ) ≤ Real.exp (-16753/1048576 : ℝ) ∧ Real.exp (-16753/1048576 : ℝ) ≤ (984150047929/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123018755991/125000000000 : ℝ) ≤ (radius 8 (16753/131072 : ℝ)) ∧ (radius 8 (16753/131072 : ℝ)) ≤ (984150047929/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16753/131072 : ℝ)) (123018755991/125000000000 : ℝ) (984150047929/1000000000000 : ℝ) (709351063/4000000000 : ℝ) (44334441439/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16753/131072 : ℝ)) (123018755991/125000000000 : ℝ) (984150047929/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16753/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123018755991/125000000000 : ℝ) (984150047929/1000000000000 : ℝ) (248018755991/250000000000 : ℝ) (198415004793/200000000000 : ℝ) (992043369983/1000000000000 : ℝ) (1937584707/1953125000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16753/131072 : ℝ)) 1 (248018755991/250000000000 : ℝ) (198415004793/200000000000 : ℝ) (992043369983/1000000000000 : ℝ) (1937584707/1953125000 : ℝ) (992059196973/1000000000000 : ℝ) (39682367879/40000000000 : ℝ) (992059196847/1000000000000 : ℝ) (992059196849/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16753/131072 : ℝ)) 2 (992059196973/1000000000000 : ℝ) (39682367879/40000000000 : ℝ) (992059196847/1000000000000 : ℝ) (992059196849/1000000000000 : ℝ) (99205919691/100000000000 : ℝ) (62003699807/62500000000 : ℝ) (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16753/131072 : ℝ)) 3 (99205919691/100000000000 : ℝ) (62003699807/62500000000 : ℝ) (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ) (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ) (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16753/131072 : ℝ)) 4 (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ) (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ) (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ) (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16753/131072 : ℝ)) 5 (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ) (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ) (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ) (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16753/131072 : ℝ)) 6 (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ) (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ) (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ) (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16753/131072 : ℝ)) 7 (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ) (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ) (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ) (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16753/131072 : ℝ))) (709351063/4000000000 : ℝ) (44334441439/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16753/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (709351063/4000000000 : ℝ) (44334441439/250000000000 : ℝ) (4709351063/8000000000 : ℝ) (294334441439/500000000000 : ℝ) (105278727003/250000000000 : ℝ) (21055745401/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16753/131072 : ℝ))) 1 (4709351063/8000000000 : ℝ) (294334441439/500000000000 : ℝ) (105278727003/250000000000 : ℝ) (21055745401/50000000000 : ℝ) (504891895443/1000000000000 : ℝ) (504891895449/1000000000000 : ℝ) (248946401089/500000000000 : ℝ) (99578560437/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16753/131072 : ℝ))) 2 (504891895443/1000000000000 : ℝ) (504891895449/1000000000000 : ℝ) (248946401089/500000000000 : ℝ) (99578560437/200000000000 : ℝ) (50139234881/100000000000 : ℝ) (501392348817/1000000000000 : ℝ) (125345033961/250000000000 : ℝ) (501380135851/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16753/131072 : ℝ))) 3 (50139234881/100000000000 : ℝ) (501392348817/1000000000000 : ℝ) (125345033961/250000000000 : ℝ) (501380135851/1000000000000 : ℝ) (501386242327/1000000000000 : ℝ) (250693121167/500000000000 : ℝ) (501386242289/1000000000000 : ℝ) (501386242297/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16753/131072 : ℝ))) 4 (501386242327/1000000000000 : ℝ) (250693121167/500000000000 : ℝ) (501386242289/1000000000000 : ℝ) (501386242297/1000000000000 : ℝ) (125346560577/250000000000 : ℝ) (125346560579/250000000000 : ℝ) (501386242307/1000000000000 : ℝ) (125346560579/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16753/131072 : ℝ))) 5 (125346560577/250000000000 : ℝ) (125346560579/250000000000 : ℝ) (501386242307/1000000000000 : ℝ) (125346560579/250000000000 : ℝ) (501386242307/1000000000000 : ℝ) (125346560579/250000000000 : ℝ) (501386242307/1000000000000 : ℝ) (125346560579/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16753/131072 : ℝ))) 6 (501386242307/1000000000000 : ℝ) (125346560579/250000000000 : ℝ) (501386242307/1000000000000 : ℝ) (125346560579/250000000000 : ℝ) (501386242307/1000000000000 : ℝ) (125346560579/250000000000 : ℝ) (501386242307/1000000000000 : ℝ) (125346560579/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16753/131072 : ℝ))) 7 (501386242307/1000000000000 : ℝ) (125346560579/250000000000 : ℝ) (501386242307/1000000000000 : ℝ) (125346560579/250000000000 : ℝ) (501386242307/1000000000000 : ℝ) (125346560579/250000000000 : ℝ) (501386242307/1000000000000 : ℝ) (125346560579/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16753/131072 : ℝ)) hmem 8 (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ) (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16753/131072 : ℝ))) hcmem 8 (501386242307/1000000000000 : ℝ) (125346560579/250000000000 : ℝ) (501386242307/1000000000000 : ℝ) (125346560579/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16753/131072 : ℝ)) (992059196909/1000000000000 : ℝ) (62003699807/62500000000 : ℝ) (501386242307/1000000000000 : ℝ) (125346560579/250000000000 : ℝ) (31755188407/40000000000 : ℝ) (793879710193/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0939_exp_lower
  have heNumeric : (2054901654599/1000000000000 : ℝ)/4 ≤ Real.exp (-85256495482829/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901654599/1000000000000 : ℝ)/4 ≤ Real.exp ((67011/524288 : ℝ)-(793879710193/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67011/524288 : ℝ) (16753/131072 : ℝ) (793879710193/1000000000000 : ℝ) (2054901654599/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0940; no trusted numerical premise.
theorem cover8_leaf0940_exp_radius : (499002424966504947/500000000000000000 : ℝ) ≤ Real.exp ((-67013/4194304 : ℝ)/8) ∧ Real.exp ((-67013/4194304 : ℝ)/8) ≤ (199600969986601979/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67013/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0940_exp_lower : (460056727367330029/500000000000000000 : ℝ) ≤ Real.exp ((-21314123821727/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314123821727/32000000000000 : ℝ)/8) ≤ (920113454734660059/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314123821727/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0940_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431353609/62500000000 : ℝ) ≤ 4*Real.exp (16753/131072 : ℝ)*Real.exp (-mu (radius 8 (67013/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (128431353609/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67013/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0940_exp_radius
  have hrNumeric : (123018726661/125000000000 : ℝ) ≤ Real.exp (-67013/4194304 : ℝ) ∧ Real.exp (-67013/4194304 : ℝ) ≤ (984149813289/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123018726661/125000000000 : ℝ) ≤ (radius 8 (67013/524288 : ℝ)) ∧ (radius 8 (67013/524288 : ℝ)) ≤ (984149813289/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67013/524288 : ℝ)) (123018726661/125000000000 : ℝ) (984149813289/1000000000000 : ℝ) (88669533949/500000000000 : ℝ) (35467813581/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67013/524288 : ℝ)) (123018726661/125000000000 : ℝ) (984149813289/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67013/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123018726661/125000000000 : ℝ) (984149813289/1000000000000 : ℝ) (248018726661/250000000000 : ℝ) (198414981329/200000000000 : ℝ) (496021625861/500000000000 : ℝ) (992043251723/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67013/524288 : ℝ)) 1 (248018726661/250000000000 : ℝ) (198414981329/200000000000 : ℝ) (496021625861/500000000000 : ℝ) (992043251723/1000000000000 : ℝ) (992059079183/1000000000000 : ℝ) (62003692449/62500000000 : ℝ) (62003692441/62500000000 : ℝ) (496029539529/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67013/524288 : ℝ)) 2 (992059079183/1000000000000 : ℝ) (62003692449/62500000000 : ℝ) (62003692441/62500000000 : ℝ) (496029539529/500000000000 : ℝ) (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ) (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67013/524288 : ℝ)) 3 (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ) (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ) (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ) (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67013/524288 : ℝ)) 4 (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ) (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ) (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ) (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67013/524288 : ℝ)) 5 (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ) (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ) (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ) (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67013/524288 : ℝ)) 6 (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ) (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ) (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ) (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67013/524288 : ℝ)) 7 (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ) (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ) (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ) (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67013/524288 : ℝ))) (88669533949/500000000000 : ℝ) (35467813581/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67013/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88669533949/500000000000 : ℝ) (35467813581/200000000000 : ℝ) (588669533949/1000000000000 : ℝ) (588669533953/1000000000000 : ℝ) (421116454081/1000000000000 : ℝ) (42111645409/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67013/524288 : ℝ))) 1 (588669533949/1000000000000 : ℝ) (588669533953/1000000000000 : ℝ) (421116454081/1000000000000 : ℝ) (42111645409/100000000000 : ℝ) (100978598803/200000000000 : ℝ) (252446497011/500000000000 : ℝ) (49789399149/100000000000 : ℝ) (248946995749/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67013/524288 : ℝ))) 2 (100978598803/200000000000 : ℝ) (252446497011/500000000000 : ℝ) (49789399149/100000000000 : ℝ) (248946995749/500000000000 : ℝ) (31337093297/62500000000 : ℝ) (12534837319/25000000000 : ℝ) (50138128013/100000000000 : ℝ) (501381280139/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67013/524288 : ℝ))) 3 (31337093297/62500000000 : ℝ) (12534837319/25000000000 : ℝ) (50138128013/100000000000 : ℝ) (501381280139/1000000000000 : ℝ) (501387386441/1000000000000 : ℝ) (10027747729/20000000000 : ℝ) (501387386403/1000000000000 : ℝ) (501387386413/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67013/524288 : ℝ))) 4 (501387386441/1000000000000 : ℝ) (10027747729/20000000000 : ℝ) (501387386403/1000000000000 : ℝ) (501387386413/1000000000000 : ℝ) (250693693211/500000000000 : ℝ) (7834177913/15625000000 : ℝ) (501387386421/1000000000000 : ℝ) (7834177913/15625000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67013/524288 : ℝ))) 5 (250693693211/500000000000 : ℝ) (7834177913/15625000000 : ℝ) (501387386421/1000000000000 : ℝ) (7834177913/15625000000 : ℝ) (501387386421/1000000000000 : ℝ) (7834177913/15625000000 : ℝ) (501387386421/1000000000000 : ℝ) (7834177913/15625000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67013/524288 : ℝ))) 6 (501387386421/1000000000000 : ℝ) (7834177913/15625000000 : ℝ) (501387386421/1000000000000 : ℝ) (7834177913/15625000000 : ℝ) (501387386421/1000000000000 : ℝ) (7834177913/15625000000 : ℝ) (501387386421/1000000000000 : ℝ) (7834177913/15625000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67013/524288 : ℝ))) 7 (501387386421/1000000000000 : ℝ) (7834177913/15625000000 : ℝ) (501387386421/1000000000000 : ℝ) (7834177913/15625000000 : ℝ) (501387386421/1000000000000 : ℝ) (7834177913/15625000000 : ℝ) (501387386421/1000000000000 : ℝ) (7834177913/15625000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67013/524288 : ℝ)) hmem 8 (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ) (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67013/524288 : ℝ))) hcmem 8 (501387386421/1000000000000 : ℝ) (7834177913/15625000000 : ℝ) (501387386421/1000000000000 : ℝ) (7834177913/15625000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67013/524288 : ℝ)) (992059079119/1000000000000 : ℝ) (992059079121/1000000000000 : ℝ) (501387386421/1000000000000 : ℝ) (7834177913/15625000000 : ℝ) (793881615991/1000000000000 : ℝ) (793881616011/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0940_exp_lower
  have heNumeric : (128431353609/62500000000 : ℝ)/4 ≤ Real.exp (-21314123821727/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431353609/62500000000 : ℝ)/4 ≤ Real.exp ((16753/131072 : ℝ)-(793881616011/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16753/131072 : ℝ) (67013/524288 : ℝ) (793881616011/1000000000000 : ℝ) (128431353609/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0941; no trusted numerical premise.
theorem cover8_leaf0941_exp_radius : (199600964038029611/200000000000000000 : ℝ) ≤ Real.exp ((-33507/2097152 : ℝ)/8) ∧ Real.exp ((-33507/2097152 : ℝ)/8) ≤ (124750602523768507/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33507/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0941_exp_lower : (18402269098280799/20000000000000000 : ℝ) ≤ Real.exp ((-3410259803491/5120000000000 : ℝ)/8) ∧ Real.exp ((-3410259803491/5120000000000 : ℝ)/8) ≤ (920113454914039951/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3410259803491/5120000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0941_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901660949/1000000000000 : ℝ) ≤ 4*Real.exp (67013/524288 : ℝ)*Real.exp (-mu (radius 8 (33507/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901660949/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33507/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0941_exp_radius
  have hrNumeric : (984149578649/1000000000000 : ℝ) ≤ Real.exp (-33507/2097152 : ℝ) ∧ Real.exp (-33507/2097152 : ℝ) ≤ (19682991573/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984149578649/1000000000000 : ℝ) ≤ (radius 8 (33507/262144 : ℝ)) ∧ (radius 8 (33507/262144 : ℝ)) ≤ (19682991573/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33507/262144 : ℝ)) (984149578649/1000000000000 : ℝ) (19682991573/20000000000 : ℝ) (177340370031/1000000000000 : ℝ) (88670185019/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33507/262144 : ℝ)) (984149578649/1000000000000 : ℝ) (19682991573/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33507/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984149578649/1000000000000 : ℝ) (19682991573/20000000000 : ℝ) (248018697331/250000000000 : ℝ) (39682991573/40000000000 : ℝ) (992043133461/1000000000000 : ℝ) (992043133463/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33507/262144 : ℝ)) 1 (248018697331/250000000000 : ℝ) (39682991573/40000000000 : ℝ) (992043133461/1000000000000 : ℝ) (992043133463/1000000000000 : ℝ) (62003685087/62500000000 : ℝ) (496029480697/500000000000 : ℝ) (496029480633/500000000000 : ℝ) (248014740317/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33507/262144 : ℝ)) 2 (62003685087/62500000000 : ℝ) (496029480697/500000000000 : ℝ) (496029480633/500000000000 : ℝ) (248014740317/250000000000 : ℝ) (992058961329/1000000000000 : ℝ) (992058961331/1000000000000 : ℝ) (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33507/262144 : ℝ)) 3 (992058961329/1000000000000 : ℝ) (992058961331/1000000000000 : ℝ) (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ) (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ) (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33507/262144 : ℝ)) 4 (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ) (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ) (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ) (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33507/262144 : ℝ)) 5 (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ) (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ) (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ) (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33507/262144 : ℝ)) 6 (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ) (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ) (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ) (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33507/262144 : ℝ)) 7 (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ) (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ) (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ) (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33507/262144 : ℝ))) (177340370031/1000000000000 : ℝ) (88670185019/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33507/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177340370031/1000000000000 : ℝ) (88670185019/500000000000 : ℝ) (117734037003/200000000000 : ℝ) (588670185019/1000000000000 : ℝ) (421118000127/1000000000000 : ℝ) (52639750017/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33507/262144 : ℝ))) 1 (117734037003/200000000000 : ℝ) (588670185019/1000000000000 : ℝ) (421118000127/1000000000000 : ℝ) (52639750017/125000000000 : ℝ) (504894092571/1000000000000 : ℝ) (252447046289/500000000000 : ℝ) (497895180783/1000000000000 : ℝ) (497895180791/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33507/262144 : ℝ))) 2 (504894092571/1000000000000 : ℝ) (252447046289/500000000000 : ℝ) (497895180783/1000000000000 : ℝ) (497895180791/1000000000000 : ℝ) (501394636677/1000000000000 : ℝ) (100278927337/200000000000 : ℝ) (501382424399/1000000000000 : ℝ) (62672803051/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33507/262144 : ℝ))) 3 (501394636677/1000000000000 : ℝ) (100278927337/200000000000 : ℝ) (501382424399/1000000000000 : ℝ) (62672803051/125000000000 : ℝ) (250694265269/500000000000 : ℝ) (501388530547/1000000000000 : ℝ) (1002777061/2000000000 : ℝ) (50138853051/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33507/262144 : ℝ))) 4 (250694265269/500000000000 : ℝ) (501388530547/1000000000000 : ℝ) (1002777061/2000000000 : ℝ) (50138853051/100000000000 : ℝ) (501388530519/1000000000000 : ℝ) (501388530529/1000000000000 : ℝ) (250694265259/500000000000 : ℝ) (501388530529/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33507/262144 : ℝ))) 5 (501388530519/1000000000000 : ℝ) (501388530529/1000000000000 : ℝ) (250694265259/500000000000 : ℝ) (501388530529/1000000000000 : ℝ) (250694265259/500000000000 : ℝ) (501388530529/1000000000000 : ℝ) (250694265259/500000000000 : ℝ) (501388530529/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33507/262144 : ℝ))) 6 (250694265259/500000000000 : ℝ) (501388530529/1000000000000 : ℝ) (250694265259/500000000000 : ℝ) (501388530529/1000000000000 : ℝ) (250694265259/500000000000 : ℝ) (501388530529/1000000000000 : ℝ) (250694265259/500000000000 : ℝ) (501388530529/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33507/262144 : ℝ))) 7 (250694265259/500000000000 : ℝ) (501388530529/1000000000000 : ℝ) (250694265259/500000000000 : ℝ) (501388530529/1000000000000 : ℝ) (250694265259/500000000000 : ℝ) (501388530529/1000000000000 : ℝ) (250694265259/500000000000 : ℝ) (501388530529/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33507/262144 : ℝ)) hmem 8 (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ) (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33507/262144 : ℝ))) hcmem 8 (250694265259/500000000000 : ℝ) (501388530529/1000000000000 : ℝ) (250694265259/500000000000 : ℝ) (501388530529/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33507/262144 : ℝ)) (62003685083/62500000000 : ℝ) (992058961331/1000000000000 : ℝ) (250694265259/500000000000 : ℝ) (501388530529/1000000000000 : ℝ) (793883521779/1000000000000 : ℝ) (3969417609/5000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0941_exp_lower
  have heNumeric : (2054901660949/1000000000000 : ℝ)/4 ≤ Real.exp (-3410259803491/5120000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901660949/1000000000000 : ℝ)/4 ≤ Real.exp ((67013/524288 : ℝ)-(3969417609/5000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67013/524288 : ℝ) (33507/262144 : ℝ) (3969417609/5000000000 : ℝ) (2054901660949/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0942; no trusted numerical premise.
theorem cover8_leaf0942_exp_radius : (499002395223643551/500000000000000000 : ℝ) ≤ Real.exp ((-67015/4194304 : ℝ)/8) ∧ Real.exp ((-67015/4194304 : ℝ)/8) ≤ (998004790447287103/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67015/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0942_exp_lower : (460056727547342499/500000000000000000 : ℝ) ≤ Real.exp ((-42628247443117/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628247443117/64000000000000 : ℝ)/8) ≤ (920113455094684999/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628247443117/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0942_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431354011/62500000000 : ℝ) ≤ 4*Real.exp (33507/262144 : ℝ)*Real.exp (-mu (radius 8 (67015/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (128431354011/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67015/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0942_exp_radius
  have hrNumeric : (984149344009/1000000000000 : ℝ) ≤ Real.exp (-67015/4194304 : ℝ) ∧ Real.exp (-67015/4194304 : ℝ) ≤ (98414934401/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984149344009/1000000000000 : ℝ) ≤ (radius 8 (67015/524288 : ℝ)) ∧ (radius 8 (67015/524288 : ℝ)) ≤ (98414934401/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67015/524288 : ℝ)) (984149344009/1000000000000 : ℝ) (98414934401/100000000000 : ℝ) (1108385451/6250000000 : ℝ) (177341672167/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67015/524288 : ℝ)) (984149344009/1000000000000 : ℝ) (98414934401/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67015/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984149344009/1000000000000 : ℝ) (98414934401/100000000000 : ℝ) (248018668001/250000000000 : ℝ) (198414934401/200000000000 : ℝ) (1240053769/1250000000 : ℝ) (496021507601/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67015/524288 : ℝ)) 1 (248018668001/250000000000 : ℝ) (198414934401/200000000000 : ℝ) (1240053769/1250000000 : ℝ) (496021507601/500000000000 : ℝ) (496029421801/500000000000 : ℝ) (248014710901/250000000000 : ℝ) (39682353739/40000000000 : ℝ) (496029421739/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67015/524288 : ℝ)) 2 (496029421801/500000000000 : ℝ) (248014710901/250000000000 : ℝ) (39682353739/40000000000 : ℝ) (496029421739/500000000000 : ℝ) (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ) (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67015/524288 : ℝ)) 3 (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ) (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ) (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ) (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67015/524288 : ℝ)) 4 (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ) (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ) (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ) (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67015/524288 : ℝ)) 5 (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ) (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ) (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ) (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67015/524288 : ℝ)) 6 (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ) (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ) (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ) (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67015/524288 : ℝ)) 7 (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ) (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ) (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ) (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67015/524288 : ℝ))) (1108385451/6250000000 : ℝ) (177341672167/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67015/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1108385451/6250000000 : ℝ) (177341672167/1000000000000 : ℝ) (7358385451/12500000000 : ℝ) (147167709021/250000000000 : ℝ) (210559773081/500000000000 : ℝ) (421119546171/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67015/524288 : ℝ))) 1 (7358385451/12500000000 : ℝ) (147167709021/250000000000 : ℝ) (210559773081/500000000000 : ℝ) (421119546171/1000000000000 : ℝ) (504895191121/1000000000000 : ℝ) (63111898891/125000000000 : ℝ) (497896370069/1000000000000 : ℝ) (497896370077/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67015/524288 : ℝ))) 2 (504895191121/1000000000000 : ℝ) (63111898891/125000000000 : ℝ) (497896370069/1000000000000 : ℝ) (497896370077/1000000000000 : ℝ) (100279156119/200000000000 : ℝ) (501395780603/1000000000000 : ℝ) (250691784331/500000000000 : ℝ) (50138356867/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67015/524288 : ℝ))) 3 (100279156119/200000000000 : ℝ) (501395780603/1000000000000 : ℝ) (250691784331/500000000000 : ℝ) (50138356867/100000000000 : ℝ) (125347418657/250000000000 : ℝ) (501389674637/1000000000000 : ℝ) (501389674591/1000000000000 : ℝ) (2506948373/5000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67015/524288 : ℝ))) 4 (125347418657/250000000000 : ℝ) (501389674637/1000000000000 : ℝ) (501389674591/1000000000000 : ℝ) (2506948373/5000000000 : ℝ) (501389674609/1000000000000 : ℝ) (501389674619/1000000000000 : ℝ) (501389674609/1000000000000 : ℝ) (501389674619/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67015/524288 : ℝ))) 5 (501389674609/1000000000000 : ℝ) (501389674619/1000000000000 : ℝ) (501389674609/1000000000000 : ℝ) (501389674619/1000000000000 : ℝ) (501389674609/1000000000000 : ℝ) (501389674619/1000000000000 : ℝ) (501389674609/1000000000000 : ℝ) (501389674619/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67015/524288 : ℝ))) 6 (501389674609/1000000000000 : ℝ) (501389674619/1000000000000 : ℝ) (501389674609/1000000000000 : ℝ) (501389674619/1000000000000 : ℝ) (501389674609/1000000000000 : ℝ) (501389674619/1000000000000 : ℝ) (501389674609/1000000000000 : ℝ) (501389674619/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67015/524288 : ℝ))) 7 (501389674609/1000000000000 : ℝ) (501389674619/1000000000000 : ℝ) (501389674609/1000000000000 : ℝ) (501389674619/1000000000000 : ℝ) (501389674609/1000000000000 : ℝ) (501389674619/1000000000000 : ℝ) (501389674609/1000000000000 : ℝ) (501389674619/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67015/524288 : ℝ)) hmem 8 (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ) (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67015/524288 : ℝ))) hcmem 8 (501389674609/1000000000000 : ℝ) (501389674619/1000000000000 : ℝ) (501389674609/1000000000000 : ℝ) (501389674619/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67015/524288 : ℝ)) (496029421769/500000000000 : ℝ) (992058843541/1000000000000 : ℝ) (501389674609/1000000000000 : ℝ) (501389674619/1000000000000 : ℝ) (793885427559/1000000000000 : ℝ) (396942713789/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0942_exp_lower
  have heNumeric : (128431354011/62500000000 : ℝ)/4 ≤ Real.exp (-42628247443117/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431354011/62500000000 : ℝ)/4 ≤ Real.exp ((33507/262144 : ℝ)-(396942713789/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33507/262144 : ℝ) (67015/524288 : ℝ) (396942713789/500000000000 : ℝ) (128431354011/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0943; no trusted numerical premise.
theorem cover8_leaf0943_exp_radius : (249501190176106759/250000000000000000 : ℝ) ≤ Real.exp ((-8377/524288 : ℝ)/8) ∧ Real.exp ((-8377/524288 : ℝ)/8) ≤ (998004760704427037/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8377/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0943_exp_lower : (920113455278550443/1000000000000000000 : ℝ) ≤ Real.exp ((-85256494681609/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256494681609/128000000000000 : ℝ)/8) ≤ (230028363819637611/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256494681609/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0943_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901667461/1000000000000 : ℝ) ≤ 4*Real.exp (67015/524288 : ℝ)*Real.exp (-mu (radius 8 (8377/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901667461/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8377/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0943_exp_radius
  have hrNumeric : (98414910937/100000000000 : ℝ) ≤ Real.exp (-8377/524288 : ℝ) ∧ Real.exp (-8377/524288 : ℝ) ≤ (984149109371/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98414910937/100000000000 : ℝ) ≤ (radius 8 (8377/65536 : ℝ)) ∧ (radius 8 (8377/65536 : ℝ)) ≤ (984149109371/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8377/65536 : ℝ)) (98414910937/100000000000 : ℝ) (984149109371/1000000000000 : ℝ) (177342974273/1000000000000 : ℝ) (4433574357/25000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8377/65536 : ℝ)) (98414910937/100000000000 : ℝ) (984149109371/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8377/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98414910937/100000000000 : ℝ) (984149109371/1000000000000 : ℝ) (198414910937/200000000000 : ℝ) (496037277343/500000000000 : ℝ) (49602144847/50000000000 : ℝ) (992042896941/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8377/65536 : ℝ)) 1 (198414910937/200000000000 : ℝ) (496037277343/500000000000 : ℝ) (49602144847/50000000000 : ℝ) (992042896941/1000000000000 : ℝ) (248014681453/250000000000 : ℝ) (496029362907/500000000000 : ℝ) (496029362843/500000000000 : ℝ) (124007340711/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8377/65536 : ℝ)) 2 (248014681453/250000000000 : ℝ) (496029362907/500000000000 : ℝ) (496029362843/500000000000 : ℝ) (124007340711/125000000000 : ℝ) (992058725749/1000000000000 : ℝ) (992058725751/1000000000000 : ℝ) (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8377/65536 : ℝ)) 3 (992058725749/1000000000000 : ℝ) (992058725751/1000000000000 : ℝ) (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ) (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ) (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8377/65536 : ℝ)) 4 (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ) (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ) (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ) (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8377/65536 : ℝ)) 5 (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ) (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ) (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ) (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8377/65536 : ℝ)) 6 (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ) (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ) (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ) (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8377/65536 : ℝ)) 7 (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ) (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ) (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ) (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8377/65536 : ℝ))) (177342974273/1000000000000 : ℝ) (4433574357/25000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8377/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177342974273/1000000000000 : ℝ) (4433574357/25000000000 : ℝ) (18395983973/31250000000 : ℝ) (29433574357/50000000000 : ℝ) (421121092173/1000000000000 : ℝ) (210560546091/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8377/65536 : ℝ))) 1 (18395983973/31250000000 : ℝ) (29433574357/50000000000 : ℝ) (421121092173/1000000000000 : ℝ) (210560546091/500000000000 : ℝ) (252448144827/500000000000 : ℝ) (504896289661/1000000000000 : ℝ) (497897559337/1000000000000 : ℝ) (99579511869/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8377/65536 : ℝ))) 2 (252448144827/500000000000 : ℝ) (504896289661/1000000000000 : ℝ) (497897559337/1000000000000 : ℝ) (99579511869/200000000000 : ℝ) (100279384899/200000000000 : ℝ) (501396924503/1000000000000 : ℝ) (501384712907/1000000000000 : ℝ) (100276942583/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8377/65536 : ℝ))) 3 (100279384899/200000000000 : ℝ) (501396924503/1000000000000 : ℝ) (501384712907/1000000000000 : ℝ) (100276942583/200000000000 : ℝ) (501390818701/1000000000000 : ℝ) (501390818709/1000000000000 : ℝ) (501390818663/1000000000000 : ℝ) (31336926167/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8377/65536 : ℝ))) 4 (501390818701/1000000000000 : ℝ) (501390818709/1000000000000 : ℝ) (501390818663/1000000000000 : ℝ) (31336926167/62500000000 : ℝ) (250695409341/500000000000 : ℝ) (501390818691/1000000000000 : ℝ) (501390818681/1000000000000 : ℝ) (501390818691/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8377/65536 : ℝ))) 5 (250695409341/500000000000 : ℝ) (501390818691/1000000000000 : ℝ) (501390818681/1000000000000 : ℝ) (501390818691/1000000000000 : ℝ) (501390818681/1000000000000 : ℝ) (501390818691/1000000000000 : ℝ) (501390818681/1000000000000 : ℝ) (501390818691/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8377/65536 : ℝ))) 6 (501390818681/1000000000000 : ℝ) (501390818691/1000000000000 : ℝ) (501390818681/1000000000000 : ℝ) (501390818691/1000000000000 : ℝ) (501390818681/1000000000000 : ℝ) (501390818691/1000000000000 : ℝ) (501390818681/1000000000000 : ℝ) (501390818691/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8377/65536 : ℝ))) 7 (501390818681/1000000000000 : ℝ) (501390818691/1000000000000 : ℝ) (501390818681/1000000000000 : ℝ) (501390818691/1000000000000 : ℝ) (501390818681/1000000000000 : ℝ) (501390818691/1000000000000 : ℝ) (501390818681/1000000000000 : ℝ) (501390818691/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8377/65536 : ℝ)) hmem 8 (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ) (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8377/65536 : ℝ))) hcmem 8 (501390818681/1000000000000 : ℝ) (501390818691/1000000000000 : ℝ) (501390818681/1000000000000 : ℝ) (501390818691/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8377/65536 : ℝ)) (248014681437/250000000000 : ℝ) (992058725751/1000000000000 : ℝ) (501390818681/1000000000000 : ℝ) (501390818691/1000000000000 : ℝ) (793887333309/1000000000000 : ℝ) (49617958333/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0943_exp_lower
  have heNumeric : (2054901667461/1000000000000 : ℝ)/4 ≤ Real.exp (-85256494681609/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901667461/1000000000000 : ℝ)/4 ≤ Real.exp ((67015/524288 : ℝ)-(49617958333/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67015/524288 : ℝ) (8377/65536 : ℝ) (49617958333/62500000000 : ℝ) (2054901667461/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0944; no trusted numerical premise.
theorem cover8_leaf0944_exp_radius : (62375295685097991/62500000000000000 : ℝ) ≤ Real.exp ((-67017/4194304 : ℝ)/8) ∧ Real.exp ((-67017/4194304 : ℝ)/8) ≤ (998004730961567857/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67017/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0944_exp_lower : (115014181932931377/125000000000000000 : ℝ) ≤ Real.exp ((-10657061809479/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657061809479/16000000000000 : ℝ)/8) ≤ (920113455463451017/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657061809479/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0944_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980334153/200000000000 : ℝ) ≤ 4*Real.exp (8377/65536 : ℝ)*Real.exp (-mu (radius 8 (67017/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980334153/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67017/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0944_exp_radius
  have hrNumeric : (98414887473/100000000000 : ℝ) ≤ Real.exp (-67017/4194304 : ℝ) ∧ Real.exp (-67017/4194304 : ℝ) ≤ (984148874731/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98414887473/100000000000 : ℝ) ≤ (radius 8 (67017/524288 : ℝ)) ∧ (radius 8 (67017/524288 : ℝ)) ≤ (984148874731/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67017/524288 : ℝ)) (98414887473/100000000000 : ℝ) (984148874731/1000000000000 : ℝ) (88672138191/500000000000 : ℝ) (177344276389/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67017/524288 : ℝ)) (98414887473/100000000000 : ℝ) (984148874731/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67017/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98414887473/100000000000 : ℝ) (984148874731/1000000000000 : ℝ) (198414887473/200000000000 : ℝ) (496037218683/500000000000 : ℝ) (992042778679/1000000000000 : ℝ) (24801069467/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67017/524288 : ℝ)) 1 (198414887473/200000000000 : ℝ) (496037218683/500000000000 : ℝ) (992042778679/1000000000000 : ℝ) (24801069467/25000000000 : ℝ) (496029304011/500000000000 : ℝ) (992058608023/1000000000000 : ℝ) (198411721579/200000000000 : ℝ) (992058607897/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67017/524288 : ℝ)) 2 (496029304011/500000000000 : ℝ) (992058608023/1000000000000 : ℝ) (198411721579/200000000000 : ℝ) (992058607897/1000000000000 : ℝ) (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ) (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67017/524288 : ℝ)) 3 (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ) (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ) (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ) (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67017/524288 : ℝ)) 4 (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ) (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ) (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ) (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67017/524288 : ℝ)) 5 (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ) (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ) (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ) (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67017/524288 : ℝ)) 6 (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ) (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ) (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ) (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67017/524288 : ℝ)) 7 (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ) (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ) (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ) (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67017/524288 : ℝ))) (88672138191/500000000000 : ℝ) (177344276389/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67017/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88672138191/500000000000 : ℝ) (177344276389/1000000000000 : ℝ) (588672138191/1000000000000 : ℝ) (117734427639/200000000000 : ℝ) (421122638173/1000000000000 : ℝ) (210561319091/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67017/524288 : ℝ))) 1 (588672138191/1000000000000 : ℝ) (117734427639/200000000000 : ℝ) (421122638173/1000000000000 : ℝ) (210561319091/500000000000 : ℝ) (252448694091/500000000000 : ℝ) (504897388189/1000000000000 : ℝ) (124474687149/250000000000 : ℝ) (124474687151/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67017/524288 : ℝ))) 2 (252448694091/500000000000 : ℝ) (504897388189/1000000000000 : ℝ) (124474687149/250000000000 : ℝ) (124474687151/250000000000 : ℝ) (501398068389/1000000000000 : ℝ) (501398068397/1000000000000 : ℝ) (100277171429/200000000000 : ℝ) (501385857153/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67017/524288 : ℝ))) 3 (501398068389/1000000000000 : ℝ) (501398068397/1000000000000 : ℝ) (100277171429/200000000000 : ℝ) (501385857153/1000000000000 : ℝ) (501391962767/1000000000000 : ℝ) (20055678511/40000000000 : ℝ) (501391962729/1000000000000 : ℝ) (250695981369/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67017/524288 : ℝ))) 4 (501391962767/1000000000000 : ℝ) (20055678511/40000000000 : ℝ) (501391962729/1000000000000 : ℝ) (250695981369/500000000000 : ℝ) (125347990687/250000000000 : ℝ) (501391962757/1000000000000 : ℝ) (501391962747/1000000000000 : ℝ) (501391962757/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67017/524288 : ℝ))) 5 (125347990687/250000000000 : ℝ) (501391962757/1000000000000 : ℝ) (501391962747/1000000000000 : ℝ) (501391962757/1000000000000 : ℝ) (501391962747/1000000000000 : ℝ) (501391962757/1000000000000 : ℝ) (501391962747/1000000000000 : ℝ) (501391962757/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67017/524288 : ℝ))) 6 (501391962747/1000000000000 : ℝ) (501391962757/1000000000000 : ℝ) (501391962747/1000000000000 : ℝ) (501391962757/1000000000000 : ℝ) (501391962747/1000000000000 : ℝ) (501391962757/1000000000000 : ℝ) (501391962747/1000000000000 : ℝ) (501391962757/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67017/524288 : ℝ))) 7 (501391962747/1000000000000 : ℝ) (501391962757/1000000000000 : ℝ) (501391962747/1000000000000 : ℝ) (501391962757/1000000000000 : ℝ) (501391962747/1000000000000 : ℝ) (501391962757/1000000000000 : ℝ) (501391962747/1000000000000 : ℝ) (501391962757/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67017/524288 : ℝ)) hmem 8 (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ) (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67017/524288 : ℝ))) hcmem 8 (501391962747/1000000000000 : ℝ) (501391962757/1000000000000 : ℝ) (501391962747/1000000000000 : ℝ) (501391962757/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67017/524288 : ℝ)) (496029303979/500000000000 : ℝ) (24801465199/25000000000 : ℝ) (501391962747/1000000000000 : ℝ) (501391962757/1000000000000 : ℝ) (793889239051/1000000000000 : ℝ) (793889239069/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0944_exp_lower
  have heNumeric : (410980334153/200000000000 : ℝ)/4 ≤ Real.exp (-10657061809479/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980334153/200000000000 : ℝ)/4 ≤ Real.exp ((8377/65536 : ℝ)-(793889239069/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8377/65536 : ℝ) (67017/524288 : ℝ) (793889239069/1000000000000 : ℝ) (410980334153/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0945; no trusted numerical premise.
theorem cover8_leaf0945_exp_radius : (998004701218709563/1000000000000000000 : ℝ) ≤ Real.exp ((-33509/2097152 : ℝ)/8) ∧ Real.exp ((-33509/2097152 : ℝ)/8) ≤ (249501175304677391/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33509/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0945_exp_lower : (920113455651341957/1000000000000000000 : ℝ) ≤ Real.exp ((-85256494266727/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256494266727/128000000000000 : ℝ)/8) ≤ (460056727825670979/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256494266727/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0945_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450837061/500000000000 : ℝ) ≤ 4*Real.exp (67017/524288 : ℝ)*Real.exp (-mu (radius 8 (33509/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450837061/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33509/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0945_exp_radius
  have hrNumeric : (984148640091/1000000000000 : ℝ) ≤ Real.exp (-33509/2097152 : ℝ) ∧ Real.exp (-33509/2097152 : ℝ) ≤ (246037160023/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984148640091/1000000000000 : ℝ) ≤ (radius 8 (33509/262144 : ℝ)) ∧ (radius 8 (33509/262144 : ℝ)) ≤ (246037160023/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33509/262144 : ℝ)) (984148640091/1000000000000 : ℝ) (246037160023/250000000000 : ℝ) (44336394619/250000000000 : ℝ) (88672789241/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33509/262144 : ℝ)) (984148640091/1000000000000 : ℝ) (246037160023/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33509/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984148640091/1000000000000 : ℝ) (246037160023/250000000000 : ℝ) (198414864009/200000000000 : ℝ) (496037160023/500000000000 : ℝ) (496021330209/500000000000 : ℝ) (49602133021/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33509/262144 : ℝ)) 1 (198414864009/200000000000 : ℝ) (496037160023/500000000000 : ℝ) (496021330209/500000000000 : ℝ) (49602133021/50000000000 : ℝ) (992058490231/1000000000000 : ℝ) (992058490233/1000000000000 : ℝ) (198411698021/200000000000 : ℝ) (992058490107/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33509/262144 : ℝ)) 2 (992058490231/1000000000000 : ℝ) (992058490233/1000000000000 : ℝ) (198411698021/200000000000 : ℝ) (992058490107/1000000000000 : ℝ) (124007311271/125000000000 : ℝ) (99205849017/100000000000 : ℝ) (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33509/262144 : ℝ)) 3 (124007311271/125000000000 : ℝ) (99205849017/100000000000 : ℝ) (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ) (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ) (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33509/262144 : ℝ)) 4 (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ) (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ) (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ) (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33509/262144 : ℝ)) 5 (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ) (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ) (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ) (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33509/262144 : ℝ)) 6 (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ) (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ) (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ) (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33509/262144 : ℝ)) 7 (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ) (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ) (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ) (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33509/262144 : ℝ))) (44336394619/250000000000 : ℝ) (88672789241/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33509/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44336394619/250000000000 : ℝ) (88672789241/500000000000 : ℝ) (294336394619/500000000000 : ℝ) (588672789241/1000000000000 : ℝ) (421124184149/1000000000000 : ℝ) (210562092079/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33509/262144 : ℝ))) 1 (294336394619/500000000000 : ℝ) (588672789241/1000000000000 : ℝ) (421124184149/1000000000000 : ℝ) (210562092079/500000000000 : ℝ) (504898486693/1000000000000 : ℝ) (5048984867/10000000000 : ℝ) (497899937837/1000000000000 : ℝ) (99579987569/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33509/262144 : ℝ))) 2 (504898486693/1000000000000 : ℝ) (5048984867/10000000000 : ℝ) (497899937837/1000000000000 : ℝ) (99579987569/200000000000 : ℝ) (100279842453/200000000000 : ℝ) (501399212273/1000000000000 : ℝ) (100277400273/200000000000 : ℝ) (250693500687/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33509/262144 : ℝ))) 3 (100279842453/200000000000 : ℝ) (501399212273/1000000000000 : ℝ) (100277400273/200000000000 : ℝ) (250693500687/500000000000 : ℝ) (100278621363/200000000000 : ℝ) (62674138353/125000000000 : ℝ) (501393106777/1000000000000 : ℝ) (501393106787/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33509/262144 : ℝ))) 4 (100278621363/200000000000 : ℝ) (62674138353/125000000000 : ℝ) (501393106777/1000000000000 : ℝ) (501393106787/1000000000000 : ℝ) (125348276699/250000000000 : ℝ) (250696553403/500000000000 : ℝ) (100278621359/200000000000 : ℝ) (250696553403/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33509/262144 : ℝ))) 5 (125348276699/250000000000 : ℝ) (250696553403/500000000000 : ℝ) (100278621359/200000000000 : ℝ) (250696553403/500000000000 : ℝ) (100278621359/200000000000 : ℝ) (250696553403/500000000000 : ℝ) (100278621359/200000000000 : ℝ) (250696553403/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33509/262144 : ℝ))) 6 (100278621359/200000000000 : ℝ) (250696553403/500000000000 : ℝ) (100278621359/200000000000 : ℝ) (250696553403/500000000000 : ℝ) (100278621359/200000000000 : ℝ) (250696553403/500000000000 : ℝ) (100278621359/200000000000 : ℝ) (250696553403/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33509/262144 : ℝ))) 7 (100278621359/200000000000 : ℝ) (250696553403/500000000000 : ℝ) (100278621359/200000000000 : ℝ) (250696553403/500000000000 : ℝ) (100278621359/200000000000 : ℝ) (250696553403/500000000000 : ℝ) (100278621359/200000000000 : ℝ) (250696553403/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33509/262144 : ℝ)) hmem 8 (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ) (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33509/262144 : ℝ))) hcmem 8 (100278621359/200000000000 : ℝ) (250696553403/500000000000 : ℝ) (100278621359/200000000000 : ℝ) (250696553403/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33509/262144 : ℝ)) (992058490167/1000000000000 : ℝ) (99205849017/100000000000 : ℝ) (100278621359/200000000000 : ℝ) (250696553403/500000000000 : ℝ) (793891144763/1000000000000 : ℝ) (49618196549/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0945_exp_lower
  have heNumeric : (1027450837061/500000000000 : ℝ)/4 ≤ Real.exp (-85256494266727/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450837061/500000000000 : ℝ)/4 ≤ Real.exp ((67017/524288 : ℝ)-(49618196549/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67017/524288 : ℝ) (33509/262144 : ℝ) (49618196549/62500000000 : ℝ) (1027450837061/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0946; no trusted numerical premise.
theorem cover8_leaf0946_exp_radius : (249501167868963039/250000000000000000 : ℝ) ≤ Real.exp ((-67019/4194304 : ℝ)/8) ∧ Real.exp ((-67019/4194304 : ℝ)/8) ≤ (998004671475852157/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67019/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0946_exp_lower : (920113455841648197/1000000000000000000 : ℝ) ≤ Real.exp ((-42628247027467/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628247027467/64000000000000 : ℝ)/8) ≤ (460056727920824099/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628247027467/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0946_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450838761/500000000000 : ℝ) ≤ 4*Real.exp (33509/262144 : ℝ)*Real.exp (-mu (radius 8 (67019/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450838761/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67019/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0946_exp_radius
  have hrNumeric : (246037101363/250000000000 : ℝ) ≤ Real.exp (-67019/4194304 : ℝ) ∧ Real.exp (-67019/4194304 : ℝ) ≤ (984148405453/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246037101363/250000000000 : ℝ) ≤ (radius 8 (67019/524288 : ℝ)) ∧ (radius 8 (67019/524288 : ℝ)) ≤ (984148405453/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67019/524288 : ℝ)) (246037101363/250000000000 : ℝ) (984148405453/1000000000000 : ℝ) (177346880559/1000000000000 : ℝ) (88673440283/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67019/524288 : ℝ)) (246037101363/250000000000 : ℝ) (984148405453/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67019/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246037101363/250000000000 : ℝ) (984148405453/1000000000000 : ℝ) (496037101363/500000000000 : ℝ) (992074202727/1000000000000 : ℝ) (496021271079/500000000000 : ℝ) (992042542159/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67019/524288 : ℝ)) 1 (496037101363/500000000000 : ℝ) (992074202727/1000000000000 : ℝ) (496021271079/500000000000 : ℝ) (992042542159/1000000000000 : ℝ) (496029186221/500000000000 : ℝ) (992058372443/1000000000000 : ℝ) (198411674463/200000000000 : ℝ) (992058372317/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67019/524288 : ℝ)) 2 (496029186221/500000000000 : ℝ) (992058372443/1000000000000 : ℝ) (198411674463/200000000000 : ℝ) (992058372317/1000000000000 : ℝ) (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ) (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67019/524288 : ℝ)) 3 (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ) (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ) (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ) (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67019/524288 : ℝ)) 4 (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ) (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ) (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ) (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67019/524288 : ℝ)) 5 (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ) (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ) (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ) (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67019/524288 : ℝ)) 6 (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ) (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ) (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ) (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67019/524288 : ℝ)) 7 (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ) (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ) (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ) (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67019/524288 : ℝ))) (177346880559/1000000000000 : ℝ) (88673440283/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67019/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177346880559/1000000000000 : ℝ) (88673440283/500000000000 : ℝ) (588673440279/1000000000000 : ℝ) (588673440283/1000000000000 : ℝ) (105281432527/250000000000 : ℝ) (421125730117/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67019/524288 : ℝ))) 1 (588673440279/1000000000000 : ℝ) (588673440283/1000000000000 : ℝ) (105281432527/250000000000 : ℝ) (421125730117/1000000000000 : ℝ) (504899585193/1000000000000 : ℝ) (1262248963/2500000000 : ℝ) (99580225413/200000000000 : ℝ) (497901127073/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67019/524288 : ℝ))) 2 (504899585193/1000000000000 : ℝ) (1262248963/2500000000 : ℝ) (99580225413/200000000000 : ℝ) (497901127073/1000000000000 : ℝ) (501400356129/1000000000000 : ℝ) (501400356137/1000000000000 : ℝ) (250694072787/500000000000 : ℝ) (250694072791/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67019/524288 : ℝ))) 3 (501400356129/1000000000000 : ℝ) (501400356137/1000000000000 : ℝ) (250694072787/500000000000 : ℝ) (250694072791/500000000000 : ℝ) (501394250851/1000000000000 : ℝ) (25069712543/50000000000 : ℝ) (250697125407/500000000000 : ℝ) (501394250823/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67019/524288 : ℝ))) 4 (501394250851/1000000000000 : ℝ) (25069712543/50000000000 : ℝ) (250697125407/500000000000 : ℝ) (501394250823/1000000000000 : ℝ) (31337140677/62500000000 : ℝ) (250697125421/500000000000 : ℝ) (31337140677/62500000000 : ℝ) (250697125421/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67019/524288 : ℝ))) 5 (31337140677/62500000000 : ℝ) (250697125421/500000000000 : ℝ) (31337140677/62500000000 : ℝ) (250697125421/500000000000 : ℝ) (31337140677/62500000000 : ℝ) (250697125421/500000000000 : ℝ) (31337140677/62500000000 : ℝ) (250697125421/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67019/524288 : ℝ))) 6 (31337140677/62500000000 : ℝ) (250697125421/500000000000 : ℝ) (31337140677/62500000000 : ℝ) (250697125421/500000000000 : ℝ) (31337140677/62500000000 : ℝ) (250697125421/500000000000 : ℝ) (31337140677/62500000000 : ℝ) (250697125421/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67019/524288 : ℝ))) 7 (31337140677/62500000000 : ℝ) (250697125421/500000000000 : ℝ) (31337140677/62500000000 : ℝ) (250697125421/500000000000 : ℝ) (31337140677/62500000000 : ℝ) (250697125421/500000000000 : ℝ) (31337140677/62500000000 : ℝ) (250697125421/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67019/524288 : ℝ)) hmem 8 (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ) (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67019/524288 : ℝ))) hcmem 8 (31337140677/62500000000 : ℝ) (250697125421/500000000000 : ℝ) (31337140677/62500000000 : ℝ) (250697125421/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67019/524288 : ℝ)) (496029186189/500000000000 : ℝ) (49602918619/50000000000 : ℝ) (31337140677/62500000000 : ℝ) (250697125421/500000000000 : ℝ) (793893050459/1000000000000 : ℝ) (396946525239/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0946_exp_lower
  have heNumeric : (1027450838761/500000000000 : ℝ)/4 ≤ Real.exp (-42628247027467/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450838761/500000000000 : ℝ)/4 ≤ Real.exp ((33509/262144 : ℝ)-(396946525239/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33509/262144 : ℝ) (67019/524288 : ℝ) (396946525239/500000000000 : ℝ) (1027450838761/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0947; no trusted numerical premise.
theorem cover8_leaf0947_exp_radius : (249501160433248909/250000000000000000 : ℝ) ≤ Real.exp ((-16755/1048576 : ℝ)/8) ∧ Real.exp ((-16755/1048576 : ℝ)/8) ≤ (998004641732995637/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16755/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0947_exp_lower : (184022691206827941/200000000000000000 : ℝ) ≤ Real.exp ((-85256493840709/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256493840709/128000000000000 : ℝ)/8) ≤ (460056728017069853/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256493840709/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0947_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901680961/1000000000000 : ℝ) ≤ 4*Real.exp (67019/524288 : ℝ)*Real.exp (-mu (radius 8 (16755/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901680961/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16755/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0947_exp_radius
  have hrNumeric : (984148170813/1000000000000 : ℝ) ≤ Real.exp (-16755/1048576 : ℝ) ∧ Real.exp (-16755/1048576 : ℝ) ≤ (492074085407/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984148170813/1000000000000 : ℝ) ≤ (radius 8 (16755/131072 : ℝ)) ∧ (radius 8 (16755/131072 : ℝ)) ≤ (492074085407/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16755/131072 : ℝ)) (984148170813/1000000000000 : ℝ) (492074085407/500000000000 : ℝ) (177348182633/1000000000000 : ℝ) (2216852283/12500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16755/131072 : ℝ)) (984148170813/1000000000000 : ℝ) (492074085407/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16755/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984148170813/1000000000000 : ℝ) (492074085407/500000000000 : ℝ) (496037042703/500000000000 : ℝ) (992074085407/1000000000000 : ℝ) (992042423897/1000000000000 : ℝ) (992042423899/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16755/131072 : ℝ)) 1 (496037042703/500000000000 : ℝ) (992074085407/1000000000000 : ℝ) (992042423897/1000000000000 : ℝ) (992042423899/1000000000000 : ℝ) (992058254651/1000000000000 : ℝ) (992058254653/1000000000000 : ℝ) (39682330181/40000000000 : ℝ) (992058254527/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16755/131072 : ℝ)) 2 (992058254651/1000000000000 : ℝ) (992058254653/1000000000000 : ℝ) (39682330181/40000000000 : ℝ) (992058254527/1000000000000 : ℝ) (248014563647/250000000000 : ℝ) (99205825459/100000000000 : ℝ) (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16755/131072 : ℝ)) 3 (248014563647/250000000000 : ℝ) (99205825459/100000000000 : ℝ) (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ) (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ) (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16755/131072 : ℝ)) 4 (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ) (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ) (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ) (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16755/131072 : ℝ)) 5 (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ) (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ) (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ) (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16755/131072 : ℝ)) 6 (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ) (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ) (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ) (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16755/131072 : ℝ)) 7 (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ) (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ) (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ) (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16755/131072 : ℝ))) (177348182633/1000000000000 : ℝ) (2216852283/12500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16755/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177348182633/1000000000000 : ℝ) (2216852283/12500000000 : ℝ) (147168522829/250000000000 : ℝ) (14716852283/25000000000 : ℝ) (421127276049/1000000000000 : ℝ) (210563638029/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16755/131072 : ℝ))) 1 (147168522829/250000000000 : ℝ) (14716852283/25000000000 : ℝ) (421127276049/1000000000000 : ℝ) (210563638029/500000000000 : ℝ) (252450341841/500000000000 : ℝ) (504900683689/1000000000000 : ℝ) (497902316279/1000000000000 : ℝ) (497902316287/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16755/131072 : ℝ))) 2 (252450341841/500000000000 : ℝ) (504900683689/1000000000000 : ℝ) (497902316279/1000000000000 : ℝ) (497902316287/1000000000000 : ℝ) (25070074999/50000000000 : ℝ) (125350374997/250000000000 : ℝ) (50138928977/100000000000 : ℝ) (250694644889/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16755/131072 : ℝ))) 3 (25070074999/50000000000 : ℝ) (125350374997/250000000000 : ℝ) (50138928977/100000000000 : ℝ) (250694644889/500000000000 : ℝ) (4011163159/8000000000 : ℝ) (501395394883/1000000000000 : ℝ) (501395394837/1000000000000 : ℝ) (250697697423/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16755/131072 : ℝ))) 4 (4011163159/8000000000 : ℝ) (501395394883/1000000000000 : ℝ) (501395394837/1000000000000 : ℝ) (250697697423/500000000000 : ℝ) (62674424357/125000000000 : ℝ) (100279078973/200000000000 : ℝ) (100279078971/200000000000 : ℝ) (100279078973/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16755/131072 : ℝ))) 5 (62674424357/125000000000 : ℝ) (100279078973/200000000000 : ℝ) (100279078971/200000000000 : ℝ) (100279078973/200000000000 : ℝ) (100279078971/200000000000 : ℝ) (100279078973/200000000000 : ℝ) (100279078971/200000000000 : ℝ) (100279078973/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16755/131072 : ℝ))) 6 (100279078971/200000000000 : ℝ) (100279078973/200000000000 : ℝ) (100279078971/200000000000 : ℝ) (100279078973/200000000000 : ℝ) (100279078971/200000000000 : ℝ) (100279078973/200000000000 : ℝ) (100279078971/200000000000 : ℝ) (100279078973/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16755/131072 : ℝ))) 7 (100279078971/200000000000 : ℝ) (100279078973/200000000000 : ℝ) (100279078971/200000000000 : ℝ) (100279078973/200000000000 : ℝ) (100279078971/200000000000 : ℝ) (100279078973/200000000000 : ℝ) (100279078971/200000000000 : ℝ) (100279078973/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16755/131072 : ℝ)) hmem 8 (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ) (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16755/131072 : ℝ))) hcmem 8 (100279078971/200000000000 : ℝ) (100279078973/200000000000 : ℝ) (100279078971/200000000000 : ℝ) (100279078973/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16755/131072 : ℝ)) (992058254587/1000000000000 : ℝ) (99205825459/100000000000 : ℝ) (100279078971/200000000000 : ℝ) (100279078973/200000000000 : ℝ) (396947478067/500000000000 : ℝ) (793894956153/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0947_exp_lower
  have heNumeric : (2054901680961/1000000000000 : ℝ)/4 ≤ Real.exp (-85256493840709/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901680961/1000000000000 : ℝ)/4 ≤ Real.exp ((67019/524288 : ℝ)-(793894956153/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67019/524288 : ℝ) (16755/131072 : ℝ) (793894956153/1000000000000 : ℝ) (2054901680961/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0948; no trusted numerical premise.
theorem cover8_leaf0948_exp_radius : (998004611990140001/1000000000000000000 : ℝ) ≤ Real.exp ((-67021/4194304 : ℝ)/8) ∧ Real.exp ((-67021/4194304 : ℝ)/8) ≤ (499002305995070001/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67021/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0948_exp_lower : (230028364056945339/250000000000000000 : ℝ) ≤ Real.exp ((-21314123406301/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314123406301/32000000000000 : ℝ)/8) ≤ (920113456227781357/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314123406301/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0948_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901684421/1000000000000 : ℝ) ≤ 4*Real.exp (16755/131072 : ℝ)*Real.exp (-mu (radius 8 (67021/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901684421/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67021/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0948_exp_radius
  have hrNumeric : (984147936173/1000000000000 : ℝ) ≤ Real.exp (-67021/4194304 : ℝ) ∧ Real.exp (-67021/4194304 : ℝ) ≤ (492073968087/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984147936173/1000000000000 : ℝ) ≤ (radius 8 (67021/524288 : ℝ)) ∧ (radius 8 (67021/524288 : ℝ)) ≤ (492073968087/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67021/524288 : ℝ)) (984147936173/1000000000000 : ℝ) (492073968087/500000000000 : ℝ) (177349484703/1000000000000 : ℝ) (177349484709/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67021/524288 : ℝ)) (984147936173/1000000000000 : ℝ) (492073968087/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67021/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984147936173/1000000000000 : ℝ) (492073968087/500000000000 : ℝ) (496036984043/500000000000 : ℝ) (992073968087/1000000000000 : ℝ) (248010576409/250000000000 : ℝ) (496021152819/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67021/524288 : ℝ)) 1 (496036984043/500000000000 : ℝ) (992073968087/1000000000000 : ℝ) (248010576409/250000000000 : ℝ) (496021152819/500000000000 : ℝ) (992058136861/1000000000000 : ℝ) (992058136863/1000000000000 : ℝ) (496029068367/500000000000 : ℝ) (992058136737/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67021/524288 : ℝ)) 2 (992058136861/1000000000000 : ℝ) (992058136863/1000000000000 : ℝ) (496029068367/500000000000 : ℝ) (992058136737/1000000000000 : ℝ) (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ) (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67021/524288 : ℝ)) 3 (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ) (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ) (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ) (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67021/524288 : ℝ)) 4 (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ) (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ) (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ) (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67021/524288 : ℝ)) 5 (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ) (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ) (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ) (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67021/524288 : ℝ)) 6 (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ) (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ) (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ) (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67021/524288 : ℝ)) 7 (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ) (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ) (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ) (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67021/524288 : ℝ))) (177349484703/1000000000000 : ℝ) (177349484709/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67021/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177349484703/1000000000000 : ℝ) (177349484709/1000000000000 : ℝ) (588674742351/1000000000000 : ℝ) (117734948471/200000000000 : ℝ) (21056441099/50000000000 : ℝ) (105282205497/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67021/524288 : ℝ))) 1 (588674742351/1000000000000 : ℝ) (117734948471/200000000000 : ℝ) (21056441099/50000000000 : ℝ) (105282205497/250000000000 : ℝ) (100980356433/200000000000 : ℝ) (126225445543/250000000000 : ℝ) (248951752743/500000000000 : ℝ) (497903505493/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67021/524288 : ℝ))) 2 (100980356433/200000000000 : ℝ) (126225445543/250000000000 : ℝ) (248951752743/500000000000 : ℝ) (497903505493/1000000000000 : ℝ) (20056105753/40000000000 : ℝ) (501402643833/1000000000000 : ℝ) (501390433959/1000000000000 : ℝ) (501390433967/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67021/524288 : ℝ))) 3 (20056105753/40000000000 : ℝ) (501402643833/1000000000000 : ℝ) (501390433959/1000000000000 : ℝ) (501390433967/1000000000000 : ℝ) (125349134723/250000000000 : ℝ) (5013965389/10000000000 : ℝ) (250698269427/500000000000 : ℝ) (501396538863/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67021/524288 : ℝ))) 4 (125349134723/250000000000 : ℝ) (5013965389/10000000000 : ℝ) (250698269427/500000000000 : ℝ) (501396538863/1000000000000 : ℝ) (501396538873/1000000000000 : ℝ) (250698269441/500000000000 : ℝ) (62674567359/125000000000 : ℝ) (250698269441/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67021/524288 : ℝ))) 5 (501396538873/1000000000000 : ℝ) (250698269441/500000000000 : ℝ) (62674567359/125000000000 : ℝ) (250698269441/500000000000 : ℝ) (62674567359/125000000000 : ℝ) (250698269441/500000000000 : ℝ) (62674567359/125000000000 : ℝ) (250698269441/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67021/524288 : ℝ))) 6 (62674567359/125000000000 : ℝ) (250698269441/500000000000 : ℝ) (62674567359/125000000000 : ℝ) (250698269441/500000000000 : ℝ) (62674567359/125000000000 : ℝ) (250698269441/500000000000 : ℝ) (62674567359/125000000000 : ℝ) (250698269441/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67021/524288 : ℝ))) 7 (62674567359/125000000000 : ℝ) (250698269441/500000000000 : ℝ) (62674567359/125000000000 : ℝ) (250698269441/500000000000 : ℝ) (62674567359/125000000000 : ℝ) (250698269441/500000000000 : ℝ) (62674567359/125000000000 : ℝ) (250698269441/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67021/524288 : ℝ)) hmem 8 (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ) (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67021/524288 : ℝ))) hcmem 8 (62674567359/125000000000 : ℝ) (250698269441/500000000000 : ℝ) (62674567359/125000000000 : ℝ) (250698269441/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67021/524288 : ℝ)) (992058136797/1000000000000 : ℝ) (1240072671/1250000000 : ℝ) (62674567359/125000000000 : ℝ) (250698269441/500000000000 : ℝ) (793896861799/1000000000000 : ℝ) (396948430909/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0948_exp_lower
  have heNumeric : (2054901684421/1000000000000 : ℝ)/4 ≤ Real.exp (-21314123406301/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901684421/1000000000000 : ℝ)/4 ≤ Real.exp ((16755/131072 : ℝ)-(396948430909/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16755/131072 : ℝ) (67021/524288 : ℝ) (396948430909/500000000000 : ℝ) (2054901684421/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0949; no trusted numerical premise.
theorem cover8_leaf0949_exp_radius : (499002291123642627/500000000000000000 : ℝ) ≤ Real.exp ((-33511/2097152 : ℝ)/8) ∧ Real.exp ((-33511/2097152 : ℝ)/8) ≤ (199600916449457051/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33511/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0949_exp_lower : (14376772756631459/15625000000000000 : ℝ) ≤ Real.exp ((-85256493406371/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256493406371/128000000000000 : ℝ)/8) ≤ (920113456424413377/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256493406371/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0949_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450843967/500000000000 : ℝ) ≤ 4*Real.exp (67021/524288 : ℝ)*Real.exp (-mu (radius 8 (33511/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450843967/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33511/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0949_exp_radius
  have hrNumeric : (492073850767/500000000000 : ℝ) ≤ Real.exp (-33511/2097152 : ℝ) ∧ Real.exp (-33511/2097152 : ℝ) ≤ (196829540307/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492073850767/500000000000 : ℝ) ≤ (radius 8 (33511/262144 : ℝ)) ∧ (radius 8 (33511/262144 : ℝ)) ≤ (196829540307/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33511/262144 : ℝ)) (492073850767/500000000000 : ℝ) (196829540307/200000000000 : ℝ) (177350786757/1000000000000 : ℝ) (177350786763/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33511/262144 : ℝ)) (492073850767/500000000000 : ℝ) (196829540307/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33511/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492073850767/500000000000 : ℝ) (196829540307/200000000000 : ℝ) (992073850767/1000000000000 : ℝ) (62004615673/62500000000 : ℝ) (62002636711/62500000000 : ℝ) (992042187377/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33511/262144 : ℝ)) 1 (992073850767/1000000000000 : ℝ) (62004615673/62500000000 : ℝ) (62002636711/62500000000 : ℝ) (992042187377/1000000000000 : ℝ) (992058019071/1000000000000 : ℝ) (992058019073/1000000000000 : ℝ) (198411603789/200000000000 : ℝ) (992058018947/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33511/262144 : ℝ)) 2 (992058019071/1000000000000 : ℝ) (992058019073/1000000000000 : ℝ) (198411603789/200000000000 : ℝ) (992058018947/1000000000000 : ℝ) (15500906547/15625000000 : ℝ) (99205801901/100000000000 : ℝ) (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33511/262144 : ℝ)) 3 (15500906547/15625000000 : ℝ) (99205801901/100000000000 : ℝ) (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ) (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ) (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33511/262144 : ℝ)) 4 (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ) (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ) (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ) (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33511/262144 : ℝ)) 5 (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ) (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ) (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ) (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33511/262144 : ℝ)) 6 (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ) (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ) (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ) (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33511/262144 : ℝ)) 7 (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ) (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ) (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ) (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33511/262144 : ℝ))) (177350786757/1000000000000 : ℝ) (177350786763/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33511/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177350786757/1000000000000 : ℝ) (177350786763/1000000000000 : ℝ) (294337696689/500000000000 : ℝ) (294337696691/500000000000 : ℝ) (421130367887/1000000000000 : ℝ) (84226073579/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33511/262144 : ℝ))) 1 (294337696689/500000000000 : ℝ) (294337696691/500000000000 : ℝ) (421130367887/1000000000000 : ℝ) (84226073579/200000000000 : ℝ) (63112860079/125000000000 : ℝ) (504902880639/1000000000000 : ℝ) (248952347337/500000000000 : ℝ) (248952347341/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33511/262144 : ℝ))) 2 (63112860079/125000000000 : ℝ) (504902880639/1000000000000 : ℝ) (248952347337/500000000000 : ℝ) (248952347341/500000000000 : ℝ) (501403787653/1000000000000 : ℝ) (501403787661/1000000000000 : ℝ) (501391578131/1000000000000 : ℝ) (501391578139/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33511/262144 : ℝ))) 3 (501403787653/1000000000000 : ℝ) (501403787661/1000000000000 : ℝ) (501391578131/1000000000000 : ℝ) (501391578139/1000000000000 : ℝ) (125349420723/250000000000 : ℝ) (5013976829/10000000000 : ℝ) (250698841427/500000000000 : ℝ) (501397682863/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33511/262144 : ℝ))) 4 (125349420723/250000000000 : ℝ) (5013976829/10000000000 : ℝ) (250698841427/500000000000 : ℝ) (501397682863/1000000000000 : ℝ) (501397682873/1000000000000 : ℝ) (250698841441/500000000000 : ℝ) (62674710359/125000000000 : ℝ) (250698841441/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33511/262144 : ℝ))) 5 (501397682873/1000000000000 : ℝ) (250698841441/500000000000 : ℝ) (62674710359/125000000000 : ℝ) (250698841441/500000000000 : ℝ) (62674710359/125000000000 : ℝ) (250698841441/500000000000 : ℝ) (62674710359/125000000000 : ℝ) (250698841441/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33511/262144 : ℝ))) 6 (62674710359/125000000000 : ℝ) (250698841441/500000000000 : ℝ) (62674710359/125000000000 : ℝ) (250698841441/500000000000 : ℝ) (62674710359/125000000000 : ℝ) (250698841441/500000000000 : ℝ) (62674710359/125000000000 : ℝ) (250698841441/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33511/262144 : ℝ))) 7 (62674710359/125000000000 : ℝ) (250698841441/500000000000 : ℝ) (62674710359/125000000000 : ℝ) (250698841441/500000000000 : ℝ) (62674710359/125000000000 : ℝ) (250698841441/500000000000 : ℝ) (62674710359/125000000000 : ℝ) (250698841441/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33511/262144 : ℝ)) hmem 8 (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ) (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33511/262144 : ℝ))) hcmem 8 (62674710359/125000000000 : ℝ) (250698841441/500000000000 : ℝ) (62674710359/125000000000 : ℝ) (250698841441/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33511/262144 : ℝ)) (992058019007/1000000000000 : ℝ) (99205801901/100000000000 : ℝ) (62674710359/125000000000 : ℝ) (250698841441/500000000000 : ℝ) (793898767437/1000000000000 : ℝ) (793898767457/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0949_exp_lower
  have heNumeric : (1027450843967/500000000000 : ℝ)/4 ≤ Real.exp (-85256493406371/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450843967/500000000000 : ℝ)/4 ≤ Real.exp ((67021/524288 : ℝ)-(793898767457/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67021/524288 : ℝ) (33511/262144 : ℝ) (793898767457/1000000000000 : ℝ) (1027450843967/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0925_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0925_certificate
#check SmaleRate.Proofs.cover8_leaf0926_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0926_certificate
#check SmaleRate.Proofs.cover8_leaf0927_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0927_certificate
#check SmaleRate.Proofs.cover8_leaf0928_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0928_certificate
#check SmaleRate.Proofs.cover8_leaf0929_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0929_certificate
#check SmaleRate.Proofs.cover8_leaf0930_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0930_certificate
#check SmaleRate.Proofs.cover8_leaf0931_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0931_certificate
#check SmaleRate.Proofs.cover8_leaf0932_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0932_certificate
#check SmaleRate.Proofs.cover8_leaf0933_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0933_certificate
#check SmaleRate.Proofs.cover8_leaf0934_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0934_certificate
#check SmaleRate.Proofs.cover8_leaf0935_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0935_certificate
#check SmaleRate.Proofs.cover8_leaf0936_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0936_certificate
#check SmaleRate.Proofs.cover8_leaf0937_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0937_certificate
#check SmaleRate.Proofs.cover8_leaf0938_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0938_certificate
#check SmaleRate.Proofs.cover8_leaf0939_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0939_certificate
#check SmaleRate.Proofs.cover8_leaf0940_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0940_certificate
#check SmaleRate.Proofs.cover8_leaf0941_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0941_certificate
#check SmaleRate.Proofs.cover8_leaf0942_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0942_certificate
#check SmaleRate.Proofs.cover8_leaf0943_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0943_certificate
#check SmaleRate.Proofs.cover8_leaf0944_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0944_certificate
#check SmaleRate.Proofs.cover8_leaf0945_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0945_certificate
#check SmaleRate.Proofs.cover8_leaf0946_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0946_certificate
#check SmaleRate.Proofs.cover8_leaf0947_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0947_certificate
#check SmaleRate.Proofs.cover8_leaf0948_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0948_certificate
#check SmaleRate.Proofs.cover8_leaf0949_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0949_certificate
