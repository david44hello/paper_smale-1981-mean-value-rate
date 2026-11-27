/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0700; no trusted numerical premise.
theorem cover8_leaf0700_exp_radius : (998011988245486183/1000000000000000000 : ℝ) ≤ Real.exp ((-66773/4194304 : ℝ)/8) ∧ Real.exp ((-66773/4194304 : ℝ)/8) ≤ (124751498530685773/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66773/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0700_exp_lower : (920113476106839981/1000000000000000000 : ℝ) ≤ Real.exp ((-21314117875419/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314117875419/32000000000000 : ℝ)/8) ≤ (460056738053419991/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314117875419/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0700_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490203959/100000000000 : ℝ) ≤ 4*Real.exp (16693/131072 : ℝ)*Real.exp (-mu (radius 8 (66773/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (205490203959/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66773/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0700_exp_radius
  have hrNumeric : (246051532101/250000000000 : ℝ) ≤ Real.exp (-66773/4194304 : ℝ) ∧ Real.exp (-66773/4194304 : ℝ) ≤ (196841225681/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246051532101/250000000000 : ℝ) ≤ (radius 8 (66773/524288 : ℝ)) ∧ (radius 8 (66773/524288 : ℝ)) ≤ (196841225681/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66773/524288 : ℝ)) (246051532101/250000000000 : ℝ) (196841225681/200000000000 : ℝ) (177026260227/1000000000000 : ℝ) (177026260233/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66773/524288 : ℝ)) (246051532101/250000000000 : ℝ) (196841225681/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66773/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246051532101/250000000000 : ℝ) (196841225681/200000000000 : ℝ) (496051532101/500000000000 : ℝ) (992103064203/1000000000000 : ℝ) (992071634713/1000000000000 : ℝ) (198414326943/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66773/524288 : ℝ)) 1 (496051532101/500000000000 : ℝ) (992103064203/1000000000000 : ℝ) (992071634713/1000000000000 : ℝ) (198414326943/200000000000 : ℝ) (992087349457/1000000000000 : ℝ) (992087349459/1000000000000 : ℝ) (992087349333/1000000000000 : ℝ) (198417469867/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66773/524288 : ℝ)) 2 (992087349457/1000000000000 : ℝ) (992087349459/1000000000000 : ℝ) (992087349333/1000000000000 : ℝ) (198417469867/200000000000 : ℝ) (198417469879/200000000000 : ℝ) (992087349397/1000000000000 : ℝ) (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66773/524288 : ℝ)) 3 (198417469879/200000000000 : ℝ) (992087349397/1000000000000 : ℝ) (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ) (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ) (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66773/524288 : ℝ)) 4 (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ) (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ) (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ) (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66773/524288 : ℝ)) 5 (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ) (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ) (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ) (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66773/524288 : ℝ)) 6 (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ) (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ) (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ) (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66773/524288 : ℝ)) 7 (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ) (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ) (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ) (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66773/524288 : ℝ))) (177026260227/1000000000000 : ℝ) (177026260233/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66773/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177026260227/1000000000000 : ℝ) (177026260233/1000000000000 : ℝ) (588513130113/1000000000000 : ℝ) (588513130117/1000000000000 : ℝ) (84148977469/200000000000 : ℝ) (420744887353/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66773/524288 : ℝ))) 1 (588513130113/1000000000000 : ℝ) (588513130117/1000000000000 : ℝ) (84148977469/200000000000 : ℝ) (420744887353/1000000000000 : ℝ) (504629008729/1000000000000 : ℝ) (100925801747/200000000000 : ℝ) (248804084889/500000000000 : ℝ) (248804084893/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66773/524288 : ℝ))) 2 (504629008729/1000000000000 : ℝ) (100925801747/200000000000 : ℝ) (248804084889/500000000000 : ℝ) (248804084893/500000000000 : ℝ) (501118589253/1000000000000 : ℝ) (501118589261/1000000000000 : ℝ) (100221258713/200000000000 : ℝ) (501106293573/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66773/524288 : ℝ))) 3 (501118589253/1000000000000 : ℝ) (501118589261/1000000000000 : ℝ) (100221258713/200000000000 : ℝ) (501106293573/1000000000000 : ℝ) (501112441409/1000000000000 : ℝ) (501112441417/1000000000000 : ℝ) (501112441371/1000000000000 : ℝ) (25055622069/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66773/524288 : ℝ))) 4 (501112441409/1000000000000 : ℝ) (501112441417/1000000000000 : ℝ) (501112441371/1000000000000 : ℝ) (25055622069/50000000000 : ℝ) (50111244139/100000000000 : ℝ) (501112441399/1000000000000 : ℝ) (501112441389/1000000000000 : ℝ) (501112441399/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66773/524288 : ℝ))) 5 (50111244139/100000000000 : ℝ) (501112441399/1000000000000 : ℝ) (501112441389/1000000000000 : ℝ) (501112441399/1000000000000 : ℝ) (501112441389/1000000000000 : ℝ) (501112441399/1000000000000 : ℝ) (501112441389/1000000000000 : ℝ) (501112441399/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66773/524288 : ℝ))) 6 (501112441389/1000000000000 : ℝ) (501112441399/1000000000000 : ℝ) (501112441389/1000000000000 : ℝ) (501112441399/1000000000000 : ℝ) (501112441389/1000000000000 : ℝ) (501112441399/1000000000000 : ℝ) (501112441389/1000000000000 : ℝ) (501112441399/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66773/524288 : ℝ))) 7 (501112441389/1000000000000 : ℝ) (501112441399/1000000000000 : ℝ) (501112441389/1000000000000 : ℝ) (501112441399/1000000000000 : ℝ) (501112441389/1000000000000 : ℝ) (501112441399/1000000000000 : ℝ) (501112441389/1000000000000 : ℝ) (501112441399/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66773/524288 : ℝ)) hmem 8 (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ) (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66773/524288 : ℝ))) hcmem 8 (501112441389/1000000000000 : ℝ) (501112441399/1000000000000 : ℝ) (501112441389/1000000000000 : ℝ) (501112441399/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66773/524288 : ℝ)) (496043674697/500000000000 : ℝ) (992087349397/1000000000000 : ℝ) (501112441389/1000000000000 : ℝ) (501112441399/1000000000000 : ℝ) (396711833249/500000000000 : ℝ) (793423666517/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0700_exp_lower
  have heNumeric : (205490203959/100000000000 : ℝ)/4 ≤ Real.exp (-21314117875419/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490203959/100000000000 : ℝ)/4 ≤ Real.exp ((16693/131072 : ℝ)-(793423666517/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16693/131072 : ℝ) (66773/524288 : ℝ) (793423666517/1000000000000 : ℝ) (205490203959/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0701; no trusted numerical premise.
theorem cover8_leaf0701_exp_radius : (499005979251205803/500000000000000000 : ℝ) ≤ Real.exp ((-33387/2097152 : ℝ)/8) ∧ Real.exp ((-33387/2097152 : ℝ)/8) ≤ (998011958502411607/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33387/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0701_exp_lower : (230028368937908487/250000000000000000 : ℝ) ≤ Real.exp ((-85256471896987/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256471896987/128000000000000 : ℝ)/8) ≤ (920113475751633949/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256471896987/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0701_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725508311/250000000000 : ℝ) ≤ 4*Real.exp (66773/524288 : ℝ)*Real.exp (-mu (radius 8 (33387/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725508311/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33387/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0701_exp_radius
  have hrNumeric : (984205893751/1000000000000 : ℝ) ≤ Real.exp (-33387/2097152 : ℝ) ∧ Real.exp (-33387/2097152 : ℝ) ≤ (123025736719/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984205893751/1000000000000 : ℝ) ≤ (radius 8 (33387/262144 : ℝ)) ∧ (radius 8 (33387/262144 : ℝ)) ≤ (123025736719/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33387/262144 : ℝ)) (984205893751/1000000000000 : ℝ) (123025736719/125000000000 : ℝ) (177027564813/1000000000000 : ℝ) (8851378241/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33387/262144 : ℝ)) (984205893751/1000000000000 : ℝ) (123025736719/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33387/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984205893751/1000000000000 : ℝ) (123025736719/125000000000 : ℝ) (317472943/320000000 : ℝ) (248025736719/250000000000 : ℝ) (992071516449/1000000000000 : ℝ) (992071516451/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33387/262144 : ℝ)) 1 (317472943/320000000 : ℝ) (248025736719/250000000000 : ℝ) (992071516449/1000000000000 : ℝ) (992071516451/1000000000000 : ℝ) (496043615831/500000000000 : ℝ) (62005451979/62500000000 : ℝ) (992087231537/1000000000000 : ℝ) (49604361577/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33387/262144 : ℝ)) 2 (496043615831/500000000000 : ℝ) (62005451979/62500000000 : ℝ) (992087231537/1000000000000 : ℝ) (49604361577/50000000000 : ℝ) (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ) (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33387/262144 : ℝ)) 3 (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ) (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ) (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ) (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33387/262144 : ℝ)) 4 (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ) (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ) (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ) (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33387/262144 : ℝ)) 5 (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ) (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ) (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ) (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33387/262144 : ℝ)) 6 (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ) (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ) (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ) (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33387/262144 : ℝ)) 7 (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ) (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ) (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ) (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33387/262144 : ℝ))) (177027564813/1000000000000 : ℝ) (8851378241/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33387/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177027564813/1000000000000 : ℝ) (8851378241/50000000000 : ℝ) (294256891203/500000000000 : ℝ) (58851378241/100000000000 : ℝ) (420746437671/1000000000000 : ℝ) (5259330471/12500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33387/262144 : ℝ))) 1 (294256891203/500000000000 : ℝ) (58851378241/100000000000 : ℝ) (420746437671/1000000000000 : ℝ) (5259330471/12500000000 : ℝ) (252315055019/500000000000 : ℝ) (100926022009/200000000000 : ℝ) (497609362319/1000000000000 : ℝ) (497609362327/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33387/262144 : ℝ))) 2 (252315055019/500000000000 : ℝ) (100926022009/200000000000 : ℝ) (497609362319/1000000000000 : ℝ) (497609362327/1000000000000 : ℝ) (250559868089/500000000000 : ℝ) (250559868093/500000000000 : ℝ) (501107440837/1000000000000 : ℝ) (250553720423/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33387/262144 : ℝ))) 3 (250559868089/500000000000 : ℝ) (250559868093/500000000000 : ℝ) (501107440837/1000000000000 : ℝ) (250553720423/500000000000 : ℝ) (501113588507/1000000000000 : ℝ) (125278397129/250000000000 : ℝ) (501113588469/1000000000000 : ℝ) (501113588479/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33387/262144 : ℝ))) 4 (501113588507/1000000000000 : ℝ) (125278397129/250000000000 : ℝ) (501113588469/1000000000000 : ℝ) (501113588479/1000000000000 : ℝ) (62639198561/125000000000 : ℝ) (250556794249/500000000000 : ℝ) (501113588487/1000000000000 : ℝ) (250556794249/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33387/262144 : ℝ))) 5 (62639198561/125000000000 : ℝ) (250556794249/500000000000 : ℝ) (501113588487/1000000000000 : ℝ) (250556794249/500000000000 : ℝ) (501113588487/1000000000000 : ℝ) (250556794249/500000000000 : ℝ) (501113588487/1000000000000 : ℝ) (250556794249/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33387/262144 : ℝ))) 6 (501113588487/1000000000000 : ℝ) (250556794249/500000000000 : ℝ) (501113588487/1000000000000 : ℝ) (250556794249/500000000000 : ℝ) (501113588487/1000000000000 : ℝ) (250556794249/500000000000 : ℝ) (501113588487/1000000000000 : ℝ) (250556794249/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33387/262144 : ℝ))) 7 (501113588487/1000000000000 : ℝ) (250556794249/500000000000 : ℝ) (501113588487/1000000000000 : ℝ) (250556794249/500000000000 : ℝ) (501113588487/1000000000000 : ℝ) (250556794249/500000000000 : ℝ) (501113588487/1000000000000 : ℝ) (250556794249/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33387/262144 : ℝ)) hmem 8 (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ) (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33387/262144 : ℝ))) hcmem 8 (501113588487/1000000000000 : ℝ) (250556794249/500000000000 : ℝ) (501113588487/1000000000000 : ℝ) (250556794249/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33387/262144 : ℝ)) (992087231599/1000000000000 : ℝ) (496043615801/500000000000 : ℝ) (501113588487/1000000000000 : ℝ) (250556794249/500000000000 : ℝ) (793425576933/1000000000000 : ℝ) (396712788477/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0701_exp_lower
  have heNumeric : (513725508311/250000000000 : ℝ)/4 ≤ Real.exp (-85256471896987/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725508311/250000000000 : ℝ)/4 ≤ Real.exp ((66773/524288 : ℝ)-(396712788477/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66773/524288 : ℝ) (33387/262144 : ℝ) (396712788477/500000000000 : ℝ) (513725508311/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0702; no trusted numerical premise.
theorem cover8_leaf0702_exp_radius : (199602385751867583/200000000000000000 : ℝ) ≤ Real.exp ((-66775/4194304 : ℝ)/8) ∧ Real.exp ((-66775/4194304 : ℝ)/8) ≤ (249502982189834479/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66775/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0702_exp_lower : (460056737699364099/500000000000000000 : ℝ) ≤ Real.exp ((-42628236144869/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628236144869/64000000000000 : ℝ)/8) ≤ (920113475398728199/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628236144869/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0702_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902026939/1000000000000 : ℝ) ≤ 4*Real.exp (33387/262144 : ℝ)*Real.exp (-mu (radius 8 (66775/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902026939/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66775/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0702_exp_radius
  have hrNumeric : (492102829549/500000000000 : ℝ) ≤ Real.exp (-66775/4194304 : ℝ) ∧ Real.exp (-66775/4194304 : ℝ) ≤ (984205659099/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492102829549/500000000000 : ℝ) ≤ (radius 8 (66775/524288 : ℝ)) ∧ (radius 8 (66775/524288 : ℝ)) ≤ (984205659099/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66775/524288 : ℝ)) (492102829549/500000000000 : ℝ) (984205659099/1000000000000 : ℝ) (17702886939/100000000000 : ℝ) (44257217349/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66775/524288 : ℝ)) (492102829549/500000000000 : ℝ) (984205659099/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66775/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492102829549/500000000000 : ℝ) (984205659099/1000000000000 : ℝ) (992102829549/1000000000000 : ℝ) (19842056591/20000000000 : ℝ) (198414279637/200000000000 : ℝ) (992071398187/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66775/524288 : ℝ)) 1 (992102829549/1000000000000 : ℝ) (19842056591/20000000000 : ℝ) (198414279637/200000000000 : ℝ) (992071398187/1000000000000 : ℝ) (992087113867/1000000000000 : ℝ) (992087113869/1000000000000 : ℝ) (496043556871/500000000000 : ℝ) (198417422749/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66775/524288 : ℝ)) 2 (992087113867/1000000000000 : ℝ) (992087113869/1000000000000 : ℝ) (496043556871/500000000000 : ℝ) (198417422749/200000000000 : ℝ) (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ) (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66775/524288 : ℝ)) 3 (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ) (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ) (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ) (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66775/524288 : ℝ)) 4 (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ) (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ) (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ) (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66775/524288 : ℝ)) 5 (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ) (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ) (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ) (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66775/524288 : ℝ)) 6 (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ) (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ) (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ) (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66775/524288 : ℝ)) 7 (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ) (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ) (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ) (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66775/524288 : ℝ))) (17702886939/100000000000 : ℝ) (44257217349/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66775/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17702886939/100000000000 : ℝ) (44257217349/250000000000 : ℝ) (117702886939/200000000000 : ℝ) (294257217349/500000000000 : ℝ) (21037399399/50000000000 : ℝ) (420747987989/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66775/524288 : ℝ))) 1 (117702886939/200000000000 : ℝ) (294257217349/500000000000 : ℝ) (21037399399/50000000000 : ℝ) (420747987989/1000000000000 : ℝ) (504631211337/1000000000000 : ℝ) (31539450709/62500000000 : ℝ) (248805277423/500000000000 : ℝ) (248805277427/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66775/524288 : ℝ))) 2 (504631211337/1000000000000 : ℝ) (31539450709/62500000000 : ℝ) (248805277423/500000000000 : ℝ) (248805277427/500000000000 : ℝ) (501120883091/1000000000000 : ℝ) (501120883099/1000000000000 : ℝ) (250554294049/500000000000 : ℝ) (250554294053/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66775/524288 : ℝ))) 3 (501120883091/1000000000000 : ℝ) (501120883099/1000000000000 : ℝ) (250554294049/500000000000 : ℝ) (250554294053/500000000000 : ℝ) (250557367797/500000000000 : ℝ) (501114735603/1000000000000 : ℝ) (125278683889/250000000000 : ℝ) (100222947113/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66775/524288 : ℝ))) 4 (250557367797/500000000000 : ℝ) (501114735603/1000000000000 : ℝ) (125278683889/250000000000 : ℝ) (100222947113/200000000000 : ℝ) (20044589423/40000000000 : ℝ) (15659835487/31250000000 : ℝ) (250557367787/500000000000 : ℝ) (15659835487/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66775/524288 : ℝ))) 5 (20044589423/40000000000 : ℝ) (15659835487/31250000000 : ℝ) (250557367787/500000000000 : ℝ) (15659835487/31250000000 : ℝ) (250557367787/500000000000 : ℝ) (15659835487/31250000000 : ℝ) (250557367787/500000000000 : ℝ) (15659835487/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66775/524288 : ℝ))) 6 (250557367787/500000000000 : ℝ) (15659835487/31250000000 : ℝ) (250557367787/500000000000 : ℝ) (15659835487/31250000000 : ℝ) (250557367787/500000000000 : ℝ) (15659835487/31250000000 : ℝ) (250557367787/500000000000 : ℝ) (15659835487/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66775/524288 : ℝ))) 7 (250557367787/500000000000 : ℝ) (15659835487/31250000000 : ℝ) (250557367787/500000000000 : ℝ) (15659835487/31250000000 : ℝ) (250557367787/500000000000 : ℝ) (15659835487/31250000000 : ℝ) (250557367787/500000000000 : ℝ) (15659835487/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66775/524288 : ℝ)) hmem 8 (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ) (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66775/524288 : ℝ))) hcmem 8 (250557367787/500000000000 : ℝ) (15659835487/31250000000 : ℝ) (250557367787/500000000000 : ℝ) (15659835487/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66775/524288 : ℝ)) (248021778451/250000000000 : ℝ) (992087113807/1000000000000 : ℝ) (250557367787/500000000000 : ℝ) (15659835487/31250000000 : ℝ) (99178435919/125000000000 : ℝ) (793427487371/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0702_exp_lower
  have heNumeric : (2054902026939/1000000000000 : ℝ)/4 ≤ Real.exp (-42628236144869/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902026939/1000000000000 : ℝ)/4 ≤ Real.exp ((33387/262144 : ℝ)-(793427487371/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33387/262144 : ℝ) (66775/524288 : ℝ) (793427487371/1000000000000 : ℝ) (2054902026939/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0703; no trusted numerical premise.
theorem cover8_leaf0703_exp_radius : (998011899016265111/1000000000000000000 : ℝ) ≤ Real.exp ((-8347/524288 : ℝ)/8) ∧ Real.exp ((-8347/524288 : ℝ)/8) ≤ (124751487377033139/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8347/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0703_exp_lower : (920113475047547661/1000000000000000000 : ℝ) ≤ Real.exp ((-85256472680569/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256472680569/128000000000000 : ℝ)/8) ≤ (460056737523773831/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256472680569/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0703_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862752583/125000000000 : ℝ) ≤ 4*Real.exp (66775/524288 : ℝ)*Real.exp (-mu (radius 8 (8347/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (256862752583/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8347/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0703_exp_radius
  have hrNumeric : (196841084889/200000000000 : ℝ) ≤ Real.exp (-8347/524288 : ℝ) ∧ Real.exp (-8347/524288 : ℝ) ≤ (492102712223/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196841084889/200000000000 : ℝ) ≤ (radius 8 (8347/65536 : ℝ)) ∧ (radius 8 (8347/65536 : ℝ)) ≤ (492102712223/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8347/65536 : ℝ)) (196841084889/200000000000 : ℝ) (492102712223/500000000000 : ℝ) (44257543489/250000000000 : ℝ) (177030173963/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8347/65536 : ℝ)) (196841084889/200000000000 : ℝ) (492102712223/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8347/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196841084889/200000000000 : ℝ) (492102712223/500000000000 : ℝ) (496051356111/500000000000 : ℝ) (992102712223/1000000000000 : ℝ) (992071279921/1000000000000 : ℝ) (496035639961/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8347/65536 : ℝ)) 1 (496051356111/500000000000 : ℝ) (992102712223/1000000000000 : ℝ) (992071279921/1000000000000 : ℝ) (496035639961/500000000000 : ℝ) (992086996071/1000000000000 : ℝ) (992086996073/1000000000000 : ℝ) (992086995947/1000000000000 : ℝ) (992086995949/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8347/65536 : ℝ)) 2 (992086996071/1000000000000 : ℝ) (992086996073/1000000000000 : ℝ) (992086995947/1000000000000 : ℝ) (992086995949/1000000000000 : ℝ) (992086996009/1000000000000 : ℝ) (992086996011/1000000000000 : ℝ) (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8347/65536 : ℝ)) 3 (992086996009/1000000000000 : ℝ) (992086996011/1000000000000 : ℝ) (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ) (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ) (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8347/65536 : ℝ)) 4 (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ) (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ) (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ) (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8347/65536 : ℝ)) 5 (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ) (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ) (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ) (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8347/65536 : ℝ)) 6 (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ) (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ) (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ) (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8347/65536 : ℝ)) 7 (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ) (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ) (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ) (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8347/65536 : ℝ))) (44257543489/250000000000 : ℝ) (177030173963/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8347/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44257543489/250000000000 : ℝ) (177030173963/1000000000000 : ℝ) (294257543489/500000000000 : ℝ) (294257543491/500000000000 : ℝ) (420749538271/1000000000000 : ℝ) (420749538281/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8347/65536 : ℝ))) 1 (294257543489/500000000000 : ℝ) (294257543491/500000000000 : ℝ) (420749538271/1000000000000 : ℝ) (420749538281/1000000000000 : ℝ) (31539519539/62500000000 : ℝ) (63079039079/125000000000 : ℝ) (3110073421/6250000000 : ℝ) (497611747369/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8347/65536 : ℝ))) 2 (31539519539/62500000000 : ℝ) (63079039079/125000000000 : ℝ) (3110073421/6250000000 : ℝ) (497611747369/1000000000000 : ℝ) (62640253749/125000000000 : ℝ) (501122030001/1000000000000 : ℝ) (250554867673/500000000000 : ℝ) (125277433839/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8347/65536 : ℝ))) 3 (62640253749/125000000000 : ℝ) (501122030001/1000000000000 : ℝ) (250554867673/500000000000 : ℝ) (125277433839/250000000000 : ℝ) (501115882669/1000000000000 : ℝ) (501115882679/1000000000000 : ℝ) (501115882631/1000000000000 : ℝ) (501115882641/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8347/65536 : ℝ))) 4 (501115882669/1000000000000 : ℝ) (501115882679/1000000000000 : ℝ) (501115882631/1000000000000 : ℝ) (501115882641/1000000000000 : ℝ) (10022317653/20000000000 : ℝ) (25055794133/50000000000 : ℝ) (501115882649/1000000000000 : ℝ) (25055794133/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8347/65536 : ℝ))) 5 (10022317653/20000000000 : ℝ) (25055794133/50000000000 : ℝ) (501115882649/1000000000000 : ℝ) (25055794133/50000000000 : ℝ) (501115882649/1000000000000 : ℝ) (25055794133/50000000000 : ℝ) (501115882649/1000000000000 : ℝ) (25055794133/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8347/65536 : ℝ))) 6 (501115882649/1000000000000 : ℝ) (25055794133/50000000000 : ℝ) (501115882649/1000000000000 : ℝ) (25055794133/50000000000 : ℝ) (501115882649/1000000000000 : ℝ) (25055794133/50000000000 : ℝ) (501115882649/1000000000000 : ℝ) (25055794133/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8347/65536 : ℝ))) 7 (501115882649/1000000000000 : ℝ) (25055794133/50000000000 : ℝ) (501115882649/1000000000000 : ℝ) (25055794133/50000000000 : ℝ) (501115882649/1000000000000 : ℝ) (25055794133/50000000000 : ℝ) (501115882649/1000000000000 : ℝ) (25055794133/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8347/65536 : ℝ)) hmem 8 (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ) (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8347/65536 : ℝ))) hcmem 8 (501115882649/1000000000000 : ℝ) (25055794133/50000000000 : ℝ) (501115882649/1000000000000 : ℝ) (25055794133/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8347/65536 : ℝ)) (124010874501/125000000000 : ℝ) (992086996011/1000000000000 : ℝ) (501115882649/1000000000000 : ℝ) (25055794133/50000000000 : ℝ) (793429397753/1000000000000 : ℝ) (793429397773/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0703_exp_lower
  have heNumeric : (256862752583/125000000000 : ℝ)/4 ≤ Real.exp (-85256472680569/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862752583/125000000000 : ℝ)/4 ≤ Real.exp ((66775/524288 : ℝ)-(793429397773/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66775/524288 : ℝ) (8347/65536 : ℝ) (793429397773/1000000000000 : ℝ) (256862752583/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0704; no trusted numerical premise.
theorem cover8_leaf0704_exp_radius : (998011869273193193/1000000000000000000 : ℝ) ≤ Real.exp ((-66777/4194304 : ℝ)/8) ∧ Real.exp ((-66777/4194304 : ℝ)/8) ≤ (499005934636596597/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66777/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0704_exp_lower : (920113474699012451/1000000000000000000 : ℝ) ≤ Real.exp ((-10657059133557/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657059133557/16000000000000 : ℝ)/8) ≤ (230028368674753113/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657059133557/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0704_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902014437/1000000000000 : ℝ) ≤ 4*Real.exp (8347/65536 : ℝ)*Real.exp (-mu (radius 8 (66777/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902014437/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66777/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0704_exp_radius
  have hrNumeric : (30756412181/31250000000 : ℝ) ≤ Real.exp (-66777/4194304 : ℝ) ∧ Real.exp (-66777/4194304 : ℝ) ≤ (984205189793/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30756412181/31250000000 : ℝ) ≤ (radius 8 (66777/524288 : ℝ)) ∧ (radius 8 (66777/524288 : ℝ)) ≤ (984205189793/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66777/524288 : ℝ)) (30756412181/31250000000 : ℝ) (984205189793/1000000000000 : ℝ) (177031478513/1000000000000 : ℝ) (177031478519/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66777/524288 : ℝ)) (30756412181/31250000000 : ℝ) (984205189793/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66777/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30756412181/31250000000 : ℝ) (984205189793/1000000000000 : ℝ) (62006412181/62500000000 : ℝ) (992102594897/1000000000000 : ℝ) (992071161657/1000000000000 : ℝ) (496035580829/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66777/524288 : ℝ)) 1 (62006412181/62500000000 : ℝ) (992102594897/1000000000000 : ℝ) (992071161657/1000000000000 : ℝ) (496035580829/500000000000 : ℝ) (248021719569/250000000000 : ℝ) (496043439139/500000000000 : ℝ) (124010859769/125000000000 : ℝ) (496043439077/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66777/524288 : ℝ)) 2 (248021719569/250000000000 : ℝ) (496043439139/500000000000 : ℝ) (124010859769/125000000000 : ℝ) (496043439077/500000000000 : ℝ) (496043439107/500000000000 : ℝ) (124010859777/125000000000 : ℝ) (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66777/524288 : ℝ)) 3 (496043439107/500000000000 : ℝ) (124010859777/125000000000 : ℝ) (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ) (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ) (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66777/524288 : ℝ)) 4 (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ) (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ) (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ) (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66777/524288 : ℝ)) 5 (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ) (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ) (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ) (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66777/524288 : ℝ)) 6 (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ) (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ) (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ) (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66777/524288 : ℝ)) 7 (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ) (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ) (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ) (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66777/524288 : ℝ))) (177031478513/1000000000000 : ℝ) (177031478519/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66777/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177031478513/1000000000000 : ℝ) (177031478519/1000000000000 : ℝ) (73564467407/125000000000 : ℝ) (29425786963/50000000000 : ℝ) (210375544273/500000000000 : ℝ) (210375544277/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66777/524288 : ℝ))) 1 (73564467407/125000000000 : ℝ) (29425786963/50000000000 : ℝ) (210375544273/500000000000 : ℝ) (210375544277/500000000000 : ℝ) (504633413901/1000000000000 : ℝ) (504633413907/1000000000000 : ℝ) (248806469931/500000000000 : ℝ) (497612939869/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66777/524288 : ℝ))) 2 (504633413901/1000000000000 : ℝ) (504633413907/1000000000000 : ℝ) (248806469931/500000000000 : ℝ) (497612939869/1000000000000 : ℝ) (501123176881/1000000000000 : ℝ) (62640397111/125000000000 : ℝ) (501110882583/1000000000000 : ℝ) (501110882591/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66777/524288 : ℝ))) 3 (501123176881/1000000000000 : ℝ) (62640397111/125000000000 : ℝ) (501110882583/1000000000000 : ℝ) (501110882591/1000000000000 : ℝ) (125279257433/250000000000 : ℝ) (25055851487/50000000000 : ℝ) (250558514847/500000000000 : ℝ) (250558514851/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66777/524288 : ℝ))) 4 (125279257433/250000000000 : ℝ) (25055851487/50000000000 : ℝ) (250558514847/500000000000 : ℝ) (250558514851/500000000000 : ℝ) (501117029713/1000000000000 : ℝ) (501117029721/1000000000000 : ℝ) (31319814357/62500000000 : ℝ) (501117029721/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66777/524288 : ℝ))) 5 (501117029713/1000000000000 : ℝ) (501117029721/1000000000000 : ℝ) (31319814357/62500000000 : ℝ) (501117029721/1000000000000 : ℝ) (31319814357/62500000000 : ℝ) (501117029721/1000000000000 : ℝ) (31319814357/62500000000 : ℝ) (501117029721/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66777/524288 : ℝ))) 6 (31319814357/62500000000 : ℝ) (501117029721/1000000000000 : ℝ) (31319814357/62500000000 : ℝ) (501117029721/1000000000000 : ℝ) (31319814357/62500000000 : ℝ) (501117029721/1000000000000 : ℝ) (31319814357/62500000000 : ℝ) (501117029721/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66777/524288 : ℝ))) 7 (31319814357/62500000000 : ℝ) (501117029721/1000000000000 : ℝ) (31319814357/62500000000 : ℝ) (501117029721/1000000000000 : ℝ) (31319814357/62500000000 : ℝ) (501117029721/1000000000000 : ℝ) (31319814357/62500000000 : ℝ) (501117029721/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66777/524288 : ℝ)) hmem 8 (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ) (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66777/524288 : ℝ))) hcmem 8 (31319814357/62500000000 : ℝ) (501117029721/1000000000000 : ℝ) (31319814357/62500000000 : ℝ) (501117029721/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66777/524288 : ℝ)) (992086878213/1000000000000 : ℝ) (124010859777/125000000000 : ℝ) (31319814357/62500000000 : ℝ) (501117029721/1000000000000 : ℝ) (396715654067/500000000000 : ℝ) (99178913519/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0704_exp_lower
  have heNumeric : (2054902014437/1000000000000 : ℝ)/4 ≤ Real.exp (-10657059133557/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902014437/1000000000000 : ℝ)/4 ≤ Real.exp ((8347/65536 : ℝ)-(99178913519/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8347/65536 : ℝ) (66777/524288 : ℝ) (99178913519/125000000000 : ℝ) (2054902014437/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0705; no trusted numerical premise.
theorem cover8_leaf0705_exp_radius : (998011839530122161/1000000000000000000 : ℝ) ≤ Real.exp ((-33389/2097152 : ℝ)/8) ∧ Real.exp ((-33389/2097152 : ℝ)/8) ≤ (499005919765061081/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33389/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0705_exp_lower : (230028368588079367/250000000000000000 : ℝ) ≤ Real.exp ((-17051294690859/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051294690859/25600000000000 : ℝ)/8) ≤ (920113474352317469/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051294690859/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0705_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902008243/1000000000000 : ℝ) ≤ 4*Real.exp (66777/524288 : ℝ)*Real.exp (-mu (radius 8 (33389/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902008243/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33389/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0705_exp_radius
  have hrNumeric : (984204955139/1000000000000 : ℝ) ≤ Real.exp (-33389/2097152 : ℝ) ∧ Real.exp (-33389/2097152 : ℝ) ≤ (49210247757/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984204955139/1000000000000 : ℝ) ≤ (radius 8 (33389/262144 : ℝ)) ∧ (radius 8 (33389/262144 : ℝ)) ≤ (49210247757/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33389/262144 : ℝ)) (984204955139/1000000000000 : ℝ) (49210247757/50000000000 : ℝ) (177032783059/1000000000000 : ℝ) (88516391533/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33389/262144 : ℝ)) (984204955139/1000000000000 : ℝ) (49210247757/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33389/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984204955139/1000000000000 : ℝ) (49210247757/50000000000 : ℝ) (992102477569/1000000000000 : ℝ) (99210247757/100000000000 : ℝ) (992071043393/1000000000000 : ℝ) (496035521697/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33389/262144 : ℝ)) 1 (992102477569/1000000000000 : ℝ) (99210247757/100000000000 : ℝ) (992071043393/1000000000000 : ℝ) (496035521697/500000000000 : ℝ) (992086760481/1000000000000 : ℝ) (496043380241/500000000000 : ℝ) (248021690089/250000000000 : ℝ) (496043380179/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33389/262144 : ℝ)) 2 (992086760481/1000000000000 : ℝ) (496043380241/500000000000 : ℝ) (248021690089/250000000000 : ℝ) (496043380179/500000000000 : ℝ) (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ) (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33389/262144 : ℝ)) 3 (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ) (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ) (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ) (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33389/262144 : ℝ)) 4 (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ) (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ) (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ) (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33389/262144 : ℝ)) 5 (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ) (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ) (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ) (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33389/262144 : ℝ)) 6 (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ) (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ) (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ) (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33389/262144 : ℝ)) 7 (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ) (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ) (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ) (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33389/262144 : ℝ))) (177032783059/1000000000000 : ℝ) (88516391533/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33389/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177032783059/1000000000000 : ℝ) (88516391533/500000000000 : ℝ) (588516391529/1000000000000 : ℝ) (588516391533/1000000000000 : ℝ) (210376319401/500000000000 : ℝ) (420752638811/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33389/262144 : ℝ))) 1 (588516391529/1000000000000 : ℝ) (588516391533/1000000000000 : ℝ) (210376319401/500000000000 : ℝ) (420752638811/1000000000000 : ℝ) (100926903033/200000000000 : ℝ) (126158628793/250000000000 : ℝ) (497614132349/1000000000000 : ℝ) (497614132357/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33389/262144 : ℝ))) 2 (100926903033/200000000000 : ℝ) (126158628793/250000000000 : ℝ) (497614132349/1000000000000 : ℝ) (497614132357/1000000000000 : ℝ) (501124323757/1000000000000 : ℝ) (100224864753/200000000000 : ℝ) (250556014903/500000000000 : ℝ) (100222405963/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33389/262144 : ℝ))) 3 (501124323757/1000000000000 : ℝ) (100224864753/200000000000 : ℝ) (250556014903/500000000000 : ℝ) (100222405963/200000000000 : ℝ) (501118176781/1000000000000 : ℝ) (50111817679/100000000000 : ℝ) (501118176743/1000000000000 : ℝ) (501118176753/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33389/262144 : ℝ))) 4 (501118176781/1000000000000 : ℝ) (50111817679/100000000000 : ℝ) (501118176743/1000000000000 : ℝ) (501118176753/1000000000000 : ℝ) (250559088381/500000000000 : ℝ) (125279544193/250000000000 : ℝ) (501118176761/1000000000000 : ℝ) (125279544193/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33389/262144 : ℝ))) 5 (250559088381/500000000000 : ℝ) (125279544193/250000000000 : ℝ) (501118176761/1000000000000 : ℝ) (125279544193/250000000000 : ℝ) (501118176761/1000000000000 : ℝ) (125279544193/250000000000 : ℝ) (501118176761/1000000000000 : ℝ) (125279544193/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33389/262144 : ℝ))) 6 (501118176761/1000000000000 : ℝ) (125279544193/250000000000 : ℝ) (501118176761/1000000000000 : ℝ) (125279544193/250000000000 : ℝ) (501118176761/1000000000000 : ℝ) (125279544193/250000000000 : ℝ) (501118176761/1000000000000 : ℝ) (125279544193/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33389/262144 : ℝ))) 7 (501118176761/1000000000000 : ℝ) (125279544193/250000000000 : ℝ) (501118176761/1000000000000 : ℝ) (125279544193/250000000000 : ℝ) (501118176761/1000000000000 : ℝ) (125279544193/250000000000 : ℝ) (501118176761/1000000000000 : ℝ) (125279544193/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33389/262144 : ℝ)) hmem 8 (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ) (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33389/262144 : ℝ))) hcmem 8 (501118176761/1000000000000 : ℝ) (125279544193/250000000000 : ℝ) (501118176761/1000000000000 : ℝ) (125279544193/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33389/262144 : ℝ)) (496043380209/500000000000 : ℝ) (49604338021/50000000000 : ℝ) (501118176761/1000000000000 : ℝ) (125279544193/250000000000 : ℝ) (158686643699/200000000000 : ℝ) (158686643703/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0705_exp_lower
  have heNumeric : (2054902008243/1000000000000 : ℝ)/4 ≤ Real.exp (-17051294690859/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902008243/1000000000000 : ℝ)/4 ≤ Real.exp ((66777/524288 : ℝ)-(158686643703/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66777/524288 : ℝ) (33389/262144 : ℝ) (158686643703/200000000000 : ℝ) (2054902008243/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0706; no trusted numerical premise.
theorem cover8_leaf0706_exp_radius : (62375738111690751/62500000000000000 : ℝ) ≤ Real.exp ((-66779/4194304 : ℝ)/8) ∧ Real.exp ((-66779/4194304 : ℝ)/8) ≤ (998011809787052017/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66779/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0706_exp_lower : (57507092125495173/62500000000000000 : ℝ) ≤ Real.exp ((-42628236918787/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628236918787/64000000000000 : ℝ)/8) ≤ (920113474007922769/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628236918787/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0706_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490200209/100000000000 : ℝ) ≤ 4*Real.exp (33389/262144 : ℝ)*Real.exp (-mu (radius 8 (66779/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (205490200209/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66779/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0706_exp_radius
  have hrNumeric : (492102360243/500000000000 : ℝ) ≤ Real.exp (-66779/4194304 : ℝ) ∧ Real.exp (-66779/4194304 : ℝ) ≤ (984204720487/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492102360243/500000000000 : ℝ) ≤ (radius 8 (66779/524288 : ℝ)) ∧ (radius 8 (66779/524288 : ℝ)) ≤ (984204720487/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66779/524288 : ℝ)) (492102360243/500000000000 : ℝ) (984204720487/1000000000000 : ℝ) (44258521899/250000000000 : ℝ) (177034087603/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66779/524288 : ℝ)) (492102360243/500000000000 : ℝ) (984204720487/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66779/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492102360243/500000000000 : ℝ) (984204720487/1000000000000 : ℝ) (992102360243/1000000000000 : ℝ) (248025590061/250000000000 : ℝ) (124008865641/125000000000 : ℝ) (99207092513/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66779/524288 : ℝ)) 1 (992102360243/1000000000000 : ℝ) (248025590061/250000000000 : ℝ) (124008865641/125000000000 : ℝ) (99207092513/100000000000 : ℝ) (198417328537/200000000000 : ℝ) (992086642687/1000000000000 : ℝ) (1550135379/1562500000 : ℝ) (992086642563/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66779/524288 : ℝ)) 2 (198417328537/200000000000 : ℝ) (992086642687/1000000000000 : ℝ) (1550135379/1562500000 : ℝ) (992086642563/1000000000000 : ℝ) (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ) (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66779/524288 : ℝ)) 3 (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ) (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ) (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ) (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66779/524288 : ℝ)) 4 (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ) (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ) (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ) (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66779/524288 : ℝ)) 5 (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ) (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ) (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ) (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66779/524288 : ℝ)) 6 (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ) (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ) (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ) (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66779/524288 : ℝ)) 7 (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ) (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ) (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ) (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66779/524288 : ℝ))) (44258521899/250000000000 : ℝ) (177034087603/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66779/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44258521899/250000000000 : ℝ) (177034087603/1000000000000 : ℝ) (294258521899/500000000000 : ℝ) (294258521901/500000000000 : ℝ) (420754189041/1000000000000 : ℝ) (8415083781/20000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66779/524288 : ℝ))) 1 (294258521899/500000000000 : ℝ) (294258521901/500000000000 : ℝ) (420754189041/1000000000000 : ℝ) (8415083781/20000000000 : ℝ) (504635616419/1000000000000 : ℝ) (252317808213/500000000000 : ℝ) (62201915603/125000000000 : ℝ) (15550478901/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66779/524288 : ℝ))) 2 (504635616419/1000000000000 : ℝ) (252317808213/500000000000 : ℝ) (62201915603/125000000000 : ℝ) (15550478901/31250000000 : ℝ) (501125470621/1000000000000 : ℝ) (501125470629/1000000000000 : ℝ) (501113177019/1000000000000 : ℝ) (501113177027/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66779/524288 : ℝ))) 3 (501125470621/1000000000000 : ℝ) (501125470629/1000000000000 : ℝ) (501113177019/1000000000000 : ℝ) (501113177027/1000000000000 : ℝ) (25055966191/50000000000 : ℝ) (125279830957/250000000000 : ℝ) (250559661891/500000000000 : ℝ) (501119323791/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66779/524288 : ℝ))) 4 (25055966191/50000000000 : ℝ) (125279830957/250000000000 : ℝ) (250559661891/500000000000 : ℝ) (501119323791/1000000000000 : ℝ) (501119323801/1000000000000 : ℝ) (50111932381/100000000000 : ℝ) (2505596619/5000000000 : ℝ) (50111932381/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66779/524288 : ℝ))) 5 (501119323801/1000000000000 : ℝ) (50111932381/100000000000 : ℝ) (2505596619/5000000000 : ℝ) (50111932381/100000000000 : ℝ) (2505596619/5000000000 : ℝ) (50111932381/100000000000 : ℝ) (2505596619/5000000000 : ℝ) (50111932381/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66779/524288 : ℝ))) 6 (2505596619/5000000000 : ℝ) (50111932381/100000000000 : ℝ) (2505596619/5000000000 : ℝ) (50111932381/100000000000 : ℝ) (2505596619/5000000000 : ℝ) (50111932381/100000000000 : ℝ) (2505596619/5000000000 : ℝ) (50111932381/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66779/524288 : ℝ))) 7 (2505596619/5000000000 : ℝ) (50111932381/100000000000 : ℝ) (2505596619/5000000000 : ℝ) (50111932381/100000000000 : ℝ) (2505596619/5000000000 : ℝ) (50111932381/100000000000 : ℝ) (2505596619/5000000000 : ℝ) (50111932381/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66779/524288 : ℝ)) hmem 8 (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ) (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66779/524288 : ℝ))) hcmem 8 (2505596619/5000000000 : ℝ) (50111932381/100000000000 : ℝ) (2505596619/5000000000 : ℝ) (50111932381/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66779/524288 : ℝ)) (496043321311/500000000000 : ℝ) (7936693141/8000000000 : ℝ) (2505596619/5000000000 : ℝ) (50111932381/100000000000 : ℝ) (793435128839/1000000000000 : ℝ) (396717564429/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0706_exp_lower
  have heNumeric : (205490200209/100000000000 : ℝ)/4 ≤ Real.exp (-42628236918787/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490200209/100000000000 : ℝ)/4 ≤ Real.exp ((33389/262144 : ℝ)-(396717564429/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33389/262144 : ℝ) (66779/524288 : ℝ) (396717564429/500000000000 : ℝ) (205490200209/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0707; no trusted numerical premise.
theorem cover8_leaf0707_exp_radius : (998011780043982757/1000000000000000000 : ℝ) ≤ Real.exp ((-16695/1048576 : ℝ)/8) ∧ Real.exp ((-16695/1048576 : ℝ)/8) ≤ (499005890021991379/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16695/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0707_exp_lower : (230028368416658363/250000000000000000 : ℝ) ≤ Real.exp ((-85256474217397/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256474217397/128000000000000 : ℝ)/8) ≤ (920113473666633453/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256474217397/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0707_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862749499/125000000000 : ℝ) ≤ 4*Real.exp (66779/524288 : ℝ)*Real.exp (-mu (radius 8 (16695/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (256862749499/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16695/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0707_exp_radius
  have hrNumeric : (492102242917/500000000000 : ℝ) ≤ Real.exp (-16695/1048576 : ℝ) ∧ Real.exp (-16695/1048576 : ℝ) ≤ (196840897167/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492102242917/500000000000 : ℝ) ≤ (radius 8 (16695/131072 : ℝ)) ∧ (radius 8 (16695/131072 : ℝ)) ≤ (196840897167/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16695/131072 : ℝ)) (492102242917/500000000000 : ℝ) (196840897167/200000000000 : ℝ) (177035392117/1000000000000 : ℝ) (44258848031/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16695/131072 : ℝ)) (492102242917/500000000000 : ℝ) (196840897167/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16695/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492102242917/500000000000 : ℝ) (196840897167/200000000000 : ℝ) (992102242917/1000000000000 : ℝ) (496051121459/500000000000 : ℝ) (198414161373/200000000000 : ℝ) (496035403433/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16695/131072 : ℝ)) 1 (992102242917/1000000000000 : ℝ) (496051121459/500000000000 : ℝ) (198414161373/200000000000 : ℝ) (496035403433/500000000000 : ℝ) (992086524891/1000000000000 : ℝ) (248021631223/250000000000 : ℝ) (496043262383/500000000000 : ℝ) (31002703899/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16695/131072 : ℝ)) 2 (992086524891/1000000000000 : ℝ) (248021631223/250000000000 : ℝ) (496043262383/500000000000 : ℝ) (31002703899/31250000000 : ℝ) (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ) (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16695/131072 : ℝ)) 3 (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ) (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ) (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ) (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16695/131072 : ℝ)) 4 (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ) (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ) (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ) (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16695/131072 : ℝ)) 5 (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ) (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ) (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ) (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16695/131072 : ℝ)) 6 (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ) (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ) (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ) (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16695/131072 : ℝ)) 7 (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ) (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ) (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ) (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16695/131072 : ℝ))) (177035392117/1000000000000 : ℝ) (44258848031/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16695/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177035392117/1000000000000 : ℝ) (44258848031/250000000000 : ℝ) (294258848029/500000000000 : ℝ) (294258848031/500000000000 : ℝ) (52594467407/125000000000 : ℝ) (84151147853/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16695/131072 : ℝ))) 1 (294258848029/500000000000 : ℝ) (294258848031/500000000000 : ℝ) (52594467407/125000000000 : ℝ) (84151147853/200000000000 : ℝ) (504636717657/1000000000000 : ℝ) (15769897427/31250000000 : ℝ) (3110103233/6250000000 : ℝ) (62202064661/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16695/131072 : ℝ))) 2 (504636717657/1000000000000 : ℝ) (15769897427/31250000000 : ℝ) (3110103233/6250000000 : ℝ) (62202064661/125000000000 : ℝ) (125281654367/250000000000 : ℝ) (125281654369/250000000000 : ℝ) (501114324213/1000000000000 : ℝ) (250557162111/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16695/131072 : ℝ))) 3 (125281654367/250000000000 : ℝ) (125281654369/250000000000 : ℝ) (501114324213/1000000000000 : ℝ) (250557162111/500000000000 : ℝ) (12528011771/25000000000 : ℝ) (501120470849/1000000000000 : ℝ) (250560235401/500000000000 : ℝ) (125280117703/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16695/131072 : ℝ))) 4 (12528011771/25000000000 : ℝ) (501120470849/1000000000000 : ℝ) (250560235401/500000000000 : ℝ) (125280117703/250000000000 : ℝ) (501120470821/1000000000000 : ℝ) (501120470831/1000000000000 : ℝ) (25056023541/50000000000 : ℝ) (501120470831/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16695/131072 : ℝ))) 5 (501120470821/1000000000000 : ℝ) (501120470831/1000000000000 : ℝ) (25056023541/50000000000 : ℝ) (501120470831/1000000000000 : ℝ) (25056023541/50000000000 : ℝ) (501120470831/1000000000000 : ℝ) (25056023541/50000000000 : ℝ) (501120470831/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16695/131072 : ℝ))) 6 (25056023541/50000000000 : ℝ) (501120470831/1000000000000 : ℝ) (25056023541/50000000000 : ℝ) (501120470831/1000000000000 : ℝ) (25056023541/50000000000 : ℝ) (501120470831/1000000000000 : ℝ) (25056023541/50000000000 : ℝ) (501120470831/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16695/131072 : ℝ))) 7 (25056023541/50000000000 : ℝ) (501120470831/1000000000000 : ℝ) (25056023541/50000000000 : ℝ) (501120470831/1000000000000 : ℝ) (25056023541/50000000000 : ℝ) (501120470831/1000000000000 : ℝ) (25056023541/50000000000 : ℝ) (501120470831/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16695/131072 : ℝ)) hmem 8 (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ) (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16695/131072 : ℝ))) hcmem 8 (25056023541/50000000000 : ℝ) (501120470831/1000000000000 : ℝ) (25056023541/50000000000 : ℝ) (501120470831/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16695/131072 : ℝ)) (248021631207/250000000000 : ℝ) (99208652483/100000000000 : ℝ) (25056023541/50000000000 : ℝ) (501120470831/1000000000000 : ℝ) (396718519577/500000000000 : ℝ) (396718519587/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0707_exp_lower
  have heNumeric : (256862749499/125000000000 : ℝ)/4 ≤ Real.exp (-85256474217397/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862749499/125000000000 : ℝ)/4 ≤ Real.exp ((66779/524288 : ℝ)-(396718519587/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66779/524288 : ℝ) (16695/131072 : ℝ) (396718519587/500000000000 : ℝ) (256862749499/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0708; no trusted numerical premise.
theorem cover8_leaf0708_exp_radius : (62375734393807149/62500000000000000 : ℝ) ≤ Real.exp ((-66781/4194304 : ℝ)/8) ∧ Real.exp ((-66781/4194304 : ℝ)/8) ≤ (199602350060182877/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66781/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0708_exp_lower : (460056736663362153/500000000000000000 : ℝ) ≤ Real.exp ((-21314118648921/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314118648921/32000000000000 : ℝ)/8) ≤ (920113473326724307/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314118648921/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0708_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901989919/1000000000000 : ℝ) ≤ 4*Real.exp (16695/131072 : ℝ)*Real.exp (-mu (radius 8 (66781/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901989919/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66781/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0708_exp_radius
  have hrNumeric : (984204251181/1000000000000 : ℝ) ≤ Real.exp (-66781/4194304 : ℝ) ∧ Real.exp (-66781/4194304 : ℝ) ≤ (492102125591/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984204251181/1000000000000 : ℝ) ≤ (radius 8 (66781/524288 : ℝ)) ∧ (radius 8 (66781/524288 : ℝ)) ≤ (492102125591/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66781/524288 : ℝ)) (984204251181/1000000000000 : ℝ) (492102125591/500000000000 : ℝ) (88518348317/500000000000 : ℝ) (177036696641/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66781/524288 : ℝ)) (984204251181/1000000000000 : ℝ) (492102125591/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66781/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984204251181/1000000000000 : ℝ) (492102125591/500000000000 : ℝ) (99210212559/100000000000 : ℝ) (992102125591/1000000000000 : ℝ) (4960353443/5000000000 : ℝ) (496035344301/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66781/524288 : ℝ)) 1 (99210212559/100000000000 : ℝ) (992102125591/1000000000000 : ℝ) (4960353443/5000000000 : ℝ) (496035344301/500000000000 : ℝ) (198417281419/200000000000 : ℝ) (992086407097/1000000000000 : ℝ) (99208640697/100000000000 : ℝ) (248021601743/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66781/524288 : ℝ)) 2 (198417281419/200000000000 : ℝ) (992086407097/1000000000000 : ℝ) (99208640697/100000000000 : ℝ) (248021601743/250000000000 : ℝ) (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ) (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66781/524288 : ℝ)) 3 (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ) (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ) (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ) (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66781/524288 : ℝ)) 4 (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ) (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ) (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ) (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66781/524288 : ℝ)) 5 (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ) (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ) (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ) (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66781/524288 : ℝ)) 6 (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ) (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ) (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ) (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66781/524288 : ℝ)) 7 (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ) (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ) (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ) (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66781/524288 : ℝ))) (88518348317/500000000000 : ℝ) (177036696641/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66781/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88518348317/500000000000 : ℝ) (177036696641/1000000000000 : ℝ) (588518348317/1000000000000 : ℝ) (588518348321/1000000000000 : ℝ) (21037864473/50000000000 : ℝ) (420757289469/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66781/524288 : ℝ))) 1 (588518348317/1000000000000 : ℝ) (588518348321/1000000000000 : ℝ) (21037864473/50000000000 : ℝ) (420757289469/1000000000000 : ℝ) (63079727361/125000000000 : ℝ) (100927563779/200000000000 : ℝ) (15550553429/31250000000 : ℝ) (62202213717/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66781/524288 : ℝ))) 2 (63079727361/125000000000 : ℝ) (100927563779/200000000000 : ℝ) (15550553429/31250000000 : ℝ) (62202213717/125000000000 : ℝ) (125281941077/250000000000 : ℝ) (125281941079/250000000000 : ℝ) (2505577357/5000000000 : ℝ) (501115471409/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66781/524288 : ℝ))) 3 (125281941077/250000000000 : ℝ) (125281941079/250000000000 : ℝ) (2505577357/5000000000 : ℝ) (501115471409/1000000000000 : ℝ) (250560808927/500000000000 : ℝ) (501121617863/1000000000000 : ℝ) (62640202227/125000000000 : ℝ) (20044864713/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66781/524288 : ℝ))) 4 (250560808927/500000000000 : ℝ) (501121617863/1000000000000 : ℝ) (62640202227/125000000000 : ℝ) (20044864713/40000000000 : ℝ) (100224323567/200000000000 : ℝ) (125280404461/250000000000 : ℝ) (250560808917/500000000000 : ℝ) (125280404461/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66781/524288 : ℝ))) 5 (100224323567/200000000000 : ℝ) (125280404461/250000000000 : ℝ) (250560808917/500000000000 : ℝ) (125280404461/250000000000 : ℝ) (250560808917/500000000000 : ℝ) (125280404461/250000000000 : ℝ) (250560808917/500000000000 : ℝ) (125280404461/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66781/524288 : ℝ))) 6 (250560808917/500000000000 : ℝ) (125280404461/250000000000 : ℝ) (250560808917/500000000000 : ℝ) (125280404461/250000000000 : ℝ) (250560808917/500000000000 : ℝ) (125280404461/250000000000 : ℝ) (250560808917/500000000000 : ℝ) (125280404461/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66781/524288 : ℝ))) 7 (250560808917/500000000000 : ℝ) (125280404461/250000000000 : ℝ) (250560808917/500000000000 : ℝ) (125280404461/250000000000 : ℝ) (250560808917/500000000000 : ℝ) (125280404461/250000000000 : ℝ) (250560808917/500000000000 : ℝ) (125280404461/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66781/524288 : ℝ)) hmem 8 (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ) (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66781/524288 : ℝ))) hcmem 8 (250560808917/500000000000 : ℝ) (125280404461/250000000000 : ℝ) (250560808917/500000000000 : ℝ) (125280404461/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66781/524288 : ℝ)) (124010800879/125000000000 : ℝ) (198417281407/200000000000 : ℝ) (250560808917/500000000000 : ℝ) (125280404461/250000000000 : ℝ) (793438949459/1000000000000 : ℝ) (396719474739/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0708_exp_lower
  have heNumeric : (2054901989919/1000000000000 : ℝ)/4 ≤ Real.exp (-21314118648921/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901989919/1000000000000 : ℝ)/4 ≤ Real.exp ((16695/131072 : ℝ)-(396719474739/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16695/131072 : ℝ) (66781/524288 : ℝ) (396719474739/500000000000 : ℝ) (2054901989919/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0709; no trusted numerical premise.
theorem cover8_leaf0709_exp_radius : (998011720557846899/1000000000000000000 : ℝ) ≤ Real.exp ((-33391/2097152 : ℝ)/8) ∧ Real.exp ((-33391/2097152 : ℝ)/8) ≤ (9980117205578469/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33391/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0709_exp_lower : (920113472989805529/1000000000000000000 : ℝ) ≤ Real.exp ((-85256474970643/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256474970643/128000000000000 : ℝ)/8) ≤ (92011347298980553/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256474970643/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0709_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (20549019839/10000000000 : ℝ) ≤ 4*Real.exp (66781/524288 : ℝ)*Real.exp (-mu (radius 8 (33391/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (20549019839/10000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33391/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0709_exp_radius
  have hrNumeric : (984204016529/1000000000000 : ℝ) ≤ Real.exp (-33391/2097152 : ℝ) ∧ Real.exp (-33391/2097152 : ℝ) ≤ (98420401653/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984204016529/1000000000000 : ℝ) ≤ (radius 8 (33391/262144 : ℝ)) ∧ (radius 8 (33391/262144 : ℝ)) ≤ (98420401653/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33391/262144 : ℝ)) (984204016529/1000000000000 : ℝ) (98420401653/100000000000 : ℝ) (35407600227/200000000000 : ℝ) (88519000571/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33391/262144 : ℝ)) (984204016529/1000000000000 : ℝ) (98420401653/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33391/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984204016529/1000000000000 : ℝ) (98420401653/100000000000 : ℝ) (124012751033/125000000000 : ℝ) (198420401653/200000000000 : ℝ) (992070570337/1000000000000 : ℝ) (496035285169/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33391/262144 : ℝ)) 1 (124012751033/125000000000 : ℝ) (198420401653/200000000000 : ℝ) (992070570337/1000000000000 : ℝ) (496035285169/500000000000 : ℝ) (9920862893/10000000000 : ℝ) (496043144651/500000000000 : ℝ) (39683451567/40000000000 : ℝ) (992086289177/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33391/262144 : ℝ)) 2 (9920862893/10000000000 : ℝ) (496043144651/500000000000 : ℝ) (39683451567/40000000000 : ℝ) (992086289177/1000000000000 : ℝ) (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ) (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33391/262144 : ℝ)) 3 (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ) (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ) (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ) (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33391/262144 : ℝ)) 4 (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ) (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ) (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ) (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33391/262144 : ℝ)) 5 (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ) (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ) (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ) (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33391/262144 : ℝ)) 6 (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ) (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ) (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ) (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33391/262144 : ℝ)) 7 (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ) (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ) (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ) (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33391/262144 : ℝ))) (35407600227/200000000000 : ℝ) (88519000571/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33391/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35407600227/200000000000 : ℝ) (88519000571/500000000000 : ℝ) (588519000567/1000000000000 : ℝ) (588519000571/1000000000000 : ℝ) (420758839639/1000000000000 : ℝ) (420758839649/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33391/262144 : ℝ))) 1 (588519000567/1000000000000 : ℝ) (588519000571/1000000000000 : ℝ) (420758839639/1000000000000 : ℝ) (420758839649/1000000000000 : ℝ) (504638920103/1000000000000 : ℝ) (50463892011/100000000000 : ℝ) (497618902157/1000000000000 : ℝ) (99523780433/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33391/262144 : ℝ))) 2 (504638920103/1000000000000 : ℝ) (50463892011/100000000000 : ℝ) (497618902157/1000000000000 : ℝ) (99523780433/200000000000 : ℝ) (50112891113/100000000000 : ℝ) (250564455569/500000000000 : ℝ) (50111661857/100000000000 : ℝ) (250558309289/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33391/262144 : ℝ))) 3 (50112891113/100000000000 : ℝ) (250564455569/500000000000 : ℝ) (50111661857/100000000000 : ℝ) (250558309289/500000000000 : ℝ) (10022455297/20000000000 : ℝ) (250561382429/500000000000 : ℝ) (125280691203/250000000000 : ℝ) (501122764821/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33391/262144 : ℝ))) 4 (10022455297/20000000000 : ℝ) (250561382429/500000000000 : ℝ) (125280691203/250000000000 : ℝ) (501122764821/1000000000000 : ℝ) (501122764831/1000000000000 : ℝ) (12528069121/25000000000 : ℝ) (50112276483/100000000000 : ℝ) (12528069121/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33391/262144 : ℝ))) 5 (501122764831/1000000000000 : ℝ) (12528069121/25000000000 : ℝ) (50112276483/100000000000 : ℝ) (12528069121/25000000000 : ℝ) (50112276483/100000000000 : ℝ) (12528069121/25000000000 : ℝ) (50112276483/100000000000 : ℝ) (12528069121/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33391/262144 : ℝ))) 6 (50112276483/100000000000 : ℝ) (12528069121/25000000000 : ℝ) (50112276483/100000000000 : ℝ) (12528069121/25000000000 : ℝ) (50112276483/100000000000 : ℝ) (12528069121/25000000000 : ℝ) (50112276483/100000000000 : ℝ) (12528069121/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33391/262144 : ℝ))) 7 (50112276483/100000000000 : ℝ) (12528069121/25000000000 : ℝ) (50112276483/100000000000 : ℝ) (12528069121/25000000000 : ℝ) (50112276483/100000000000 : ℝ) (12528069121/25000000000 : ℝ) (50112276483/100000000000 : ℝ) (12528069121/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33391/262144 : ℝ)) hmem 8 (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ) (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33391/262144 : ℝ))) hcmem 8 (50112276483/100000000000 : ℝ) (12528069121/25000000000 : ℝ) (50112276483/100000000000 : ℝ) (12528069121/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33391/262144 : ℝ)) (992086289237/1000000000000 : ℝ) (24802157231/25000000000 : ℝ) (50112276483/100000000000 : ℝ) (12528069121/25000000000 : ℝ) (793440859737/1000000000000 : ℝ) (198360214939/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0709_exp_lower
  have heNumeric : (20549019839/10000000000 : ℝ)/4 ≤ Real.exp (-85256474970643/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (20549019839/10000000000 : ℝ)/4 ≤ Real.exp ((66781/524288 : ℝ)-(198360214939/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66781/524288 : ℝ) (33391/262144 : ℝ) (198360214939/250000000000 : ℝ) (20549019839/10000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0710; no trusted numerical premise.
theorem cover8_leaf0710_exp_radius : (998011690814780299/1000000000000000000 : ℝ) ≤ Real.exp ((-66783/4194304 : ℝ)/8) ∧ Real.exp ((-66783/4194304 : ℝ)/8) ≤ (9980116908147803/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66783/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0710_exp_lower : (230028368163537977/250000000000000000 : ℝ) ≤ Real.exp ((-42628237672097/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628237672097/64000000000000 : ℝ)/8) ≤ (920113472654151909/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628237672097/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0710_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901977903/1000000000000 : ℝ) ≤ 4*Real.exp (33391/262144 : ℝ)*Real.exp (-mu (radius 8 (66783/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901977903/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66783/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0710_exp_radius
  have hrNumeric : (246050945469/250000000000 : ℝ) ≤ Real.exp (-66783/4194304 : ℝ) ∧ Real.exp (-66783/4194304 : ℝ) ≤ (984203781877/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246050945469/250000000000 : ℝ) ≤ (radius 8 (66783/524288 : ℝ)) ∧ (radius 8 (66783/524288 : ℝ)) ≤ (984203781877/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66783/524288 : ℝ)) (246050945469/250000000000 : ℝ) (984203781877/1000000000000 : ℝ) (5532478301/31250000000 : ℝ) (177039305639/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66783/524288 : ℝ)) (246050945469/250000000000 : ℝ) (984203781877/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66783/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246050945469/250000000000 : ℝ) (984203781877/1000000000000 : ℝ) (496050945469/500000000000 : ℝ) (992101890939/1000000000000 : ℝ) (124008806509/125000000000 : ℝ) (496035226037/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66783/524288 : ℝ)) 1 (496050945469/500000000000 : ℝ) (992101890939/1000000000000 : ℝ) (124008806509/125000000000 : ℝ) (496035226037/500000000000 : ℝ) (198417234301/200000000000 : ℝ) (992086171507/1000000000000 : ℝ) (49604308569/50000000000 : ℝ) (496043085691/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66783/524288 : ℝ)) 2 (198417234301/200000000000 : ℝ) (992086171507/1000000000000 : ℝ) (49604308569/50000000000 : ℝ) (496043085691/500000000000 : ℝ) (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ) (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66783/524288 : ℝ)) 3 (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ) (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ) (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ) (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66783/524288 : ℝ)) 4 (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ) (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ) (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ) (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66783/524288 : ℝ)) 5 (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ) (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ) (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ) (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66783/524288 : ℝ)) 6 (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ) (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ) (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ) (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66783/524288 : ℝ)) 7 (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ) (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ) (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ) (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66783/524288 : ℝ))) (5532478301/31250000000 : ℝ) (177039305639/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66783/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5532478301/31250000000 : ℝ) (177039305639/1000000000000 : ℝ) (36782478301/62500000000 : ℝ) (29425982641/50000000000 : ℝ) (26297524363/62500000000 : ℝ) (210380194909/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66783/524288 : ℝ))) 1 (36782478301/62500000000 : ℝ) (29425982641/50000000000 : ℝ) (26297524363/62500000000 : ℝ) (210380194909/500000000000 : ℝ) (7885000333/15625000000 : ℝ) (504640021319/1000000000000 : ℝ) (248810047289/500000000000 : ℝ) (497620094587/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66783/524288 : ℝ))) 2 (7885000333/15625000000 : ℝ) (504640021319/1000000000000 : ℝ) (248810047289/500000000000 : ℝ) (497620094587/1000000000000 : ℝ) (100226011589/200000000000 : ℝ) (501130057953/1000000000000 : ℝ) (125279441433/250000000000 : ℝ) (501117765741/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66783/524288 : ℝ))) 3 (100226011589/200000000000 : ℝ) (501130057953/1000000000000 : ℝ) (125279441433/250000000000 : ℝ) (501117765741/1000000000000 : ℝ) (250561955919/500000000000 : ℝ) (501123911847/1000000000000 : ℝ) (2505619559/5000000000 : ℝ) (50112391181/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66783/524288 : ℝ))) 4 (250561955919/500000000000 : ℝ) (501123911847/1000000000000 : ℝ) (2505619559/5000000000 : ℝ) (50112391181/100000000000 : ℝ) (501123911819/1000000000000 : ℝ) (501123911829/1000000000000 : ℝ) (250561955909/500000000000 : ℝ) (501123911829/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66783/524288 : ℝ))) 5 (501123911819/1000000000000 : ℝ) (501123911829/1000000000000 : ℝ) (250561955909/500000000000 : ℝ) (501123911829/1000000000000 : ℝ) (250561955909/500000000000 : ℝ) (501123911829/1000000000000 : ℝ) (250561955909/500000000000 : ℝ) (501123911829/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66783/524288 : ℝ))) 6 (250561955909/500000000000 : ℝ) (501123911829/1000000000000 : ℝ) (250561955909/500000000000 : ℝ) (501123911829/1000000000000 : ℝ) (250561955909/500000000000 : ℝ) (501123911829/1000000000000 : ℝ) (250561955909/500000000000 : ℝ) (501123911829/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66783/524288 : ℝ))) 7 (250561955909/500000000000 : ℝ) (501123911829/1000000000000 : ℝ) (250561955909/500000000000 : ℝ) (501123911829/1000000000000 : ℝ) (250561955909/500000000000 : ℝ) (501123911829/1000000000000 : ℝ) (250561955909/500000000000 : ℝ) (501123911829/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66783/524288 : ℝ)) hmem 8 (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ) (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66783/524288 : ℝ))) hcmem 8 (250561955909/500000000000 : ℝ) (501123911829/1000000000000 : ℝ) (250561955909/500000000000 : ℝ) (501123911829/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66783/524288 : ℝ)) (496043085721/500000000000 : ℝ) (198417234289/200000000000 : ℝ) (250561955909/500000000000 : ℝ) (501123911829/1000000000000 : ℝ) (396721385001/500000000000 : ℝ) (793442770023/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0710_exp_lower
  have heNumeric : (2054901977903/1000000000000 : ℝ)/4 ≤ Real.exp (-42628237672097/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901977903/1000000000000 : ℝ)/4 ≤ Real.exp ((33391/262144 : ℝ)-(793442770023/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33391/262144 : ℝ) (66783/524288 : ℝ) (793442770023/1000000000000 : ℝ) (2054901977903/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0711; no trusted numerical premise.
theorem cover8_leaf0711_exp_radius : (499005830535857293/500000000000000000 : ℝ) ≤ Real.exp ((-2087/131072 : ℝ)/8) ∧ Real.exp ((-2087/131072 : ℝ)/8) ≤ (998011661071714587/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2087/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0711_exp_lower : (184022694464297731/200000000000000000 : ℝ) ≤ Real.exp ((-85256475714417/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256475714417/128000000000000 : ℝ)/8) ≤ (57507092020093041/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256475714417/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0711_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901971959/1000000000000 : ℝ) ≤ 4*Real.exp (66783/524288 : ℝ)*Real.exp (-mu (radius 8 (2087/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901971959/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2087/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0711_exp_radius
  have hrNumeric : (123025443403/125000000000 : ℝ) ≤ Real.exp (-2087/131072 : ℝ) ∧ Real.exp (-2087/131072 : ℝ) ≤ (39368141889/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123025443403/125000000000 : ℝ) ≤ (radius 8 (2087/16384 : ℝ)) ∧ (radius 8 (2087/16384 : ℝ)) ≤ (39368141889/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2087/16384 : ℝ)) (123025443403/125000000000 : ℝ) (39368141889/40000000000 : ℝ) (88520305057/500000000000 : ℝ) (177040610121/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2087/16384 : ℝ)) (123025443403/125000000000 : ℝ) (39368141889/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2087/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123025443403/125000000000 : ℝ) (39368141889/40000000000 : ℝ) (248025443403/250000000000 : ℝ) (992101773613/1000000000000 : ℝ) (992070333809/1000000000000 : ℝ) (99207033381/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2087/16384 : ℝ)) 1 (248025443403/250000000000 : ℝ) (992101773613/1000000000000 : ℝ) (992070333809/1000000000000 : ℝ) (99207033381/100000000000 : ℝ) (99208605371/100000000000 : ℝ) (62005378357/62500000000 : ℝ) (198417210717/200000000000 : ℝ) (992086053587/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2087/16384 : ℝ)) 2 (99208605371/100000000000 : ℝ) (62005378357/62500000000 : ℝ) (198417210717/200000000000 : ℝ) (992086053587/1000000000000 : ℝ) (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ) (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2087/16384 : ℝ)) 3 (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ) (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ) (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ) (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2087/16384 : ℝ)) 4 (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ) (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ) (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ) (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2087/16384 : ℝ)) 5 (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ) (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ) (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ) (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2087/16384 : ℝ)) 6 (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ) (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ) (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ) (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2087/16384 : ℝ)) 7 (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ) (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ) (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ) (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2087/16384 : ℝ))) (88520305057/500000000000 : ℝ) (177040610121/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2087/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88520305057/500000000000 : ℝ) (177040610121/1000000000000 : ℝ) (588520305057/1000000000000 : ℝ) (588520305061/1000000000000 : ℝ) (210380969977/500000000000 : ℝ) (420761939963/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2087/16384 : ℝ))) 1 (588520305057/1000000000000 : ℝ) (588520305061/1000000000000 : ℝ) (210380969977/500000000000 : ℝ) (420761939963/1000000000000 : ℝ) (100928224501/200000000000 : ℝ) (31540070157/62500000000 : ℝ) (248810643491/500000000000 : ℝ) (49762128699/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2087/16384 : ℝ))) 2 (100928224501/200000000000 : ℝ) (31540070157/62500000000 : ℝ) (248810643491/500000000000 : ℝ) (49762128699/100000000000 : ℝ) (501131204743/1000000000000 : ℝ) (501131204751/1000000000000 : ℝ) (250559456439/500000000000 : ℝ) (501118912887/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2087/16384 : ℝ))) 3 (501131204743/1000000000000 : ℝ) (501131204751/1000000000000 : ℝ) (250559456439/500000000000 : ℝ) (501118912887/1000000000000 : ℝ) (50112505881/100000000000 : ℝ) (501125058819/1000000000000 : ℝ) (125281264693/250000000000 : ℝ) (250562529391/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2087/16384 : ℝ))) 4 (50112505881/100000000000 : ℝ) (501125058819/1000000000000 : ℝ) (125281264693/250000000000 : ℝ) (250562529391/500000000000 : ℝ) (501125058791/1000000000000 : ℝ) (501125058801/1000000000000 : ℝ) (50112505879/100000000000 : ℝ) (501125058801/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2087/16384 : ℝ))) 5 (501125058791/1000000000000 : ℝ) (501125058801/1000000000000 : ℝ) (50112505879/100000000000 : ℝ) (501125058801/1000000000000 : ℝ) (50112505879/100000000000 : ℝ) (501125058801/1000000000000 : ℝ) (50112505879/100000000000 : ℝ) (501125058801/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2087/16384 : ℝ))) 6 (50112505879/100000000000 : ℝ) (501125058801/1000000000000 : ℝ) (50112505879/100000000000 : ℝ) (501125058801/1000000000000 : ℝ) (50112505879/100000000000 : ℝ) (501125058801/1000000000000 : ℝ) (50112505879/100000000000 : ℝ) (501125058801/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2087/16384 : ℝ))) 7 (50112505879/100000000000 : ℝ) (501125058801/1000000000000 : ℝ) (50112505879/100000000000 : ℝ) (501125058801/1000000000000 : ℝ) (50112505879/100000000000 : ℝ) (501125058801/1000000000000 : ℝ) (50112505879/100000000000 : ℝ) (501125058801/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2087/16384 : ℝ)) hmem 8 (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ) (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2087/16384 : ℝ))) hcmem 8 (50112505879/100000000000 : ℝ) (501125058801/1000000000000 : ℝ) (50112505879/100000000000 : ℝ) (501125058801/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2087/16384 : ℝ)) (992086053647/1000000000000 : ℝ) (19841721073/20000000000 : ℝ) (50112505879/100000000000 : ℝ) (501125058801/1000000000000 : ℝ) (793444680243/1000000000000 : ℝ) (99180585033/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0711_exp_lower
  have heNumeric : (2054901971959/1000000000000 : ℝ)/4 ≤ Real.exp (-85256475714417/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901971959/1000000000000 : ℝ)/4 ≤ Real.exp ((66783/524288 : ℝ)-(99180585033/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66783/524288 : ℝ) (2087/16384 : ℝ) (99180585033/125000000000 : ℝ) (2054901971959/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0712; no trusted numerical premise.
theorem cover8_leaf0712_exp_radius : (998011631328649759/1000000000000000000 : ℝ) ≤ Real.exp ((-66785/4194304 : ℝ)/8) ∧ Real.exp ((-66785/4194304 : ℝ)/8) ≤ (6237572695804061/6250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66785/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0712_exp_lower : (460056735995102787/500000000000000000 : ℝ) ≤ Real.exp ((-2664264877597/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664264877597/4000000000000 : ℝ)/8) ≤ (36804538879608223/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664264877597/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0712_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (51372549151/25000000000 : ℝ) ≤ 4*Real.exp (2087/16384 : ℝ)*Real.exp (-mu (radius 8 (66785/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (51372549151/25000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66785/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0712_exp_radius
  have hrNumeric : (984203312571/1000000000000 : ℝ) ≤ Real.exp (-66785/4194304 : ℝ) ∧ Real.exp (-66785/4194304 : ℝ) ≤ (246050828143/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984203312571/1000000000000 : ℝ) ≤ (radius 8 (66785/524288 : ℝ)) ∧ (radius 8 (66785/524288 : ℝ)) ≤ (246050828143/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66785/524288 : ℝ)) (984203312571/1000000000000 : ℝ) (246050828143/250000000000 : ℝ) (177041914591/1000000000000 : ℝ) (88520957299/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66785/524288 : ℝ)) (984203312571/1000000000000 : ℝ) (246050828143/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66785/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984203312571/1000000000000 : ℝ) (246050828143/250000000000 : ℝ) (198420331257/200000000000 : ℝ) (496050828143/500000000000 : ℝ) (124008776943/125000000000 : ℝ) (496035107773/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66785/524288 : ℝ)) 1 (198420331257/200000000000 : ℝ) (496050828143/500000000000 : ℝ) (124008776943/125000000000 : ℝ) (496035107773/500000000000 : ℝ) (496042967957/500000000000 : ℝ) (248021483979/250000000000 : ℝ) (992085935789/1000000000000 : ℝ) (62005370987/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66785/524288 : ℝ)) 2 (496042967957/500000000000 : ℝ) (248021483979/250000000000 : ℝ) (992085935789/1000000000000 : ℝ) (62005370987/62500000000 : ℝ) (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ) (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66785/524288 : ℝ)) 3 (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ) (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ) (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ) (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66785/524288 : ℝ)) 4 (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ) (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ) (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ) (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66785/524288 : ℝ)) 5 (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ) (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ) (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ) (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66785/524288 : ℝ)) 6 (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ) (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ) (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ) (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66785/524288 : ℝ)) 7 (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ) (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ) (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ) (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66785/524288 : ℝ))) (177041914591/1000000000000 : ℝ) (88520957299/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66785/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177041914591/1000000000000 : ℝ) (88520957299/500000000000 : ℝ) (117704191459/200000000000 : ℝ) (588520957299/1000000000000 : ℝ) (420763490087/1000000000000 : ℝ) (420763490097/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66785/524288 : ℝ))) 1 (117704191459/200000000000 : ℝ) (588520957299/1000000000000 : ℝ) (420763490087/1000000000000 : ℝ) (420763490097/1000000000000 : ℝ) (504642223691/1000000000000 : ℝ) (252321111849/500000000000 : ℝ) (31101404961/62500000000 : ℝ) (99524495877/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66785/524288 : ℝ))) 2 (504642223691/1000000000000 : ℝ) (252321111849/500000000000 : ℝ) (31101404961/62500000000 : ℝ) (99524495877/200000000000 : ℝ) (501132351533/1000000000000 : ℝ) (250566175771/500000000000 : ℝ) (31320003751/62500000000 : ℝ) (20044802401/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66785/524288 : ℝ))) 3 (501132351533/1000000000000 : ℝ) (250566175771/500000000000 : ℝ) (31320003751/62500000000 : ℝ) (20044802401/40000000000 : ℝ) (250563102887/500000000000 : ℝ) (62640775723/125000000000 : ℝ) (62640775717/125000000000 : ℝ) (250563102873/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66785/524288 : ℝ))) 4 (250563102887/500000000000 : ℝ) (62640775723/125000000000 : ℝ) (62640775717/125000000000 : ℝ) (250563102873/500000000000 : ℝ) (100225241151/200000000000 : ℝ) (100225241153/200000000000 : ℝ) (250563102877/500000000000 : ℝ) (100225241153/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66785/524288 : ℝ))) 5 (100225241151/200000000000 : ℝ) (100225241153/200000000000 : ℝ) (250563102877/500000000000 : ℝ) (100225241153/200000000000 : ℝ) (250563102877/500000000000 : ℝ) (100225241153/200000000000 : ℝ) (250563102877/500000000000 : ℝ) (100225241153/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66785/524288 : ℝ))) 6 (250563102877/500000000000 : ℝ) (100225241153/200000000000 : ℝ) (250563102877/500000000000 : ℝ) (100225241153/200000000000 : ℝ) (250563102877/500000000000 : ℝ) (100225241153/200000000000 : ℝ) (250563102877/500000000000 : ℝ) (100225241153/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66785/524288 : ℝ))) 7 (250563102877/500000000000 : ℝ) (100225241153/200000000000 : ℝ) (250563102877/500000000000 : ℝ) (100225241153/200000000000 : ℝ) (250563102877/500000000000 : ℝ) (100225241153/200000000000 : ℝ) (250563102877/500000000000 : ℝ) (100225241153/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66785/524288 : ℝ)) hmem 8 (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ) (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66785/524288 : ℝ))) hcmem 8 (250563102877/500000000000 : ℝ) (100225241153/200000000000 : ℝ) (250563102877/500000000000 : ℝ) (100225241153/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66785/524288 : ℝ)) (992085935851/1000000000000 : ℝ) (496042967927/500000000000 : ℝ) (250563102877/500000000000 : ℝ) (100225241153/200000000000 : ℝ) (99180823809/125000000000 : ℝ) (793446590493/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0712_exp_lower
  have heNumeric : (51372549151/25000000000 : ℝ)/4 ≤ Real.exp (-2664264877597/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (51372549151/25000000000 : ℝ)/4 ≤ Real.exp ((2087/16384 : ℝ)-(793446590493/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2087/16384 : ℝ) (66785/524288 : ℝ) (793446590493/1000000000000 : ℝ) (51372549151/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0713; no trusted numerical premise.
theorem cover8_leaf0713_exp_radius : (998011601585585819/1000000000000000000 : ℝ) ≤ Real.exp ((-33393/2097152 : ℝ)/8) ∧ Real.exp ((-33393/2097152 : ℝ)/8) ≤ (49900580079279291/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33393/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0713_exp_lower : (7360907773296223/8000000000000000 : ℝ) ≤ Real.exp ((-17051295289667/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051295289667/25600000000000 : ℝ)/8) ≤ (230028367915506969/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051295289667/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0713_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901960177/1000000000000 : ℝ) ≤ 4*Real.exp (66785/524288 : ℝ)*Real.exp (-mu (radius 8 (33393/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901960177/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33393/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0713_exp_radius
  have hrNumeric : (984203077919/1000000000000 : ℝ) ≤ Real.exp (-33393/2097152 : ℝ) ∧ Real.exp (-33393/2097152 : ℝ) ≤ (6151269237/6250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984203077919/1000000000000 : ℝ) ≤ (radius 8 (33393/262144 : ℝ)) ∧ (radius 8 (33393/262144 : ℝ)) ≤ (6151269237/6250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33393/262144 : ℝ)) (984203077919/1000000000000 : ℝ) (6151269237/6250000000 : ℝ) (177043219053/1000000000000 : ℝ) (177043219059/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33393/262144 : ℝ)) (984203077919/1000000000000 : ℝ) (6151269237/6250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33393/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984203077919/1000000000000 : ℝ) (6151269237/6250000000 : ℝ) (992101538959/1000000000000 : ℝ) (12401269237/12500000000 : ℝ) (1550109527/1562500000 : ℝ) (496035048641/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33393/262144 : ℝ)) 1 (992101538959/1000000000000 : ℝ) (12401269237/12500000000 : ℝ) (1550109527/1562500000 : ℝ) (496035048641/500000000000 : ℝ) (992085818119/1000000000000 : ℝ) (992085818121/1000000000000 : ℝ) (496042908997/500000000000 : ℝ) (992085817997/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33393/262144 : ℝ)) 2 (992085818119/1000000000000 : ℝ) (992085818121/1000000000000 : ℝ) (496042908997/500000000000 : ℝ) (992085817997/1000000000000 : ℝ) (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ) (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33393/262144 : ℝ)) 3 (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ) (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ) (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ) (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33393/262144 : ℝ)) 4 (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ) (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ) (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ) (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33393/262144 : ℝ)) 5 (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ) (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ) (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ) (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33393/262144 : ℝ)) 6 (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ) (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ) (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ) (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33393/262144 : ℝ)) 7 (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ) (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ) (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ) (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33393/262144 : ℝ))) (177043219053/1000000000000 : ℝ) (177043219059/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33393/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177043219053/1000000000000 : ℝ) (177043219059/1000000000000 : ℝ) (294260804763/500000000000 : ℝ) (58852160953/100000000000 : ℝ) (210382520099/500000000000 : ℝ) (210382520103/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33393/262144 : ℝ))) 1 (294260804763/500000000000 : ℝ) (58852160953/100000000000 : ℝ) (210382520099/500000000000 : ℝ) (210382520103/500000000000 : ℝ) (252321662431/500000000000 : ℝ) (126160831217/250000000000 : ℝ) (497623671753/1000000000000 : ℝ) (497623671761/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33393/262144 : ℝ))) 2 (252321662431/500000000000 : ℝ) (126160831217/250000000000 : ℝ) (497623671753/1000000000000 : ℝ) (497623671761/1000000000000 : ℝ) (501133498307/1000000000000 : ℝ) (100226699663/200000000000 : ℝ) (250560603569/500000000000 : ℝ) (250560603573/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33393/262144 : ℝ))) 3 (501133498307/1000000000000 : ℝ) (100226699663/200000000000 : ℝ) (250560603569/500000000000 : ℝ) (250560603573/500000000000 : ℝ) (250563676361/500000000000 : ℝ) (501127352731/1000000000000 : ℝ) (125281838171/250000000000 : ℝ) (501127352693/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33393/262144 : ℝ))) 4 (250563676361/500000000000 : ℝ) (501127352731/1000000000000 : ℝ) (125281838171/250000000000 : ℝ) (501127352693/1000000000000 : ℝ) (501127352703/1000000000000 : ℝ) (62640919089/125000000000 : ℝ) (250563676351/500000000000 : ℝ) (62640919089/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33393/262144 : ℝ))) 5 (501127352703/1000000000000 : ℝ) (62640919089/125000000000 : ℝ) (250563676351/500000000000 : ℝ) (62640919089/125000000000 : ℝ) (250563676351/500000000000 : ℝ) (62640919089/125000000000 : ℝ) (250563676351/500000000000 : ℝ) (62640919089/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33393/262144 : ℝ))) 6 (250563676351/500000000000 : ℝ) (62640919089/125000000000 : ℝ) (250563676351/500000000000 : ℝ) (62640919089/125000000000 : ℝ) (250563676351/500000000000 : ℝ) (62640919089/125000000000 : ℝ) (250563676351/500000000000 : ℝ) (62640919089/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33393/262144 : ℝ))) 7 (250563676351/500000000000 : ℝ) (62640919089/125000000000 : ℝ) (250563676351/500000000000 : ℝ) (62640919089/125000000000 : ℝ) (250563676351/500000000000 : ℝ) (62640919089/125000000000 : ℝ) (250563676351/500000000000 : ℝ) (62640919089/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33393/262144 : ℝ)) hmem 8 (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ) (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33393/262144 : ℝ))) hcmem 8 (250563676351/500000000000 : ℝ) (62640919089/125000000000 : ℝ) (250563676351/500000000000 : ℝ) (62640919089/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33393/262144 : ℝ)) (124010727257/125000000000 : ℝ) (992085818059/1000000000000 : ℝ) (250563676351/500000000000 : ℝ) (62640919089/125000000000 : ℝ) (31737940027/40000000000 : ℝ) (158689700139/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0713_exp_lower
  have heNumeric : (2054901960177/1000000000000 : ℝ)/4 ≤ Real.exp (-17051295289667/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901960177/1000000000000 : ℝ)/4 ≤ Real.exp ((66785/524288 : ℝ)-(158689700139/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66785/524288 : ℝ) (33393/262144 : ℝ) (158689700139/200000000000 : ℝ) (2054901960177/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0714; no trusted numerical premise.
theorem cover8_leaf0714_exp_radius : (199602314368504553/200000000000000000 : ℝ) ≤ Real.exp ((-66787/4194304 : ℝ)/8) ∧ Real.exp ((-66787/4194304 : ℝ)/8) ≤ (499005785921261383/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66787/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0714_exp_lower : (46005673566807523/50000000000000000 : ℝ) ≤ Real.exp ((-42628238405503/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628238405503/64000000000000 : ℝ)/8) ≤ (920113471336150461/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628238405503/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0714_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980390871/200000000000 : ℝ) ≤ 4*Real.exp (33393/262144 : ℝ)*Real.exp (-mu (radius 8 (66787/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980390871/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66787/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0714_exp_radius
  have hrNumeric : (984202843267/1000000000000 : ℝ) ≤ Real.exp (-66787/4194304 : ℝ) ∧ Real.exp (-66787/4194304 : ℝ) ≤ (246050710817/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984202843267/1000000000000 : ℝ) ≤ (radius 8 (66787/524288 : ℝ)) ∧ (radius 8 (66787/524288 : ℝ)) ≤ (246050710817/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66787/524288 : ℝ)) (984202843267/1000000000000 : ℝ) (246050710817/250000000000 : ℝ) (35408904701/200000000000 : ℝ) (177044523511/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66787/524288 : ℝ)) (984202843267/1000000000000 : ℝ) (246050710817/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66787/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984202843267/1000000000000 : ℝ) (246050710817/250000000000 : ℝ) (992101421633/1000000000000 : ℝ) (496050710817/500000000000 : ℝ) (992069979017/1000000000000 : ℝ) (496034989509/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66787/524288 : ℝ)) 1 (992101421633/1000000000000 : ℝ) (496050710817/500000000000 : ℝ) (992069979017/1000000000000 : ℝ) (496034989509/500000000000 : ℝ) (39683428013/40000000000 : ℝ) (496042850163/500000000000 : ℝ) (4960428501/5000000000 : ℝ) (496042850101/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66787/524288 : ℝ)) 2 (39683428013/40000000000 : ℝ) (496042850163/500000000000 : ℝ) (4960428501/5000000000 : ℝ) (496042850101/500000000000 : ℝ) (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ) (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66787/524288 : ℝ)) 3 (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ) (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ) (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ) (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66787/524288 : ℝ)) 4 (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ) (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ) (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ) (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66787/524288 : ℝ)) 5 (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ) (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ) (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ) (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66787/524288 : ℝ)) 6 (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ) (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ) (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ) (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66787/524288 : ℝ)) 7 (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ) (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ) (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ) (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66787/524288 : ℝ))) (35408904701/200000000000 : ℝ) (177044523511/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66787/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35408904701/200000000000 : ℝ) (177044523511/1000000000000 : ℝ) (73565282719/125000000000 : ℝ) (147130565439/250000000000 : ℝ) (42076659029/100000000000 : ℝ) (210383295149/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66787/524288 : ℝ))) 1 (73565282719/125000000000 : ℝ) (147130565439/250000000000 : ℝ) (42076659029/100000000000 : ℝ) (210383295149/500000000000 : ℝ) (504644426021/1000000000000 : ℝ) (504644426027/1000000000000 : ℝ) (124406216029/250000000000 : ℝ) (124406216031/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66787/524288 : ℝ))) 2 (504644426021/1000000000000 : ℝ) (504644426027/1000000000000 : ℝ) (124406216029/250000000000 : ℝ) (124406216031/250000000000 : ℝ) (125283661267/250000000000 : ℝ) (125283661269/250000000000 : ℝ) (250561177123/500000000000 : ℝ) (250561177127/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66787/524288 : ℝ))) 3 (125283661267/250000000000 : ℝ) (125283661269/250000000000 : ℝ) (250561177123/500000000000 : ℝ) (250561177127/500000000000 : ℝ) (501128499657/1000000000000 : ℝ) (100225699933/200000000000 : ℝ) (501128499619/1000000000000 : ℝ) (125282124907/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66787/524288 : ℝ))) 4 (501128499657/1000000000000 : ℝ) (100225699933/200000000000 : ℝ) (501128499619/1000000000000 : ℝ) (125282124907/250000000000 : ℝ) (250564249819/500000000000 : ℝ) (501128499647/1000000000000 : ℝ) (501128499637/1000000000000 : ℝ) (501128499647/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66787/524288 : ℝ))) 5 (250564249819/500000000000 : ℝ) (501128499647/1000000000000 : ℝ) (501128499637/1000000000000 : ℝ) (501128499647/1000000000000 : ℝ) (501128499637/1000000000000 : ℝ) (501128499647/1000000000000 : ℝ) (501128499637/1000000000000 : ℝ) (501128499647/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66787/524288 : ℝ))) 6 (501128499637/1000000000000 : ℝ) (501128499647/1000000000000 : ℝ) (501128499637/1000000000000 : ℝ) (501128499647/1000000000000 : ℝ) (501128499637/1000000000000 : ℝ) (501128499647/1000000000000 : ℝ) (501128499637/1000000000000 : ℝ) (501128499647/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66787/524288 : ℝ))) 7 (501128499637/1000000000000 : ℝ) (501128499647/1000000000000 : ℝ) (501128499637/1000000000000 : ℝ) (501128499647/1000000000000 : ℝ) (501128499637/1000000000000 : ℝ) (501128499647/1000000000000 : ℝ) (501128499637/1000000000000 : ℝ) (501128499647/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66787/524288 : ℝ)) hmem 8 (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ) (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66787/524288 : ℝ))) hcmem 8 (501128499637/1000000000000 : ℝ) (501128499647/1000000000000 : ℝ) (501128499637/1000000000000 : ℝ) (501128499647/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66787/524288 : ℝ)) (496042850131/500000000000 : ℝ) (124010712533/125000000000 : ℝ) (501128499637/1000000000000 : ℝ) (501128499647/1000000000000 : ℝ) (793450410859/1000000000000 : ℝ) (793450410877/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0714_exp_lower
  have heNumeric : (410980390871/200000000000 : ℝ)/4 ≤ Real.exp (-42628238405503/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980390871/200000000000 : ℝ)/4 ≤ Real.exp ((33393/262144 : ℝ)-(793450410877/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33393/262144 : ℝ) (66787/524288 : ℝ) (793450410877/1000000000000 : ℝ) (410980390871/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0715; no trusted numerical premise.
theorem cover8_leaf0715_exp_radius : (998011542099460597/1000000000000000000 : ℝ) ≤ Real.exp ((-16697/1048576 : ℝ)/8) ∧ Real.exp ((-16697/1048576 : ℝ)/8) ≤ (499005771049730299/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16697/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0715_exp_lower : (184022694202215629/200000000000000000 : ℝ) ≤ Real.exp ((-85256477172781/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256477172781/128000000000000 : ℝ)/8) ≤ (460056735505539073/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256477172781/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0715_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901948547/1000000000000 : ℝ) ≤ 4*Real.exp (66787/524288 : ℝ)*Real.exp (-mu (radius 8 (16697/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901948547/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16697/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0715_exp_radius
  have hrNumeric : (492101304307/500000000000 : ℝ) ≤ Real.exp (-16697/1048576 : ℝ) ∧ Real.exp (-16697/1048576 : ℝ) ≤ (196840521723/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492101304307/500000000000 : ℝ) ≤ (radius 8 (16697/131072 : ℝ)) ∧ (radius 8 (16697/131072 : ℝ)) ≤ (196840521723/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16697/131072 : ℝ)) (492101304307/500000000000 : ℝ) (196840521723/200000000000 : ℝ) (11065364247/62500000000 : ℝ) (177045827959/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16697/131072 : ℝ)) (492101304307/500000000000 : ℝ) (196840521723/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16697/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492101304307/500000000000 : ℝ) (196840521723/200000000000 : ℝ) (992101304307/1000000000000 : ℝ) (248025326077/250000000000 : ℝ) (62004366297/62500000000 : ℝ) (496034930377/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16697/131072 : ℝ)) 1 (992101304307/1000000000000 : ℝ) (248025326077/250000000000 : ℝ) (62004366297/62500000000 : ℝ) (496034930377/500000000000 : ℝ) (992085582529/1000000000000 : ℝ) (992085582531/1000000000000 : ℝ) (248021395601/250000000000 : ℝ) (992085582407/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16697/131072 : ℝ)) 2 (992085582529/1000000000000 : ℝ) (992085582531/1000000000000 : ℝ) (248021395601/250000000000 : ℝ) (992085582407/1000000000000 : ℝ) (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ) (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16697/131072 : ℝ)) 3 (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ) (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ) (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ) (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16697/131072 : ℝ)) 4 (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ) (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ) (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ) (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16697/131072 : ℝ)) 5 (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ) (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ) (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ) (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16697/131072 : ℝ)) 6 (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ) (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ) (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ) (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16697/131072 : ℝ)) 7 (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ) (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ) (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ) (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16697/131072 : ℝ))) (11065364247/62500000000 : ℝ) (177045827959/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16697/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11065364247/62500000000 : ℝ) (177045827959/1000000000000 : ℝ) (73565364247/125000000000 : ℝ) (29426145699/50000000000 : ℝ) (420768140371/1000000000000 : ℝ) (420768140381/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16697/131072 : ℝ))) 1 (73565364247/125000000000 : ℝ) (29426145699/50000000000 : ℝ) (420768140371/1000000000000 : ℝ) (420768140381/1000000000000 : ℝ) (504645527173/1000000000000 : ℝ) (504645527181/1000000000000 : ℝ) (497626056471/1000000000000 : ℝ) (3110162853/6250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16697/131072 : ℝ))) 2 (504645527173/1000000000000 : ℝ) (504645527181/1000000000000 : ℝ) (497626056471/1000000000000 : ℝ) (3110162853/6250000000 : ℝ) (250567895911/500000000000 : ℝ) (501135791831/1000000000000 : ℝ) (501123501347/1000000000000 : ℝ) (501123501357/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16697/131072 : ℝ))) 3 (250567895911/500000000000 : ℝ) (501135791831/1000000000000 : ℝ) (501123501347/1000000000000 : ℝ) (501123501357/1000000000000 : ℝ) (62641205823/125000000000 : ℝ) (250564823297/500000000000 : ℝ) (250564823273/500000000000 : ℝ) (501129646557/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16697/131072 : ℝ))) 4 (62641205823/125000000000 : ℝ) (250564823297/500000000000 : ℝ) (250564823273/500000000000 : ℝ) (501129646557/1000000000000 : ℝ) (100225929313/200000000000 : ℝ) (31320602911/62500000000 : ℝ) (125282411641/250000000000 : ℝ) (31320602911/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16697/131072 : ℝ))) 5 (100225929313/200000000000 : ℝ) (31320602911/62500000000 : ℝ) (125282411641/250000000000 : ℝ) (31320602911/62500000000 : ℝ) (125282411641/250000000000 : ℝ) (31320602911/62500000000 : ℝ) (125282411641/250000000000 : ℝ) (31320602911/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16697/131072 : ℝ))) 6 (125282411641/250000000000 : ℝ) (31320602911/62500000000 : ℝ) (125282411641/250000000000 : ℝ) (31320602911/62500000000 : ℝ) (125282411641/250000000000 : ℝ) (31320602911/62500000000 : ℝ) (125282411641/250000000000 : ℝ) (31320602911/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16697/131072 : ℝ))) 7 (125282411641/250000000000 : ℝ) (31320602911/62500000000 : ℝ) (125282411641/250000000000 : ℝ) (31320602911/62500000000 : ℝ) (125282411641/250000000000 : ℝ) (31320602911/62500000000 : ℝ) (125282411641/250000000000 : ℝ) (31320602911/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16697/131072 : ℝ)) hmem 8 (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ) (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16697/131072 : ℝ))) hcmem 8 (125282411641/250000000000 : ℝ) (31320602911/62500000000 : ℝ) (125282411641/250000000000 : ℝ) (31320602911/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16697/131072 : ℝ)) (496042791233/500000000000 : ℝ) (992085582469/1000000000000 : ℝ) (125282411641/250000000000 : ℝ) (31320602911/62500000000 : ℝ) (79345232103/100000000000 : ℝ) (198363080263/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0715_exp_lower
  have heNumeric : (2054901948547/1000000000000 : ℝ)/4 ≤ Real.exp (-85256477172781/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901948547/1000000000000 : ℝ)/4 ≤ Real.exp ((66787/524288 : ℝ)-(198363080263/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66787/524288 : ℝ) (16697/131072 : ℝ) (198363080263/250000000000 : ℝ) (2054901948547/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0716; no trusted numerical premise.
theorem cover8_leaf0716_exp_radius : (249502878089099829/250000000000000000 : ℝ) ≤ Real.exp ((-66789/4194304 : ℝ)/8) ∧ Real.exp ((-66789/4194304 : ℝ)/8) ≤ (998011512356399317/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66789/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0716_exp_lower : (920113470689686283/1000000000000000000 : ℝ) ≤ Real.exp ((-4262823876523/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262823876523/6400000000000 : ℝ)/8) ≤ (230028367672421571/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262823876523/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0716_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980388561/200000000000 : ℝ) ≤ 4*Real.exp (16697/131072 : ℝ)*Real.exp (-mu (radius 8 (66789/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980388561/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66789/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0716_exp_radius
  have hrNumeric : (492101186981/500000000000 : ℝ) ≤ Real.exp (-66789/4194304 : ℝ) ∧ Real.exp (-66789/4194304 : ℝ) ≤ (984202373963/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492101186981/500000000000 : ℝ) ≤ (radius 8 (66789/524288 : ℝ)) ∧ (radius 8 (66789/524288 : ℝ)) ≤ (984202373963/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66789/524288 : ℝ)) (492101186981/500000000000 : ℝ) (984202373963/1000000000000 : ℝ) (5532722887/31250000000 : ℝ) (177047132391/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66789/524288 : ℝ)) (492101186981/500000000000 : ℝ) (984202373963/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66789/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492101186981/500000000000 : ℝ) (984202373963/1000000000000 : ℝ) (992101186981/1000000000000 : ℝ) (496050593491/500000000000 : ℝ) (124008717811/125000000000 : ℝ) (99206974249/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66789/524288 : ℝ)) 1 (992101186981/1000000000000 : ℝ) (496050593491/500000000000 : ℝ) (124008717811/125000000000 : ℝ) (99206974249/100000000000 : ℝ) (496042732367/500000000000 : ℝ) (31002670773/31250000000 : ℝ) (992085464609/1000000000000 : ℝ) (248021366153/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66789/524288 : ℝ)) 2 (496042732367/500000000000 : ℝ) (31002670773/31250000000 : ℝ) (992085464609/1000000000000 : ℝ) (248021366153/250000000000 : ℝ) (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ) (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66789/524288 : ℝ)) 3 (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ) (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ) (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ) (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66789/524288 : ℝ)) 4 (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ) (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ) (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ) (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66789/524288 : ℝ)) 5 (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ) (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ) (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ) (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66789/524288 : ℝ)) 6 (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ) (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ) (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ) (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66789/524288 : ℝ)) 7 (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ) (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ) (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ) (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66789/524288 : ℝ))) (5532722887/31250000000 : ℝ) (177047132391/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66789/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5532722887/31250000000 : ℝ) (177047132391/1000000000000 : ℝ) (36782722887/62500000000 : ℝ) (147130891549/250000000000 : ℝ) (420769690429/1000000000000 : ℝ) (210384845219/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66789/524288 : ℝ))) 1 (36782722887/62500000000 : ℝ) (147130891549/250000000000 : ℝ) (420769690429/1000000000000 : ℝ) (210384845219/500000000000 : ℝ) (50464662831/100000000000 : ℝ) (504646628317/1000000000000 : ℝ) (62203406101/125000000000 : ℝ) (31101703051/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66789/524288 : ℝ))) 2 (50464662831/100000000000 : ℝ) (504646628317/1000000000000 : ℝ) (62203406101/125000000000 : ℝ) (31101703051/62500000000 : ℝ) (501136938559/1000000000000 : ℝ) (501136938567/1000000000000 : ℝ) (31320290527/62500000000 : ℝ) (12528116211/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66789/524288 : ℝ))) 3 (501136938559/1000000000000 : ℝ) (501136938567/1000000000000 : ℝ) (31320290527/62500000000 : ℝ) (12528116211/25000000000 : ℝ) (100226158699/200000000000 : ℝ) (15660337297/31250000000 : ℝ) (501130793457/1000000000000 : ℝ) (250565396733/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66789/524288 : ℝ))) 4 (100226158699/200000000000 : ℝ) (15660337297/31250000000 : ℝ) (501130793457/1000000000000 : ℝ) (250565396733/500000000000 : ℝ) (125282698369/250000000000 : ℝ) (100226158697/200000000000 : ℝ) (20045231739/40000000000 : ℝ) (100226158697/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66789/524288 : ℝ))) 5 (125282698369/250000000000 : ℝ) (100226158697/200000000000 : ℝ) (20045231739/40000000000 : ℝ) (100226158697/200000000000 : ℝ) (20045231739/40000000000 : ℝ) (100226158697/200000000000 : ℝ) (20045231739/40000000000 : ℝ) (100226158697/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66789/524288 : ℝ))) 6 (20045231739/40000000000 : ℝ) (100226158697/200000000000 : ℝ) (20045231739/40000000000 : ℝ) (100226158697/200000000000 : ℝ) (20045231739/40000000000 : ℝ) (100226158697/200000000000 : ℝ) (20045231739/40000000000 : ℝ) (100226158697/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66789/524288 : ℝ))) 7 (20045231739/40000000000 : ℝ) (100226158697/200000000000 : ℝ) (20045231739/40000000000 : ℝ) (100226158697/200000000000 : ℝ) (20045231739/40000000000 : ℝ) (100226158697/200000000000 : ℝ) (20045231739/40000000000 : ℝ) (100226158697/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66789/524288 : ℝ)) hmem 8 (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ) (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66789/524288 : ℝ))) hcmem 8 (20045231739/40000000000 : ℝ) (100226158697/200000000000 : ℝ) (20045231739/40000000000 : ℝ) (100226158697/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66789/524288 : ℝ)) (992085464671/1000000000000 : ℝ) (496042732337/500000000000 : ℝ) (20045231739/40000000000 : ℝ) (100226158697/200000000000 : ℝ) (99181778897/125000000000 : ℝ) (158690846239/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0716_exp_lower
  have heNumeric : (410980388561/200000000000 : ℝ)/4 ≤ Real.exp (-4262823876523/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980388561/200000000000 : ℝ)/4 ≤ Real.exp ((16697/131072 : ℝ)-(158690846239/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16697/131072 : ℝ) (66789/524288 : ℝ) (158690846239/200000000000 : ℝ) (410980388561/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0717; no trusted numerical premise.
theorem cover8_leaf0717_exp_radius : (499005741306669461/500000000000000000 : ℝ) ≤ Real.exp ((-33395/2097152 : ℝ)/8) ∧ Real.exp ((-33395/2097152 : ℝ)/8) ≤ (998011482613338923/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33395/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0717_exp_lower : (920113470370134649/1000000000000000000 : ℝ) ≤ Real.exp ((-85256477886091/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256477886091/128000000000000 : ℝ)/8) ≤ (18402269407402693/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256477886091/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0717_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980387419/200000000000 : ℝ) ≤ 4*Real.exp (66789/524288 : ℝ)*Real.exp (-mu (radius 8 (33395/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980387419/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33395/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0717_exp_radius
  have hrNumeric : (98420213931/100000000000 : ℝ) ≤ Real.exp (-33395/2097152 : ℝ) ∧ Real.exp (-33395/2097152 : ℝ) ≤ (984202139311/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98420213931/100000000000 : ℝ) ≤ (radius 8 (33395/262144 : ℝ)) ∧ (radius 8 (33395/262144 : ℝ)) ≤ (984202139311/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33395/262144 : ℝ)) (98420213931/100000000000 : ℝ) (984202139311/1000000000000 : ℝ) (88524218403/500000000000 : ℝ) (177048436813/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33395/262144 : ℝ)) (98420213931/100000000000 : ℝ) (984202139311/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33395/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98420213931/100000000000 : ℝ) (984202139311/1000000000000 : ℝ) (198420213931/200000000000 : ℝ) (124012633707/125000000000 : ℝ) (39682784969/40000000000 : ℝ) (496034812113/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33395/262144 : ℝ)) 1 (198420213931/200000000000 : ℝ) (124012633707/125000000000 : ℝ) (39682784969/40000000000 : ℝ) (496034812113/500000000000 : ℝ) (49604267347/50000000000 : ℝ) (992085346941/1000000000000 : ℝ) (198417069363/200000000000 : ℝ) (992085346817/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33395/262144 : ℝ)) 2 (49604267347/50000000000 : ℝ) (992085346941/1000000000000 : ℝ) (198417069363/200000000000 : ℝ) (992085346817/1000000000000 : ℝ) (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ) (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33395/262144 : ℝ)) 3 (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ) (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ) (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ) (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33395/262144 : ℝ)) 4 (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ) (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ) (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ) (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33395/262144 : ℝ)) 5 (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ) (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ) (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ) (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33395/262144 : ℝ)) 6 (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ) (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ) (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ) (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33395/262144 : ℝ)) 7 (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ) (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ) (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ) (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33395/262144 : ℝ))) (88524218403/500000000000 : ℝ) (177048436813/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33395/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88524218403/500000000000 : ℝ) (177048436813/1000000000000 : ℝ) (588524218403/1000000000000 : ℝ) (588524218407/1000000000000 : ℝ) (420771240469/1000000000000 : ℝ) (210385620239/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33395/262144 : ℝ))) 1 (588524218403/1000000000000 : ℝ) (588524218407/1000000000000 : ℝ) (420771240469/1000000000000 : ℝ) (210385620239/500000000000 : ℝ) (126161932359/250000000000 : ℝ) (504647729443/1000000000000 : ℝ) (124407110283/250000000000 : ℝ) (24881422057/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33395/262144 : ℝ))) 2 (126161932359/250000000000 : ℝ) (504647729443/1000000000000 : ℝ) (124407110283/250000000000 : ℝ) (24881422057/50000000000 : ℝ) (125284521321/250000000000 : ℝ) (125284521323/250000000000 : ℝ) (31320362219/62500000000 : ℝ) (501125795513/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33395/262144 : ℝ))) 3 (125284521321/250000000000 : ℝ) (125284521323/250000000000 : ℝ) (31320362219/62500000000 : ℝ) (501125795513/1000000000000 : ℝ) (250565970197/500000000000 : ℝ) (501131940403/1000000000000 : ℝ) (125282985089/250000000000 : ℝ) (100226388073/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33395/262144 : ℝ))) 4 (250565970197/500000000000 : ℝ) (501131940403/1000000000000 : ℝ) (125282985089/250000000000 : ℝ) (100226388073/200000000000 : ℝ) (4009055523/8000000000 : ℝ) (15660373137/31250000000 : ℝ) (250565970187/500000000000 : ℝ) (15660373137/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33395/262144 : ℝ))) 5 (4009055523/8000000000 : ℝ) (15660373137/31250000000 : ℝ) (250565970187/500000000000 : ℝ) (15660373137/31250000000 : ℝ) (250565970187/500000000000 : ℝ) (15660373137/31250000000 : ℝ) (250565970187/500000000000 : ℝ) (15660373137/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33395/262144 : ℝ))) 6 (250565970187/500000000000 : ℝ) (15660373137/31250000000 : ℝ) (250565970187/500000000000 : ℝ) (15660373137/31250000000 : ℝ) (250565970187/500000000000 : ℝ) (15660373137/31250000000 : ℝ) (250565970187/500000000000 : ℝ) (15660373137/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33395/262144 : ℝ))) 7 (250565970187/500000000000 : ℝ) (15660373137/31250000000 : ℝ) (250565970187/500000000000 : ℝ) (15660373137/31250000000 : ℝ) (250565970187/500000000000 : ℝ) (15660373137/31250000000 : ℝ) (250565970187/500000000000 : ℝ) (15660373137/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33395/262144 : ℝ)) hmem 8 (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ) (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33395/262144 : ℝ))) hcmem 8 (250565970187/500000000000 : ℝ) (15660373137/31250000000 : ℝ) (250565970187/500000000000 : ℝ) (15660373137/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33395/262144 : ℝ)) (992085346877/1000000000000 : ℝ) (992085346879/1000000000000 : ℝ) (250565970187/500000000000 : ℝ) (15660373137/31250000000 : ℝ) (99182017663/125000000000 : ℝ) (396728070661/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0717_exp_lower
  have heNumeric : (410980387419/200000000000 : ℝ)/4 ≤ Real.exp (-85256477886091/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980387419/200000000000 : ℝ)/4 ≤ Real.exp ((66789/524288 : ℝ)-(396728070661/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66789/524288 : ℝ) (33395/262144 : ℝ) (396728070661/500000000000 : ℝ) (410980387419/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0718; no trusted numerical premise.
theorem cover8_leaf0718_exp_radius : (998011452870279413/1000000000000000000 : ℝ) ≤ Real.exp ((-66791/4194304 : ℝ)/8) ∧ Real.exp ((-66791/4194304 : ℝ)/8) ≤ (499005726435139707/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66791/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0718_exp_lower : (115014183756624789/125000000000000000 : ℝ) ≤ Real.exp ((-42628239119517/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628239119517/64000000000000 : ℝ)/8) ≤ (920113470052998313/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628239119517/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0718_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901931429/1000000000000 : ℝ) ≤ 4*Real.exp (33395/262144 : ℝ)*Real.exp (-mu (radius 8 (66791/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901931429/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66791/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0718_exp_radius
  have hrNumeric : (492100952329/500000000000 : ℝ) ≤ Real.exp (-66791/4194304 : ℝ) ∧ Real.exp (-66791/4194304 : ℝ) ≤ (984201904659/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492100952329/500000000000 : ℝ) ≤ (radius 8 (66791/524288 : ℝ)) ∧ (radius 8 (66791/524288 : ℝ)) ≤ (984201904659/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66791/524288 : ℝ)) (492100952329/500000000000 : ℝ) (984201904659/1000000000000 : ℝ) (88524870609/500000000000 : ℝ) (7081989649/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66791/524288 : ℝ)) (492100952329/500000000000 : ℝ) (984201904659/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66791/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492100952329/500000000000 : ℝ) (984201904659/1000000000000 : ℝ) (992100952329/1000000000000 : ℝ) (99210095233/100000000000 : ℝ) (992069505961/1000000000000 : ℝ) (496034752981/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66791/524288 : ℝ)) 1 (992100952329/1000000000000 : ℝ) (99210095233/100000000000 : ℝ) (992069505961/1000000000000 : ℝ) (496034752981/500000000000 : ℝ) (198417045829/200000000000 : ℝ) (496042614573/500000000000 : ℝ) (49604261451/50000000000 : ℝ) (496042614511/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66791/524288 : ℝ)) 2 (198417045829/200000000000 : ℝ) (496042614573/500000000000 : ℝ) (49604261451/50000000000 : ℝ) (496042614511/500000000000 : ℝ) (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ) (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66791/524288 : ℝ)) 3 (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ) (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ) (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ) (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66791/524288 : ℝ)) 4 (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ) (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ) (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ) (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66791/524288 : ℝ)) 5 (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ) (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ) (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ) (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66791/524288 : ℝ)) 6 (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ) (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ) (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ) (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66791/524288 : ℝ)) 7 (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ) (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ) (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ) (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66791/524288 : ℝ))) (88524870609/500000000000 : ℝ) (7081989649/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66791/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88524870609/500000000000 : ℝ) (7081989649/40000000000 : ℝ) (588524870609/1000000000000 : ℝ) (588524870613/1000000000000 : ℝ) (420772790491/1000000000000 : ℝ) (841545581/2000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66791/524288 : ℝ))) 1 (588524870609/1000000000000 : ℝ) (588524870613/1000000000000 : ℝ) (420772790491/1000000000000 : ℝ) (841545581/2000000000 : ℝ) (10092976611/20000000000 : ℝ) (504648830557/1000000000000 : ℝ) (497629633441/1000000000000 : ℝ) (497629633449/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66791/524288 : ℝ))) 2 (10092976611/20000000000 : ℝ) (504648830557/1000000000000 : ℝ) (497629633441/1000000000000 : ℝ) (497629633449/1000000000000 : ℝ) (100227846399/200000000000 : ℝ) (501139232003/1000000000000 : ℝ) (501126942563/1000000000000 : ℝ) (501126942571/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66791/524288 : ℝ))) 3 (100227846399/200000000000 : ℝ) (501139232003/1000000000000 : ℝ) (501126942563/1000000000000 : ℝ) (501126942571/1000000000000 : ℝ) (501133087279/1000000000000 : ℝ) (501133087287/1000000000000 : ℝ) (501133087241/1000000000000 : ℝ) (2004532349/4000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66791/524288 : ℝ))) 4 (501133087279/1000000000000 : ℝ) (501133087287/1000000000000 : ℝ) (501133087241/1000000000000 : ℝ) (2004532349/4000000000 : ℝ) (25056654363/50000000000 : ℝ) (501133087269/1000000000000 : ℝ) (501133087259/1000000000000 : ℝ) (501133087269/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66791/524288 : ℝ))) 5 (25056654363/50000000000 : ℝ) (501133087269/1000000000000 : ℝ) (501133087259/1000000000000 : ℝ) (501133087269/1000000000000 : ℝ) (501133087259/1000000000000 : ℝ) (501133087269/1000000000000 : ℝ) (501133087259/1000000000000 : ℝ) (501133087269/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66791/524288 : ℝ))) 6 (501133087259/1000000000000 : ℝ) (501133087269/1000000000000 : ℝ) (501133087259/1000000000000 : ℝ) (501133087269/1000000000000 : ℝ) (501133087259/1000000000000 : ℝ) (501133087269/1000000000000 : ℝ) (501133087259/1000000000000 : ℝ) (501133087269/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66791/524288 : ℝ))) 7 (501133087259/1000000000000 : ℝ) (501133087269/1000000000000 : ℝ) (501133087259/1000000000000 : ℝ) (501133087269/1000000000000 : ℝ) (501133087259/1000000000000 : ℝ) (501133087269/1000000000000 : ℝ) (501133087259/1000000000000 : ℝ) (501133087269/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66791/524288 : ℝ)) hmem 8 (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ) (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66791/524288 : ℝ))) hcmem 8 (501133087259/1000000000000 : ℝ) (501133087269/1000000000000 : ℝ) (501133087259/1000000000000 : ℝ) (501133087269/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66791/524288 : ℝ)) (496042614541/500000000000 : ℝ) (248021307271/250000000000 : ℝ) (501133087259/1000000000000 : ℝ) (501133087269/1000000000000 : ℝ) (79345805141/100000000000 : ℝ) (198364512857/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0718_exp_lower
  have heNumeric : (2054901931429/1000000000000 : ℝ)/4 ≤ Real.exp (-42628239119517/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901931429/1000000000000 : ℝ)/4 ≤ Real.exp ((33395/262144 : ℝ)-(198364512857/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33395/262144 : ℝ) (66791/524288 : ℝ) (198364512857/250000000000 : ℝ) (2054901931429/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0719; no trusted numerical premise.
theorem cover8_leaf0719_exp_radius : (124751427890902599/125000000000000000 : ℝ) ≤ Real.exp ((-8349/524288 : ℝ)/8) ∧ Real.exp ((-8349/524288 : ℝ)/8) ≤ (998011423127220793/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8349/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0719_exp_lower : (920113469737817217/1000000000000000000 : ℝ) ≤ Real.exp ((-85256478589801/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256478589801/128000000000000 : ℝ)/8) ≤ (460056734868908609/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256478589801/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0719_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450962899/500000000000 : ℝ) ≤ 4*Real.exp (66791/524288 : ℝ)*Real.exp (-mu (radius 8 (8349/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450962899/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8349/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0719_exp_radius
  have hrNumeric : (492100835003/500000000000 : ℝ) ≤ Real.exp (-8349/524288 : ℝ) ∧ Real.exp (-8349/524288 : ℝ) ≤ (984201670007/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492100835003/500000000000 : ℝ) ≤ (radius 8 (8349/65536 : ℝ)) ∧ (radius 8 (8349/65536 : ℝ)) ≤ (984201670007/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8349/65536 : ℝ)) (492100835003/500000000000 : ℝ) (984201670007/1000000000000 : ℝ) (8852552281/50000000000 : ℝ) (177051045627/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8349/65536 : ℝ)) (492100835003/500000000000 : ℝ) (984201670007/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8349/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492100835003/500000000000 : ℝ) (984201670007/1000000000000 : ℝ) (992100835003/1000000000000 : ℝ) (248025208751/250000000000 : ℝ) (992069387697/1000000000000 : ℝ) (496034693849/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8349/65536 : ℝ)) 1 (992100835003/1000000000000 : ℝ) (248025208751/250000000000 : ℝ) (992069387697/1000000000000 : ℝ) (496034693849/500000000000 : ℝ) (19841702227/20000000000 : ℝ) (992085111351/1000000000000 : ℝ) (39683404449/40000000000 : ℝ) (992085111227/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8349/65536 : ℝ)) 2 (19841702227/20000000000 : ℝ) (992085111351/1000000000000 : ℝ) (39683404449/40000000000 : ℝ) (992085111227/1000000000000 : ℝ) (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ) (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8349/65536 : ℝ)) 3 (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ) (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ) (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ) (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8349/65536 : ℝ)) 4 (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ) (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ) (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ) (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8349/65536 : ℝ)) 5 (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ) (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ) (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ) (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8349/65536 : ℝ)) 6 (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ) (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ) (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ) (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8349/65536 : ℝ)) 7 (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ) (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ) (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ) (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8349/65536 : ℝ))) (8852552281/50000000000 : ℝ) (177051045627/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8349/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8852552281/50000000000 : ℝ) (177051045627/1000000000000 : ℝ) (58852552281/100000000000 : ℝ) (294262761407/500000000000 : ℝ) (26298396281/62500000000 : ℝ) (84154868101/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8349/65536 : ℝ))) 1 (58852552281/100000000000 : ℝ) (294262761407/500000000000 : ℝ) (26298396281/62500000000 : ℝ) (84154868101/200000000000 : ℝ) (504649931653/1000000000000 : ℝ) (25232496583/50000000000 : ℝ) (248815412869/500000000000 : ℝ) (248815412873/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8349/65536 : ℝ))) 2 (504649931653/1000000000000 : ℝ) (25232496583/50000000000 : ℝ) (248815412869/500000000000 : ℝ) (248815412873/500000000000 : ℝ) (100228075739/200000000000 : ℝ) (501140378703/1000000000000 : ℝ) (50112808961/100000000000 : ℝ) (501128089619/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8349/65536 : ℝ))) 3 (100228075739/200000000000 : ℝ) (501140378703/1000000000000 : ℝ) (50112808961/100000000000 : ℝ) (501128089619/1000000000000 : ℝ) (62641779269/125000000000 : ℝ) (501134234161/1000000000000 : ℝ) (250567117057/500000000000 : ℝ) (125283558531/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8349/65536 : ℝ))) 4 (62641779269/125000000000 : ℝ) (501134234161/1000000000000 : ℝ) (250567117057/500000000000 : ℝ) (125283558531/250000000000 : ℝ) (501134234133/1000000000000 : ℝ) (501134234143/1000000000000 : ℝ) (125283558533/250000000000 : ℝ) (501134234143/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8349/65536 : ℝ))) 5 (501134234133/1000000000000 : ℝ) (501134234143/1000000000000 : ℝ) (125283558533/250000000000 : ℝ) (501134234143/1000000000000 : ℝ) (125283558533/250000000000 : ℝ) (501134234143/1000000000000 : ℝ) (125283558533/250000000000 : ℝ) (501134234143/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8349/65536 : ℝ))) 6 (125283558533/250000000000 : ℝ) (501134234143/1000000000000 : ℝ) (125283558533/250000000000 : ℝ) (501134234143/1000000000000 : ℝ) (125283558533/250000000000 : ℝ) (501134234143/1000000000000 : ℝ) (125283558533/250000000000 : ℝ) (501134234143/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8349/65536 : ℝ))) 7 (125283558533/250000000000 : ℝ) (501134234143/1000000000000 : ℝ) (125283558533/250000000000 : ℝ) (501134234143/1000000000000 : ℝ) (125283558533/250000000000 : ℝ) (501134234143/1000000000000 : ℝ) (125283558533/250000000000 : ℝ) (501134234143/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8349/65536 : ℝ)) hmem 8 (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ) (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8349/65536 : ℝ))) hcmem 8 (125283558533/250000000000 : ℝ) (501134234143/1000000000000 : ℝ) (125283558533/250000000000 : ℝ) (501134234143/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8349/65536 : ℝ)) (992085111287/1000000000000 : ℝ) (992085111289/1000000000000 : ℝ) (125283558533/250000000000 : ℝ) (501134234143/1000000000000 : ℝ) (793459961497/1000000000000 : ℝ) (793459961517/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0719_exp_lower
  have heNumeric : (1027450962899/500000000000 : ℝ)/4 ≤ Real.exp (-85256478589801/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450962899/500000000000 : ℝ)/4 ≤ Real.exp ((66791/524288 : ℝ)-(793459961517/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66791/524288 : ℝ) (8349/65536 : ℝ) (793459961517/1000000000000 : ℝ) (1027450962899/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0720; no trusted numerical premise.
theorem cover8_leaf0720_exp_radius : (62375712086510191/62500000000000000 : ℝ) ≤ Real.exp ((-66793/4194304 : ℝ)/8) ∧ Real.exp ((-66793/4194304 : ℝ)/8) ≤ (998011393384163057/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66793/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0720_exp_lower : (460056734712468203/500000000000000000 : ℝ) ≤ Real.exp ((-10657059867251/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657059867251/16000000000000 : ℝ)/8) ≤ (920113469424936407/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657059867251/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0720_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431370013/62500000000 : ℝ) ≤ 4*Real.exp (8349/65536 : ℝ)*Real.exp (-mu (radius 8 (66793/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (128431370013/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66793/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0720_exp_radius
  have hrNumeric : (492100717677/500000000000 : ℝ) ≤ Real.exp (-66793/4194304 : ℝ) ∧ Real.exp (-66793/4194304 : ℝ) ≤ (196840287071/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492100717677/500000000000 : ℝ) ≤ (radius 8 (66793/524288 : ℝ)) ∧ (radius 8 (66793/524288 : ℝ)) ≤ (196840287071/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66793/524288 : ℝ)) (492100717677/500000000000 : ℝ) (196840287071/200000000000 : ℝ) (177052350013/1000000000000 : ℝ) (177052350019/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66793/524288 : ℝ)) (492100717677/500000000000 : ℝ) (196840287071/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66793/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492100717677/500000000000 : ℝ) (196840287071/200000000000 : ℝ) (992100717677/1000000000000 : ℝ) (496050358839/500000000000 : ℝ) (992069269433/1000000000000 : ℝ) (496034634717/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66793/524288 : ℝ)) 1 (992100717677/1000000000000 : ℝ) (496050358839/500000000000 : ℝ) (992069269433/1000000000000 : ℝ) (496034634717/500000000000 : ℝ) (198416998711/200000000000 : ℝ) (248021248389/250000000000 : ℝ) (99208499343/100000000000 : ℝ) (124010624179/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66793/524288 : ℝ)) 2 (198416998711/200000000000 : ℝ) (248021248389/250000000000 : ℝ) (99208499343/100000000000 : ℝ) (124010624179/125000000000 : ℝ) (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ) (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66793/524288 : ℝ)) 3 (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ) (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ) (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ) (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66793/524288 : ℝ)) 4 (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ) (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ) (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ) (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66793/524288 : ℝ)) 5 (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ) (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ) (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ) (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66793/524288 : ℝ)) 6 (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ) (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ) (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ) (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66793/524288 : ℝ)) 7 (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ) (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ) (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ) (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66793/524288 : ℝ))) (177052350013/1000000000000 : ℝ) (177052350019/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66793/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177052350013/1000000000000 : ℝ) (177052350019/1000000000000 : ℝ) (294263087503/500000000000 : ℝ) (58852617501/100000000000 : ℝ) (105193972621/250000000000 : ℝ) (105193972623/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66793/524288 : ℝ))) 1 (294263087503/500000000000 : ℝ) (58852617501/100000000000 : ℝ) (105193972621/250000000000 : ℝ) (105193972623/250000000000 : ℝ) (100930206549/200000000000 : ℝ) (504651032751/1000000000000 : ℝ) (248816009011/500000000000 : ℝ) (49763201803/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66793/524288 : ℝ))) 2 (100930206549/200000000000 : ℝ) (504651032751/1000000000000 : ℝ) (248816009011/500000000000 : ℝ) (49763201803/100000000000 : ℝ) (501141525383/1000000000000 : ℝ) (501141525391/1000000000000 : ℝ) (250564618323/500000000000 : ℝ) (250564618327/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66793/524288 : ℝ))) 3 (501141525383/1000000000000 : ℝ) (501141525391/1000000000000 : ℝ) (250564618323/500000000000 : ℝ) (250564618327/500000000000 : ℝ) (250567690507/500000000000 : ℝ) (501135381023/1000000000000 : ℝ) (31320961311/62500000000 : ℝ) (100227076197/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66793/524288 : ℝ))) 4 (250567690507/500000000000 : ℝ) (501135381023/1000000000000 : ℝ) (31320961311/62500000000 : ℝ) (100227076197/200000000000 : ℝ) (100227076199/200000000000 : ℝ) (125283845251/250000000000 : ℝ) (250567690497/500000000000 : ℝ) (125283845251/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66793/524288 : ℝ))) 5 (100227076199/200000000000 : ℝ) (125283845251/250000000000 : ℝ) (250567690497/500000000000 : ℝ) (125283845251/250000000000 : ℝ) (250567690497/500000000000 : ℝ) (125283845251/250000000000 : ℝ) (250567690497/500000000000 : ℝ) (125283845251/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66793/524288 : ℝ))) 6 (250567690497/500000000000 : ℝ) (125283845251/250000000000 : ℝ) (250567690497/500000000000 : ℝ) (125283845251/250000000000 : ℝ) (250567690497/500000000000 : ℝ) (125283845251/250000000000 : ℝ) (250567690497/500000000000 : ℝ) (125283845251/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66793/524288 : ℝ))) 7 (250567690497/500000000000 : ℝ) (125283845251/250000000000 : ℝ) (250567690497/500000000000 : ℝ) (125283845251/250000000000 : ℝ) (250567690497/500000000000 : ℝ) (125283845251/250000000000 : ℝ) (250567690497/500000000000 : ℝ) (125283845251/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66793/524288 : ℝ)) hmem 8 (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ) (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66793/524288 : ℝ))) hcmem 8 (250567690497/500000000000 : ℝ) (125283845251/250000000000 : ℝ) (250567690497/500000000000 : ℝ) (125283845251/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66793/524288 : ℝ)) (248021248373/250000000000 : ℝ) (496042496747/500000000000 : ℝ) (250567690497/500000000000 : ℝ) (125283845251/250000000000 : ℝ) (49591366973/62500000000 : ℝ) (396730935793/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0720_exp_lower
  have heNumeric : (128431370013/62500000000 : ℝ)/4 ≤ Real.exp (-10657059867251/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431370013/62500000000 : ℝ)/4 ≤ Real.exp ((8349/65536 : ℝ)-(396730935793/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8349/65536 : ℝ) (66793/524288 : ℝ) (396730935793/500000000000 : ℝ) (128431370013/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0721; no trusted numerical premise.
theorem cover8_leaf0721_exp_radius : (998011363641106207/1000000000000000000 : ℝ) ≤ Real.exp ((-33397/2097152 : ℝ)/8) ∧ Real.exp ((-33397/2097152 : ℝ)/8) ≤ (31187855113784569/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33397/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0721_exp_lower : (28753545909820027/31250000000000000 : ℝ) ≤ Real.exp ((-85256479283783/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256479283783/128000000000000 : ℝ)/8) ≤ (184022693822848173/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256479283783/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0721_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901914657/1000000000000 : ℝ) ≤ 4*Real.exp (66793/524288 : ℝ)*Real.exp (-mu (radius 8 (33397/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901914657/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33397/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0721_exp_radius
  have hrNumeric : (492100600351/500000000000 : ℝ) ≤ Real.exp (-33397/2097152 : ℝ) ∧ Real.exp (-33397/2097152 : ℝ) ≤ (984201200703/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492100600351/500000000000 : ℝ) ≤ (radius 8 (33397/262144 : ℝ)) ∧ (radius 8 (33397/262144 : ℝ)) ≤ (984201200703/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33397/262144 : ℝ)) (492100600351/500000000000 : ℝ) (984201200703/1000000000000 : ℝ) (35410730879/200000000000 : ℝ) (177053654401/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33397/262144 : ℝ)) (492100600351/500000000000 : ℝ) (984201200703/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33397/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492100600351/500000000000 : ℝ) (984201200703/1000000000000 : ℝ) (992100600351/1000000000000 : ℝ) (31003143761/31250000000 : ℝ) (992069151169/1000000000000 : ℝ) (99206915117/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33397/262144 : ℝ)) 1 (992100600351/1000000000000 : ℝ) (31003143761/31250000000 : ℝ) (992069151169/1000000000000 : ℝ) (99206915117/100000000000 : ℝ) (12401060947/12500000000 : ℝ) (992084875761/1000000000000 : ℝ) (198416975127/200000000000 : ℝ) (992084875637/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33397/262144 : ℝ)) 2 (12401060947/12500000000 : ℝ) (992084875761/1000000000000 : ℝ) (198416975127/200000000000 : ℝ) (992084875637/1000000000000 : ℝ) (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ) (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33397/262144 : ℝ)) 3 (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ) (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ) (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ) (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33397/262144 : ℝ)) 4 (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ) (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ) (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ) (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33397/262144 : ℝ)) 5 (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ) (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ) (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ) (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33397/262144 : ℝ)) 6 (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ) (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ) (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ) (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33397/262144 : ℝ)) 7 (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ) (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ) (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ) (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33397/262144 : ℝ))) (35410730879/200000000000 : ℝ) (177053654401/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33397/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35410730879/200000000000 : ℝ) (177053654401/1000000000000 : ℝ) (588526827197/1000000000000 : ℝ) (588526827201/1000000000000 : ℝ) (420777440453/1000000000000 : ℝ) (210388720231/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33397/262144 : ℝ))) 1 (588526827197/1000000000000 : ℝ) (588526827201/1000000000000 : ℝ) (420777440453/1000000000000 : ℝ) (210388720231/500000000000 : ℝ) (20186085353/40000000000 : ℝ) (63081516729/125000000000 : ℝ) (124408302573/250000000000 : ℝ) (4976332103/10000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33397/262144 : ℝ))) 2 (20186085353/40000000000 : ℝ) (63081516729/125000000000 : ℝ) (124408302573/250000000000 : ℝ) (4976332103/10000000000 : ℝ) (250571336029/500000000000 : ℝ) (250571336033/500000000000 : ℝ) (125282595917/250000000000 : ℝ) (501130383677/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33397/262144 : ℝ))) 3 (250571336029/500000000000 : ℝ) (250571336033/500000000000 : ℝ) (125282595917/250000000000 : ℝ) (501130383677/1000000000000 : ℝ) (501136527863/1000000000000 : ℝ) (978782281/1953125000 : ℝ) (20045461113/40000000000 : ℝ) (250568263917/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33397/262144 : ℝ))) 4 (501136527863/1000000000000 : ℝ) (978782281/1953125000 : ℝ) (20045461113/40000000000 : ℝ) (250568263917/500000000000 : ℝ) (125284131961/250000000000 : ℝ) (501136527853/1000000000000 : ℝ) (501136527843/1000000000000 : ℝ) (501136527853/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33397/262144 : ℝ))) 5 (125284131961/250000000000 : ℝ) (501136527853/1000000000000 : ℝ) (501136527843/1000000000000 : ℝ) (501136527853/1000000000000 : ℝ) (501136527843/1000000000000 : ℝ) (501136527853/1000000000000 : ℝ) (501136527843/1000000000000 : ℝ) (501136527853/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33397/262144 : ℝ))) 6 (501136527843/1000000000000 : ℝ) (501136527853/1000000000000 : ℝ) (501136527843/1000000000000 : ℝ) (501136527853/1000000000000 : ℝ) (501136527843/1000000000000 : ℝ) (501136527853/1000000000000 : ℝ) (501136527843/1000000000000 : ℝ) (501136527853/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33397/262144 : ℝ))) 7 (501136527843/1000000000000 : ℝ) (501136527853/1000000000000 : ℝ) (501136527843/1000000000000 : ℝ) (501136527853/1000000000000 : ℝ) (501136527843/1000000000000 : ℝ) (501136527853/1000000000000 : ℝ) (501136527843/1000000000000 : ℝ) (501136527853/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33397/262144 : ℝ)) hmem 8 (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ) (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33397/262144 : ℝ))) hcmem 8 (501136527843/1000000000000 : ℝ) (501136527853/1000000000000 : ℝ) (501136527843/1000000000000 : ℝ) (501136527853/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33397/262144 : ℝ)) (992084875697/1000000000000 : ℝ) (992084875699/1000000000000 : ℝ) (501136527843/1000000000000 : ℝ) (501136527853/1000000000000 : ℝ) (396731890809/500000000000 : ℝ) (198365945409/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0721_exp_lower
  have heNumeric : (2054901914657/1000000000000 : ℝ)/4 ≤ Real.exp (-85256479283783/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901914657/1000000000000 : ℝ)/4 ≤ Real.exp ((66793/524288 : ℝ)-(198365945409/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66793/524288 : ℝ) (33397/262144 : ℝ) (198365945409/250000000000 : ℝ) (2054901914657/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0722; no trusted numerical premise.
theorem cover8_leaf0722_exp_radius : (249502833474512561/250000000000000000 : ℝ) ≤ Real.exp ((-66795/4194304 : ℝ)/8) ∧ Real.exp ((-66795/4194304 : ℝ)/8) ≤ (199602266779610049/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66795/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0722_exp_lower : (920113468806535691/1000000000000000000 : ℝ) ≤ Real.exp ((-8525647962623/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525647962623/12800000000000 : ℝ)/8) ≤ (230028367201633923/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525647962623/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0722_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901909159/1000000000000 : ℝ) ≤ 4*Real.exp (33397/262144 : ℝ)*Real.exp (-mu (radius 8 (66795/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901909159/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66795/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0722_exp_radius
  have hrNumeric : (984200966051/1000000000000 : ℝ) ≤ Real.exp (-66795/4194304 : ℝ) ∧ Real.exp (-66795/4194304 : ℝ) ≤ (246050241513/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984200966051/1000000000000 : ℝ) ≤ (radius 8 (66795/524288 : ℝ)) ∧ (radius 8 (66795/524288 : ℝ)) ≤ (246050241513/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66795/524288 : ℝ)) (984200966051/1000000000000 : ℝ) (246050241513/250000000000 : ℝ) (88527479381/500000000000 : ℝ) (11065934923/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66795/524288 : ℝ)) (984200966051/1000000000000 : ℝ) (246050241513/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66795/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984200966051/1000000000000 : ℝ) (246050241513/250000000000 : ℝ) (39684019321/40000000000 : ℝ) (496050241513/500000000000 : ℝ) (198413806581/200000000000 : ℝ) (992069032907/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66795/524288 : ℝ)) 1 (39684019321/40000000000 : ℝ) (496050241513/500000000000 : ℝ) (198413806581/200000000000 : ℝ) (992069032907/1000000000000 : ℝ) (198416951593/200000000000 : ℝ) (992084757967/1000000000000 : ℝ) (12401059473/12500000000 : ℝ) (496042378921/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66795/524288 : ℝ)) 2 (198416951593/200000000000 : ℝ) (992084757967/1000000000000 : ℝ) (12401059473/12500000000 : ℝ) (496042378921/500000000000 : ℝ) (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ) (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66795/524288 : ℝ)) 3 (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ) (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ) (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ) (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66795/524288 : ℝ)) 4 (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ) (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ) (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ) (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66795/524288 : ℝ)) 5 (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ) (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ) (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ) (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66795/524288 : ℝ)) 6 (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ) (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ) (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ) (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66795/524288 : ℝ)) 7 (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ) (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ) (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ) (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66795/524288 : ℝ))) (88527479381/500000000000 : ℝ) (11065934923/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66795/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88527479381/500000000000 : ℝ) (11065934923/62500000000 : ℝ) (588527479381/1000000000000 : ℝ) (73565934923/125000000000 : ℝ) (420778990399/1000000000000 : ℝ) (52597373801/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66795/524288 : ℝ))) 1 (588527479381/1000000000000 : ℝ) (73565934923/125000000000 : ℝ) (420778990399/1000000000000 : ℝ) (52597373801/125000000000 : ℝ) (50465323489/100000000000 : ℝ) (31540827181/62500000000 : ℝ) (31102150159/62500000000 : ℝ) (62204300319/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66795/524288 : ℝ))) 2 (50465323489/100000000000 : ℝ) (31540827181/62500000000 : ℝ) (31102150159/62500000000 : ℝ) (62204300319/125000000000 : ℝ) (501143818717/1000000000000 : ℝ) (125285954681/250000000000 : ℝ) (250565765337/500000000000 : ℝ) (250565765341/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66795/524288 : ℝ))) 3 (501143818717/1000000000000 : ℝ) (125285954681/250000000000 : ℝ) (250565765337/500000000000 : ℝ) (250565765341/500000000000 : ℝ) (100227534939/200000000000 : ℝ) (501137674703/1000000000000 : ℝ) (501137674657/1000000000000 : ℝ) (250568837333/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66795/524288 : ℝ))) 4 (100227534939/200000000000 : ℝ) (501137674703/1000000000000 : ℝ) (501137674657/1000000000000 : ℝ) (250568837333/500000000000 : ℝ) (125284418669/250000000000 : ℝ) (100227534937/200000000000 : ℝ) (20045506987/40000000000 : ℝ) (100227534937/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66795/524288 : ℝ))) 5 (125284418669/250000000000 : ℝ) (100227534937/200000000000 : ℝ) (20045506987/40000000000 : ℝ) (100227534937/200000000000 : ℝ) (20045506987/40000000000 : ℝ) (100227534937/200000000000 : ℝ) (20045506987/40000000000 : ℝ) (100227534937/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66795/524288 : ℝ))) 6 (20045506987/40000000000 : ℝ) (100227534937/200000000000 : ℝ) (20045506987/40000000000 : ℝ) (100227534937/200000000000 : ℝ) (20045506987/40000000000 : ℝ) (100227534937/200000000000 : ℝ) (20045506987/40000000000 : ℝ) (100227534937/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66795/524288 : ℝ))) 7 (20045506987/40000000000 : ℝ) (100227534937/200000000000 : ℝ) (20045506987/40000000000 : ℝ) (100227534937/200000000000 : ℝ) (20045506987/40000000000 : ℝ) (100227534937/200000000000 : ℝ) (20045506987/40000000000 : ℝ) (100227534937/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66795/524288 : ℝ)) hmem 8 (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ) (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66795/524288 : ℝ))) hcmem 8 (20045506987/40000000000 : ℝ) (100227534937/200000000000 : ℝ) (20045506987/40000000000 : ℝ) (100227534937/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66795/524288 : ℝ)) (496042378951/500000000000 : ℝ) (198416951581/200000000000 : ℝ) (20045506987/40000000000 : ℝ) (100227534937/200000000000 : ℝ) (793465691641/1000000000000 : ℝ) (39673284583/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0722_exp_lower
  have heNumeric : (2054901909159/1000000000000 : ℝ)/4 ≤ Real.exp (-8525647962623/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901909159/1000000000000 : ℝ)/4 ≤ Real.exp ((33397/262144 : ℝ)-(39673284583/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33397/262144 : ℝ) (66795/524288 : ℝ) (39673284583/50000000000 : ℝ) (2054901909159/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0723; no trusted numerical premise.
theorem cover8_leaf0723_exp_radius : (31187853254843599/31250000000000000 : ℝ) ≤ Real.exp ((-16699/1048576 : ℝ)/8) ∧ Real.exp ((-16699/1048576 : ℝ)/8) ≤ (998011304154995169/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16699/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0723_exp_lower : (460056734250047837/500000000000000000 : ℝ) ≤ Real.exp ((-85256479967269/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256479967269/128000000000000 : ℝ)/8) ≤ (36804538740003827/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256479967269/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0723_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725475921/250000000000 : ℝ) ≤ 4*Real.exp (66795/524288 : ℝ)*Real.exp (-mu (radius 8 (16699/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513725475921/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16699/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0723_exp_radius
  have hrNumeric : (984200731399/1000000000000 : ℝ) ≤ Real.exp (-16699/1048576 : ℝ) ∧ Real.exp (-16699/1048576 : ℝ) ≤ (4921003657/5000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984200731399/1000000000000 : ℝ) ≤ (radius 8 (16699/131072 : ℝ)) ∧ (radius 8 (16699/131072 : ℝ)) ≤ (4921003657/5000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16699/131072 : ℝ)) (984200731399/1000000000000 : ℝ) (4921003657/5000000000 : ℝ) (44264065781/250000000000 : ℝ) (177056263131/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16699/131072 : ℝ)) (984200731399/1000000000000 : ℝ) (4921003657/5000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16699/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984200731399/1000000000000 : ℝ) (4921003657/5000000000 : ℝ) (992100365699/1000000000000 : ℝ) (9921003657/10000000000 : ℝ) (496034457321/500000000000 : ℝ) (992068914643/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16699/131072 : ℝ)) 1 (992100365699/1000000000000 : ℝ) (9921003657/10000000000 : ℝ) (496034457321/500000000000 : ℝ) (992068914643/1000000000000 : ℝ) (99208464017/100000000000 : ℝ) (248021160043/250000000000 : ℝ) (198416928009/200000000000 : ℝ) (992084640047/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16699/131072 : ℝ)) 2 (99208464017/100000000000 : ℝ) (248021160043/250000000000 : ℝ) (198416928009/200000000000 : ℝ) (992084640047/1000000000000 : ℝ) (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ) (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16699/131072 : ℝ)) 3 (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ) (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ) (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ) (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16699/131072 : ℝ)) 4 (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ) (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ) (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ) (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16699/131072 : ℝ)) 5 (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ) (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ) (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ) (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16699/131072 : ℝ)) 6 (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ) (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ) (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ) (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16699/131072 : ℝ)) 7 (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ) (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ) (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ) (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16699/131072 : ℝ))) (44264065781/250000000000 : ℝ) (177056263131/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16699/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44264065781/250000000000 : ℝ) (177056263131/1000000000000 : ℝ) (294264065781/500000000000 : ℝ) (294264065783/500000000000 : ℝ) (210390270167/500000000000 : ℝ) (420780540343/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16699/131072 : ℝ))) 1 (294264065781/500000000000 : ℝ) (294264065783/500000000000 : ℝ) (210390270167/500000000000 : ℝ) (420780540343/1000000000000 : ℝ) (126163583987/250000000000 : ℝ) (100930867191/200000000000 : ℝ) (124408898697/250000000000 : ℝ) (124408898699/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16699/131072 : ℝ))) 2 (126163583987/250000000000 : ℝ) (100930867191/200000000000 : ℝ) (124408898697/250000000000 : ℝ) (124408898699/250000000000 : ℝ) (62643120671/125000000000 : ℝ) (1957597521/3906250000 : ℝ) (501132677673/1000000000000 : ℝ) (501132677681/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16699/131072 : ℝ))) 3 (62643120671/125000000000 : ℝ) (1957597521/3906250000 : ℝ) (501132677673/1000000000000 : ℝ) (501132677681/1000000000000 : ℝ) (6264235269/12500000000 : ℝ) (501138821529/1000000000000 : ℝ) (250569410741/500000000000 : ℝ) (501138821491/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16699/131072 : ℝ))) 4 (6264235269/12500000000 : ℝ) (501138821529/1000000000000 : ℝ) (250569410741/500000000000 : ℝ) (501138821491/1000000000000 : ℝ) (501138821501/1000000000000 : ℝ) (50113882151/100000000000 : ℝ) (1002277643/2000000000 : ℝ) (50113882151/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16699/131072 : ℝ))) 5 (501138821501/1000000000000 : ℝ) (50113882151/100000000000 : ℝ) (1002277643/2000000000 : ℝ) (50113882151/100000000000 : ℝ) (1002277643/2000000000 : ℝ) (50113882151/100000000000 : ℝ) (1002277643/2000000000 : ℝ) (50113882151/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16699/131072 : ℝ))) 6 (1002277643/2000000000 : ℝ) (50113882151/100000000000 : ℝ) (1002277643/2000000000 : ℝ) (50113882151/100000000000 : ℝ) (1002277643/2000000000 : ℝ) (50113882151/100000000000 : ℝ) (1002277643/2000000000 : ℝ) (50113882151/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16699/131072 : ℝ))) 7 (1002277643/2000000000 : ℝ) (50113882151/100000000000 : ℝ) (1002277643/2000000000 : ℝ) (50113882151/100000000000 : ℝ) (1002277643/2000000000 : ℝ) (50113882151/100000000000 : ℝ) (1002277643/2000000000 : ℝ) (50113882151/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16699/131072 : ℝ)) hmem 8 (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ) (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16699/131072 : ℝ))) hcmem 8 (1002277643/2000000000 : ℝ) (50113882151/100000000000 : ℝ) (1002277643/2000000000 : ℝ) (50113882151/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16699/131072 : ℝ)) (992084640107/1000000000000 : ℝ) (99208464011/100000000000 : ℝ) (1002277643/2000000000 : ℝ) (50113882151/100000000000 : ℝ) (396733800827/500000000000 : ℝ) (793467601673/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0723_exp_lower
  have heNumeric : (513725475921/250000000000 : ℝ)/4 ≤ Real.exp (-85256479967269/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725475921/250000000000 : ℝ)/4 ≤ Real.exp ((66795/524288 : ℝ)-(793467601673/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66795/524288 : ℝ) (16699/131072 : ℝ) (793467601673/1000000000000 : ℝ) (513725475921/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0724; no trusted numerical premise.
theorem cover8_leaf0724_exp_radius : (499005637205970489/500000000000000000 : ℝ) ≤ Real.exp ((-66797/4194304 : ℝ)/8) ∧ Real.exp ((-66797/4194304 : ℝ)/8) ≤ (998011274411940979/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66797/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0724_exp_lower : (920113468195840927/1000000000000000000 : ℝ) ≤ Real.exp ((-21314120076469/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314120076469/32000000000000 : ℝ)/8) ≤ (28753545881120029/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314120076469/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0724_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862737281/125000000000 : ℝ) ≤ 4*Real.exp (16699/131072 : ℝ)*Real.exp (-mu (radius 8 (66797/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862737281/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66797/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0724_exp_radius
  have hrNumeric : (984200496747/1000000000000 : ℝ) ≤ Real.exp (-66797/4194304 : ℝ) ∧ Real.exp (-66797/4194304 : ℝ) ≤ (246050124187/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984200496747/1000000000000 : ℝ) ≤ (radius 8 (66797/524288 : ℝ)) ∧ (radius 8 (66797/524288 : ℝ)) ≤ (246050124187/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66797/524288 : ℝ)) (984200496747/1000000000000 : ℝ) (246050124187/250000000000 : ℝ) (177057567477/1000000000000 : ℝ) (177057567483/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66797/524288 : ℝ)) (984200496747/1000000000000 : ℝ) (246050124187/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66797/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984200496747/1000000000000 : ℝ) (246050124187/250000000000 : ℝ) (992100248373/1000000000000 : ℝ) (496050124187/500000000000 : ℝ) (496034398189/500000000000 : ℝ) (992068796379/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66797/524288 : ℝ)) 1 (992100248373/1000000000000 : ℝ) (496050124187/500000000000 : ℝ) (496034398189/500000000000 : ℝ) (992068796379/1000000000000 : ℝ) (7936676179/8000000000 : ℝ) (992084522377/1000000000000 : ℝ) (3968338089/4000000000 : ℝ) (248021130563/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66797/524288 : ℝ)) 2 (7936676179/8000000000 : ℝ) (992084522377/1000000000000 : ℝ) (3968338089/4000000000 : ℝ) (248021130563/250000000000 : ℝ) (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ) (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66797/524288 : ℝ)) 3 (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ) (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ) (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ) (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66797/524288 : ℝ)) 4 (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ) (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ) (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ) (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66797/524288 : ℝ)) 5 (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ) (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ) (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ) (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66797/524288 : ℝ)) 6 (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ) (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ) (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ) (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66797/524288 : ℝ)) 7 (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ) (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ) (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ) (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66797/524288 : ℝ))) (177057567477/1000000000000 : ℝ) (177057567483/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66797/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177057567477/1000000000000 : ℝ) (177057567483/1000000000000 : ℝ) (294264391869/500000000000 : ℝ) (294264391871/500000000000 : ℝ) (105195522563/250000000000 : ℝ) (21039104513/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66797/524288 : ℝ))) 1 (294264391869/500000000000 : ℝ) (294264391871/500000000000 : ℝ) (105195522563/250000000000 : ℝ) (21039104513/50000000000 : ℝ) (100931087399/200000000000 : ℝ) (504655437001/1000000000000 : ℝ) (497636787019/1000000000000 : ℝ) (248818393513/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66797/524288 : ℝ))) 2 (100931087399/200000000000 : ℝ) (504655437001/1000000000000 : ℝ) (497636787019/1000000000000 : ℝ) (248818393513/500000000000 : ℝ) (501146112007/1000000000000 : ℝ) (250573056007/500000000000 : ℝ) (501133824659/1000000000000 : ℝ) (501133824667/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66797/524288 : ℝ))) 3 (501146112007/1000000000000 : ℝ) (250573056007/500000000000 : ℝ) (501133824659/1000000000000 : ℝ) (501133824667/1000000000000 : ℝ) (501139968333/1000000000000 : ℝ) (501139968341/1000000000000 : ℝ) (100227993659/200000000000 : ℝ) (501139968303/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66797/524288 : ℝ))) 4 (501139968333/1000000000000 : ℝ) (501139968341/1000000000000 : ℝ) (100227993659/200000000000 : ℝ) (501139968303/1000000000000 : ℝ) (250569984157/500000000000 : ℝ) (250569984161/500000000000 : ℝ) (501139968313/1000000000000 : ℝ) (250569984161/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66797/524288 : ℝ))) 5 (250569984157/500000000000 : ℝ) (250569984161/500000000000 : ℝ) (501139968313/1000000000000 : ℝ) (250569984161/500000000000 : ℝ) (501139968313/1000000000000 : ℝ) (250569984161/500000000000 : ℝ) (501139968313/1000000000000 : ℝ) (250569984161/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66797/524288 : ℝ))) 6 (501139968313/1000000000000 : ℝ) (250569984161/500000000000 : ℝ) (501139968313/1000000000000 : ℝ) (250569984161/500000000000 : ℝ) (501139968313/1000000000000 : ℝ) (250569984161/500000000000 : ℝ) (501139968313/1000000000000 : ℝ) (250569984161/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66797/524288 : ℝ))) 7 (501139968313/1000000000000 : ℝ) (250569984161/500000000000 : ℝ) (501139968313/1000000000000 : ℝ) (250569984161/500000000000 : ℝ) (501139968313/1000000000000 : ℝ) (250569984161/500000000000 : ℝ) (501139968313/1000000000000 : ℝ) (250569984161/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66797/524288 : ℝ)) hmem 8 (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ) (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66797/524288 : ℝ))) hcmem 8 (501139968313/1000000000000 : ℝ) (250569984161/500000000000 : ℝ) (501139968313/1000000000000 : ℝ) (250569984161/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66797/524288 : ℝ)) (124010565289/125000000000 : ℝ) (198416904463/200000000000 : ℝ) (501139968313/1000000000000 : ℝ) (250569984161/500000000000 : ℝ) (793469511649/1000000000000 : ℝ) (793469511667/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0724_exp_lower
  have heNumeric : (256862737281/125000000000 : ℝ)/4 ≤ Real.exp (-21314120076469/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862737281/125000000000 : ℝ)/4 ≤ Real.exp ((16699/131072 : ℝ)-(793469511667/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16699/131072 : ℝ) (66797/524288 : ℝ) (793469511667/1000000000000 : ℝ) (256862737281/125000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0700_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0700_certificate
#check SmaleRate.Proofs.cover8_leaf0701_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0701_certificate
#check SmaleRate.Proofs.cover8_leaf0702_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0702_certificate
#check SmaleRate.Proofs.cover8_leaf0703_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0703_certificate
#check SmaleRate.Proofs.cover8_leaf0704_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0704_certificate
#check SmaleRate.Proofs.cover8_leaf0705_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0705_certificate
#check SmaleRate.Proofs.cover8_leaf0706_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0706_certificate
#check SmaleRate.Proofs.cover8_leaf0707_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0707_certificate
#check SmaleRate.Proofs.cover8_leaf0708_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0708_certificate
#check SmaleRate.Proofs.cover8_leaf0709_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0709_certificate
#check SmaleRate.Proofs.cover8_leaf0710_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0710_certificate
#check SmaleRate.Proofs.cover8_leaf0711_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0711_certificate
#check SmaleRate.Proofs.cover8_leaf0712_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0712_certificate
#check SmaleRate.Proofs.cover8_leaf0713_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0713_certificate
#check SmaleRate.Proofs.cover8_leaf0714_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0714_certificate
#check SmaleRate.Proofs.cover8_leaf0715_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0715_certificate
#check SmaleRate.Proofs.cover8_leaf0716_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0716_certificate
#check SmaleRate.Proofs.cover8_leaf0717_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0717_certificate
#check SmaleRate.Proofs.cover8_leaf0718_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0718_certificate
#check SmaleRate.Proofs.cover8_leaf0719_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0719_certificate
#check SmaleRate.Proofs.cover8_leaf0720_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0720_certificate
#check SmaleRate.Proofs.cover8_leaf0721_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0721_certificate
#check SmaleRate.Proofs.cover8_leaf0722_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0722_certificate
#check SmaleRate.Proofs.cover8_leaf0723_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0723_certificate
#check SmaleRate.Proofs.cover8_leaf0724_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0724_certificate
