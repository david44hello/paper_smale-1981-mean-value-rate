/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0350; no trusted numerical premise.
theorem cover8_leaf0350_exp_radius : (998027187072552721/1000000000000000000 : ℝ) ≤ Real.exp ((-33131/2097152 : ℝ)/8) ∧ Real.exp ((-33131/2097152 : ℝ)/8) ≤ (499013593536276361/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33131/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0350_exp_lower : (460056865827583413/500000000000000000 : ℝ) ≤ Real.exp ((-21314046775099/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314046775099/32000000000000 : ℝ)/8) ≤ (920113731655166827/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314046775099/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0350_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906605351/1000000000000 : ℝ) ≤ 4*Real.exp (16565/131072 : ℝ)*Real.exp (-mu (radius 8 (33131/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906605351/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33131/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0350_exp_radius
  have hrNumeric : (196865208681/200000000000 : ℝ) ≤ Real.exp (-33131/2097152 : ℝ) ∧ Real.exp (-33131/2097152 : ℝ) ≤ (492163021703/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196865208681/200000000000 : ℝ) ≤ (radius 8 (33131/262144 : ℝ)) ∧ (radius 8 (33131/262144 : ℝ)) ≤ (492163021703/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33131/262144 : ℝ)) (196865208681/200000000000 : ℝ) (492163021703/500000000000 : ℝ) (176358272481/1000000000000 : ℝ) (22044784061/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33131/262144 : ℝ)) (196865208681/200000000000 : ℝ) (492163021703/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33131/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196865208681/200000000000 : ℝ) (492163021703/500000000000 : ℝ) (496081510851/500000000000 : ℝ) (992163021703/1000000000000 : ℝ) (992132069537/1000000000000 : ℝ) (992132069539/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33131/262144 : ℝ)) 1 (496081510851/500000000000 : ℝ) (992163021703/1000000000000 : ℝ) (992132069537/1000000000000 : ℝ) (992132069539/1000000000000 : ℝ) (992147545619/1000000000000 : ℝ) (992147545621/1000000000000 : ℝ) (496073772749/500000000000 : ℝ) (992147545501/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33131/262144 : ℝ)) 2 (992147545619/1000000000000 : ℝ) (992147545621/1000000000000 : ℝ) (496073772749/500000000000 : ℝ) (992147545501/1000000000000 : ℝ) (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ) (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33131/262144 : ℝ)) 3 (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ) (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ) (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ) (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33131/262144 : ℝ)) 4 (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ) (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ) (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ) (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33131/262144 : ℝ)) 5 (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ) (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ) (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ) (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33131/262144 : ℝ)) 6 (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ) (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ) (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ) (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33131/262144 : ℝ)) 7 (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ) (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ) (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ) (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33131/262144 : ℝ))) (176358272481/1000000000000 : ℝ) (22044784061/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33131/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176358272481/1000000000000 : ℝ) (22044784061/125000000000 : ℝ) (7352239203/12500000000 : ℝ) (147044784061/250000000000 : ℝ) (104987580361/250000000000 : ℝ) (419950321453/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33131/262144 : ℝ))) 1 (7352239203/12500000000 : ℝ) (147044784061/250000000000 : ℝ) (104987580361/250000000000 : ℝ) (419950321453/1000000000000 : ℝ) (252032364421/500000000000 : ℝ) (504064728849/1000000000000 : ℝ) (496996999317/1000000000000 : ℝ) (19879879973/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33131/262144 : ℝ))) 2 (252032364421/500000000000 : ℝ) (504064728849/1000000000000 : ℝ) (496996999317/1000000000000 : ℝ) (19879879973/40000000000 : ℝ) (500530864079/1000000000000 : ℝ) (500530864087/1000000000000 : ℝ) (62564798621/125000000000 : ℝ) (500518388977/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33131/262144 : ℝ))) 3 (500530864079/1000000000000 : ℝ) (500530864087/1000000000000 : ℝ) (62564798621/125000000000 : ℝ) (500518388977/1000000000000 : ℝ) (500524626523/1000000000000 : ℝ) (125131156633/250000000000 : ℝ) (125131156621/250000000000 : ℝ) (250262313247/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33131/262144 : ℝ))) 4 (500524626523/1000000000000 : ℝ) (125131156633/250000000000 : ℝ) (125131156621/250000000000 : ℝ) (250262313247/500000000000 : ℝ) (500524626503/1000000000000 : ℝ) (500524626513/1000000000000 : ℝ) (500524626503/1000000000000 : ℝ) (500524626513/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33131/262144 : ℝ))) 5 (500524626503/1000000000000 : ℝ) (500524626513/1000000000000 : ℝ) (500524626503/1000000000000 : ℝ) (500524626513/1000000000000 : ℝ) (500524626503/1000000000000 : ℝ) (500524626513/1000000000000 : ℝ) (500524626503/1000000000000 : ℝ) (500524626513/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33131/262144 : ℝ))) 6 (500524626503/1000000000000 : ℝ) (500524626513/1000000000000 : ℝ) (500524626503/1000000000000 : ℝ) (500524626513/1000000000000 : ℝ) (500524626503/1000000000000 : ℝ) (500524626513/1000000000000 : ℝ) (500524626503/1000000000000 : ℝ) (500524626513/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33131/262144 : ℝ))) 7 (500524626503/1000000000000 : ℝ) (500524626513/1000000000000 : ℝ) (500524626503/1000000000000 : ℝ) (500524626513/1000000000000 : ℝ) (500524626503/1000000000000 : ℝ) (500524626513/1000000000000 : ℝ) (500524626503/1000000000000 : ℝ) (500524626513/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33131/262144 : ℝ)) hmem 8 (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ) (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33131/262144 : ℝ))) hcmem 8 (500524626503/1000000000000 : ℝ) (500524626513/1000000000000 : ℝ) (500524626503/1000000000000 : ℝ) (500524626513/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33131/262144 : ℝ)) (496073772779/500000000000 : ℝ) (992147545561/1000000000000 : ℝ) (500524626503/1000000000000 : ℝ) (500524626513/1000000000000 : ℝ) (792444882113/1000000000000 : ℝ) (198111220533/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0350_exp_lower
  have heNumeric : (2054906605351/1000000000000 : ℝ)/4 ≤ Real.exp (-21314046775099/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906605351/1000000000000 : ℝ)/4 ≤ Real.exp ((16565/131072 : ℝ)-(198111220533/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16565/131072 : ℝ) (33131/262144 : ℝ) (198111220533/250000000000 : ℝ) (2054906605351/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0351; no trusted numerical premise.
theorem cover8_leaf0351_exp_radius : (249506781896374633/250000000000000000 : ℝ) ≤ Real.exp ((-8283/524288 : ℝ)/8) ∧ Real.exp ((-8283/524288 : ℝ)/8) ≤ (998027127585498533/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8283/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0351_exp_lower : (460056864324937953/500000000000000000 : ℝ) ≤ Real.exp ((-42628095222501/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628095222501/64000000000000 : ℝ)/8) ≤ (920113728649875907/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628095222501/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0351_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906551657/1000000000000 : ℝ) ≤ 4*Real.exp (33131/262144 : ℝ)*Real.exp (-mu (radius 8 (8283/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906551657/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8283/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0351_exp_radius
  have hrNumeric : (492162787021/500000000000 : ℝ) ≤ Real.exp (-8283/524288 : ℝ) ∧ Real.exp (-8283/524288 : ℝ) ≤ (984325574043/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492162787021/500000000000 : ℝ) ≤ (radius 8 (8283/65536 : ℝ)) ∧ (radius 8 (8283/65536 : ℝ)) ≤ (984325574043/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8283/65536 : ℝ)) (492162787021/500000000000 : ℝ) (984325574043/1000000000000 : ℝ) (44090223041/250000000000 : ℝ) (17636089217/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8283/65536 : ℝ)) (492162787021/500000000000 : ℝ) (984325574043/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8283/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492162787021/500000000000 : ℝ) (984325574043/1000000000000 : ℝ) (992162787021/1000000000000 : ℝ) (496081393511/500000000000 : ℝ) (496065916497/500000000000 : ℝ) (248032958249/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8283/65536 : ℝ)) 1 (992162787021/1000000000000 : ℝ) (496081393511/500000000000 : ℝ) (496065916497/500000000000 : ℝ) (248032958249/250000000000 : ℝ) (992147310007/1000000000000 : ℝ) (992147310009/1000000000000 : ℝ) (496073654943/500000000000 : ℝ) (992147309889/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8283/65536 : ℝ)) 2 (992147310007/1000000000000 : ℝ) (992147310009/1000000000000 : ℝ) (496073654943/500000000000 : ℝ) (992147309889/1000000000000 : ℝ) (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ) (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8283/65536 : ℝ)) 3 (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ) (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ) (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ) (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8283/65536 : ℝ)) 4 (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ) (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ) (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ) (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8283/65536 : ℝ)) 5 (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ) (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ) (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ) (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8283/65536 : ℝ)) 6 (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ) (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ) (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ) (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8283/65536 : ℝ)) 7 (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ) (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ) (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ) (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8283/65536 : ℝ))) (44090223041/250000000000 : ℝ) (17636089217/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8283/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44090223041/250000000000 : ℝ) (17636089217/100000000000 : ℝ) (294090223041/500000000000 : ℝ) (117636089217/200000000000 : ℝ) (419953440471/1000000000000 : ℝ) (419953440479/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8283/65536 : ℝ))) 1 (294090223041/500000000000 : ℝ) (117636089217/200000000000 : ℝ) (419953440471/1000000000000 : ℝ) (419953440479/1000000000000 : ℝ) (126016735819/250000000000 : ℝ) (252033471641/500000000000 : ℝ) (496999398339/1000000000000 : ℝ) (248499699173/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8283/65536 : ℝ))) 2 (126016735819/250000000000 : ℝ) (252033471641/500000000000 : ℝ) (496999398339/1000000000000 : ℝ) (248499699173/500000000000 : ℝ) (500533170807/1000000000000 : ℝ) (250266585407/500000000000 : ℝ) (250260348203/500000000000 : ℝ) (500520696413/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8283/65536 : ℝ))) 3 (500533170807/1000000000000 : ℝ) (250266585407/500000000000 : ℝ) (250260348203/500000000000 : ℝ) (500520696413/1000000000000 : ℝ) (250263466803/500000000000 : ℝ) (250263466807/500000000000 : ℝ) (500526933567/1000000000000 : ℝ) (20021077343/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8283/65536 : ℝ))) 4 (250263466803/500000000000 : ℝ) (250263466807/500000000000 : ℝ) (500526933567/1000000000000 : ℝ) (20021077343/40000000000 : ℝ) (250263466793/500000000000 : ℝ) (100105386719/200000000000 : ℝ) (250263466793/500000000000 : ℝ) (100105386719/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8283/65536 : ℝ))) 5 (250263466793/500000000000 : ℝ) (100105386719/200000000000 : ℝ) (250263466793/500000000000 : ℝ) (100105386719/200000000000 : ℝ) (250263466793/500000000000 : ℝ) (100105386719/200000000000 : ℝ) (250263466793/500000000000 : ℝ) (100105386719/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8283/65536 : ℝ))) 6 (250263466793/500000000000 : ℝ) (100105386719/200000000000 : ℝ) (250263466793/500000000000 : ℝ) (100105386719/200000000000 : ℝ) (250263466793/500000000000 : ℝ) (100105386719/200000000000 : ℝ) (250263466793/500000000000 : ℝ) (100105386719/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8283/65536 : ℝ))) 7 (250263466793/500000000000 : ℝ) (100105386719/200000000000 : ℝ) (250263466793/500000000000 : ℝ) (100105386719/200000000000 : ℝ) (250263466793/500000000000 : ℝ) (100105386719/200000000000 : ℝ) (250263466793/500000000000 : ℝ) (100105386719/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8283/65536 : ℝ)) hmem 8 (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ) (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8283/65536 : ℝ))) hcmem 8 (250263466793/500000000000 : ℝ) (100105386719/200000000000 : ℝ) (250263466793/500000000000 : ℝ) (100105386719/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8283/65536 : ℝ)) (496073654973/500000000000 : ℝ) (992147309949/1000000000000 : ℝ) (250263466793/500000000000 : ℝ) (100105386719/200000000000 : ℝ) (792448722941/1000000000000 : ℝ) (792448722959/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0351_exp_lower
  have heNumeric : (2054906551657/1000000000000 : ℝ)/4 ≤ Real.exp (-42628095222501/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906551657/1000000000000 : ℝ)/4 ≤ Real.exp ((33131/262144 : ℝ)-(792448722959/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33131/262144 : ℝ) (8283/65536 : ℝ) (792448722959/1000000000000 : ℝ) (2054906551657/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0352; no trusted numerical premise.
theorem cover8_leaf0352_exp_radius : (998027068098447889/1000000000000000000 : ℝ) ≤ Real.exp ((-33133/2097152 : ℝ)/8) ∧ Real.exp ((-33133/2097152 : ℝ)/8) ≤ (99802706809844789/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33133/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0352_exp_lower : (920113725653211061/1000000000000000000 : ℝ) ≤ Real.exp ((-10657024222501/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657024222501/16000000000000 : ℝ)/8) ≤ (460056862826605531/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657024222501/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0352_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906498117/1000000000000 : ℝ) ≤ 4*Real.exp (8283/65536 : ℝ)*Real.exp (-mu (radius 8 (33133/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906498117/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33133/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0352_exp_radius
  have hrNumeric : (984325104679/1000000000000 : ℝ) ≤ Real.exp (-33133/2097152 : ℝ) ∧ Real.exp (-33133/2097152 : ℝ) ≤ (24608127617/25000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984325104679/1000000000000 : ℝ) ≤ (radius 8 (33133/262144 : ℝ)) ∧ (radius 8 (33133/262144 : ℝ)) ≤ (24608127617/25000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33133/262144 : ℝ)) (984325104679/1000000000000 : ℝ) (24608127617/25000000000 : ℝ) (88181755903/500000000000 : ℝ) (176363511813/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33133/262144 : ℝ)) (984325104679/1000000000000 : ℝ) (24608127617/25000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33133/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984325104679/1000000000000 : ℝ) (24608127617/25000000000 : ℝ) (992162552339/1000000000000 : ℝ) (49608127617/50000000000 : ℝ) (248032899113/250000000000 : ℝ) (992131596453/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33133/262144 : ℝ)) 1 (992162552339/1000000000000 : ℝ) (49608127617/50000000000 : ℝ) (248032899113/250000000000 : ℝ) (992131596453/1000000000000 : ℝ) (198429414879/200000000000 : ℝ) (992147074397/1000000000000 : ℝ) (496073537137/500000000000 : ℝ) (248036768569/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33133/262144 : ℝ)) 2 (198429414879/200000000000 : ℝ) (992147074397/1000000000000 : ℝ) (496073537137/500000000000 : ℝ) (248036768569/250000000000 : ℝ) (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ) (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33133/262144 : ℝ)) 3 (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ) (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ) (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ) (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33133/262144 : ℝ)) 4 (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ) (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ) (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ) (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33133/262144 : ℝ)) 5 (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ) (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ) (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ) (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33133/262144 : ℝ)) 6 (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ) (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ) (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ) (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33133/262144 : ℝ)) 7 (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ) (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ) (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ) (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33133/262144 : ℝ))) (88181755903/500000000000 : ℝ) (176363511813/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33133/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88181755903/500000000000 : ℝ) (176363511813/1000000000000 : ℝ) (588181755903/1000000000000 : ℝ) (588181755907/1000000000000 : ℝ) (419956559427/1000000000000 : ℝ) (104989139859/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33133/262144 : ℝ))) 1 (588181755903/1000000000000 : ℝ) (588181755907/1000000000000 : ℝ) (419956559427/1000000000000 : ℝ) (104989139859/250000000000 : ℝ) (100813831533/200000000000 : ℝ) (63008644709/125000000000 : ℝ) (497001797307/1000000000000 : ℝ) (99400359463/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33133/262144 : ℝ))) 2 (100813831533/200000000000 : ℝ) (63008644709/125000000000 : ℝ) (497001797307/1000000000000 : ℝ) (99400359463/200000000000 : ℝ) (250267738743/500000000000 : ℝ) (250267738747/500000000000 : ℝ) (500523003793/1000000000000 : ℝ) (250261501901/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33133/262144 : ℝ))) 3 (250267738743/500000000000 : ℝ) (250267738747/500000000000 : ℝ) (500523003793/1000000000000 : ℝ) (250261501901/500000000000 : ℝ) (500529240639/1000000000000 : ℝ) (62566155081/125000000000 : ℝ) (2502646203/5000000000 : ℝ) (50052924061/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33133/262144 : ℝ))) 4 (500529240639/1000000000000 : ℝ) (62566155081/125000000000 : ℝ) (2502646203/5000000000 : ℝ) (50052924061/100000000000 : ℝ) (500529240619/1000000000000 : ℝ) (500529240629/1000000000000 : ℝ) (500529240619/1000000000000 : ℝ) (500529240629/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33133/262144 : ℝ))) 5 (500529240619/1000000000000 : ℝ) (500529240629/1000000000000 : ℝ) (500529240619/1000000000000 : ℝ) (500529240629/1000000000000 : ℝ) (500529240619/1000000000000 : ℝ) (500529240629/1000000000000 : ℝ) (500529240619/1000000000000 : ℝ) (500529240629/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33133/262144 : ℝ))) 6 (500529240619/1000000000000 : ℝ) (500529240629/1000000000000 : ℝ) (500529240619/1000000000000 : ℝ) (500529240629/1000000000000 : ℝ) (500529240619/1000000000000 : ℝ) (500529240629/1000000000000 : ℝ) (500529240619/1000000000000 : ℝ) (500529240629/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33133/262144 : ℝ))) 7 (500529240619/1000000000000 : ℝ) (500529240629/1000000000000 : ℝ) (500529240619/1000000000000 : ℝ) (500529240629/1000000000000 : ℝ) (500529240619/1000000000000 : ℝ) (500529240629/1000000000000 : ℝ) (500529240619/1000000000000 : ℝ) (500529240629/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33133/262144 : ℝ)) hmem 8 (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ) (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33133/262144 : ℝ))) hcmem 8 (500529240619/1000000000000 : ℝ) (500529240629/1000000000000 : ℝ) (500529240619/1000000000000 : ℝ) (500529240629/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33133/262144 : ℝ)) (496073537167/500000000000 : ℝ) (992147074337/1000000000000 : ℝ) (500529240619/1000000000000 : ℝ) (500529240629/1000000000000 : ℝ) (792452563691/1000000000000 : ℝ) (792452563711/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0352_exp_lower
  have heNumeric : (2054906498117/1000000000000 : ℝ)/4 ≤ Real.exp (-10657024222501/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906498117/1000000000000 : ℝ)/4 ≤ Real.exp ((8283/65536 : ℝ)-(792452563711/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8283/65536 : ℝ) (33133/262144 : ℝ) (792452563711/1000000000000 : ℝ) (2054906498117/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0353; no trusted numerical premise.
theorem cover8_leaf0353_exp_radius : (124753376076425099/125000000000000000 : ℝ) ≤ Real.exp ((-16567/1048576 : ℝ)/8) ∧ Real.exp ((-16567/1048576 : ℝ)/8) ≤ (998027008611400793/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16567/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0353_exp_lower : (920113722665632349/1000000000000000000 : ℝ) ≤ Real.exp ((-42628098552451/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628098552451/64000000000000 : ℝ)/8) ≤ (18402274453312647/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628098552451/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0353_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906444739/1000000000000 : ℝ) ≤ 4*Real.exp (33133/262144 : ℝ)*Real.exp (-mu (radius 8 (16567/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906444739/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16567/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0353_exp_radius
  have hrNumeric : (246081158829/250000000000 : ℝ) ≤ Real.exp (-16567/1048576 : ℝ) ∧ Real.exp (-16567/1048576 : ℝ) ≤ (984324635317/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246081158829/250000000000 : ℝ) ≤ (radius 8 (16567/131072 : ℝ)) ∧ (radius 8 (16567/131072 : ℝ)) ≤ (984324635317/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16567/131072 : ℝ)) (246081158829/250000000000 : ℝ) (984324635317/1000000000000 : ℝ) (11022883213/62500000000 : ℝ) (35273226283/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16567/131072 : ℝ)) (246081158829/250000000000 : ℝ) (984324635317/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16567/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246081158829/250000000000 : ℝ) (984324635317/1000000000000 : ℝ) (496081158829/500000000000 : ℝ) (992162317659/1000000000000 : ℝ) (992131359909/1000000000000 : ℝ) (992131359911/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16567/131072 : ℝ)) 1 (496081158829/500000000000 : ℝ) (992162317659/1000000000000 : ℝ) (992131359909/1000000000000 : ℝ) (992131359911/1000000000000 : ℝ) (992146838783/1000000000000 : ℝ) (198429367757/200000000000 : ℝ) (496073419331/500000000000 : ℝ) (198429367733/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16567/131072 : ℝ)) 2 (992146838783/1000000000000 : ℝ) (198429367757/200000000000 : ℝ) (496073419331/500000000000 : ℝ) (198429367733/200000000000 : ℝ) (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ) (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16567/131072 : ℝ)) 3 (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ) (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ) (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ) (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16567/131072 : ℝ)) 4 (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ) (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ) (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ) (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16567/131072 : ℝ)) 5 (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ) (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ) (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ) (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16567/131072 : ℝ)) 6 (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ) (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ) (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ) (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16567/131072 : ℝ)) 7 (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ) (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ) (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ) (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16567/131072 : ℝ))) (11022883213/62500000000 : ℝ) (35273226283/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16567/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11022883213/62500000000 : ℝ) (35273226283/200000000000 : ℝ) (73522883213/125000000000 : ℝ) (147045766427/250000000000 : ℝ) (52494959789/125000000000 : ℝ) (419959678321/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16567/131072 : ℝ))) 1 (73522883213/125000000000 : ℝ) (147045766427/250000000000 : ℝ) (52494959789/125000000000 : ℝ) (419959678321/1000000000000 : ℝ) (63008921501/125000000000 : ℝ) (100814274403/200000000000 : ℝ) (497004196221/1000000000000 : ℝ) (497004196229/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16567/131072 : ℝ))) 2 (63008921501/125000000000 : ℝ) (100814274403/200000000000 : ℝ) (497004196221/1000000000000 : ℝ) (497004196229/1000000000000 : ℝ) (250268892057/500000000000 : ℝ) (250268892061/500000000000 : ℝ) (500525311131/1000000000000 : ℝ) (500525311139/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16567/131072 : ℝ))) 3 (250268892057/500000000000 : ℝ) (250268892061/500000000000 : ℝ) (500525311131/1000000000000 : ℝ) (500525311139/1000000000000 : ℝ) (250265773811/500000000000 : ℝ) (500531547631/1000000000000 : ℝ) (500531547583/1000000000000 : ℝ) (62566443449/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16567/131072 : ℝ))) 4 (250265773811/500000000000 : ℝ) (500531547631/1000000000000 : ℝ) (500531547583/1000000000000 : ℝ) (62566443449/125000000000 : ℝ) (250265773801/500000000000 : ℝ) (125132886903/250000000000 : ℝ) (250265773801/500000000000 : ℝ) (125132886903/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16567/131072 : ℝ))) 5 (250265773801/500000000000 : ℝ) (125132886903/250000000000 : ℝ) (250265773801/500000000000 : ℝ) (125132886903/250000000000 : ℝ) (250265773801/500000000000 : ℝ) (125132886903/250000000000 : ℝ) (250265773801/500000000000 : ℝ) (125132886903/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16567/131072 : ℝ))) 6 (250265773801/500000000000 : ℝ) (125132886903/250000000000 : ℝ) (250265773801/500000000000 : ℝ) (125132886903/250000000000 : ℝ) (250265773801/500000000000 : ℝ) (125132886903/250000000000 : ℝ) (250265773801/500000000000 : ℝ) (125132886903/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16567/131072 : ℝ))) 7 (250265773801/500000000000 : ℝ) (125132886903/250000000000 : ℝ) (250265773801/500000000000 : ℝ) (125132886903/250000000000 : ℝ) (250265773801/500000000000 : ℝ) (125132886903/250000000000 : ℝ) (250265773801/500000000000 : ℝ) (125132886903/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16567/131072 : ℝ)) hmem 8 (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ) (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16567/131072 : ℝ))) hcmem 8 (250265773801/500000000000 : ℝ) (125132886903/250000000000 : ℝ) (250265773801/500000000000 : ℝ) (125132886903/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16567/131072 : ℝ)) (496073419361/500000000000 : ℝ) (39685873549/40000000000 : ℝ) (250265773801/500000000000 : ℝ) (125132886903/250000000000 : ℝ) (158491280873/200000000000 : ℝ) (24764262637/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0353_exp_lower
  have heNumeric : (2054906444739/1000000000000 : ℝ)/4 ≤ Real.exp (-42628098552451/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906444739/1000000000000 : ℝ)/4 ≤ Real.exp ((33133/262144 : ℝ)-(24764262637/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33133/262144 : ℝ) (16567/131072 : ℝ) (24764262637/31250000000 : ℝ) (2054906444739/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0354; no trusted numerical premise.
theorem cover8_leaf0354_exp_radius : (24950673728108931/25000000000000000 : ℝ) ≤ Real.exp ((-33135/2097152 : ℝ)/8) ∧ Real.exp ((-33135/2097152 : ℝ)/8) ≤ (998026949124357241/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33135/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0354_exp_lower : (92011371968794487/100000000000000000 : ℝ) ≤ Real.exp ((-21314050104697/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314050104697/32000000000000 : ℝ)/8) ≤ (920113719687944871/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314050104697/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0354_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453195769/500000000000 : ℝ) ≤ 4*Real.exp (16567/131072 : ℝ)*Real.exp (-mu (radius 8 (33135/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453195769/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33135/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0354_exp_radius
  have hrNumeric : (492162082977/500000000000 : ℝ) ≤ Real.exp (-33135/2097152 : ℝ) ∧ Real.exp (-33135/2097152 : ℝ) ≤ (196864833191/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492162082977/500000000000 : ℝ) ≤ (radius 8 (33135/262144 : ℝ)) ∧ (radius 8 (33135/262144 : ℝ)) ≤ (196864833191/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33135/262144 : ℝ)) (492162082977/500000000000 : ℝ) (196864833191/200000000000 : ℝ) (35273750193/200000000000 : ℝ) (176368750971/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33135/262144 : ℝ)) (492162082977/500000000000 : ℝ) (196864833191/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33135/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492162082977/500000000000 : ℝ) (196864833191/200000000000 : ℝ) (992162082977/1000000000000 : ℝ) (496081041489/500000000000 : ℝ) (992131123367/1000000000000 : ℝ) (124016390421/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33135/262144 : ℝ)) 1 (992162082977/1000000000000 : ℝ) (496081041489/500000000000 : ℝ) (992131123367/1000000000000 : ℝ) (124016390421/125000000000 : ℝ) (248036650793/250000000000 : ℝ) (992146603173/1000000000000 : ℝ) (992146603051/1000000000000 : ℝ) (992146603053/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33135/262144 : ℝ)) 2 (248036650793/250000000000 : ℝ) (992146603173/1000000000000 : ℝ) (992146603051/1000000000000 : ℝ) (992146603053/1000000000000 : ℝ) (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ) (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33135/262144 : ℝ)) 3 (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ) (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ) (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ) (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33135/262144 : ℝ)) 4 (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ) (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ) (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ) (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33135/262144 : ℝ)) 5 (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ) (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ) (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ) (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33135/262144 : ℝ)) 6 (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ) (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ) (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ) (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33135/262144 : ℝ)) 7 (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ) (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ) (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ) (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33135/262144 : ℝ))) (35273750193/200000000000 : ℝ) (176368750971/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33135/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35273750193/200000000000 : ℝ) (176368750971/1000000000000 : ℝ) (294092187741/500000000000 : ℝ) (294092187743/500000000000 : ℝ) (1312383741/3125000000 : ℝ) (52495349641/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33135/262144 : ℝ))) 1 (294092187741/500000000000 : ℝ) (294092187743/500000000000 : ℝ) (1312383741/3125000000 : ℝ) (52495349641/125000000000 : ℝ) (504073586301/1000000000000 : ℝ) (504073586307/1000000000000 : ℝ) (124251648769/250000000000 : ℝ) (124251648771/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33135/262144 : ℝ))) 2 (504073586301/1000000000000 : ℝ) (504073586307/1000000000000 : ℝ) (124251648769/250000000000 : ℝ) (124251648771/250000000000 : ℝ) (7820938917/15625000000 : ℝ) (62567511337/125000000000 : ℝ) (250263809207/500000000000 : ℝ) (250263809211/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33135/262144 : ℝ))) 3 (7820938917/15625000000 : ℝ) (62567511337/125000000000 : ℝ) (250263809207/500000000000 : ℝ) (250263809211/500000000000 : ℝ) (500533854551/1000000000000 : ℝ) (500533854559/1000000000000 : ℝ) (31283365907/62500000000 : ℝ) (500533854521/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33135/262144 : ℝ))) 4 (500533854551/1000000000000 : ℝ) (500533854559/1000000000000 : ℝ) (31283365907/62500000000 : ℝ) (500533854521/1000000000000 : ℝ) (500533854531/1000000000000 : ℝ) (25026692727/50000000000 : ℝ) (500533854531/1000000000000 : ℝ) (25026692727/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33135/262144 : ℝ))) 5 (500533854531/1000000000000 : ℝ) (25026692727/50000000000 : ℝ) (500533854531/1000000000000 : ℝ) (25026692727/50000000000 : ℝ) (500533854531/1000000000000 : ℝ) (25026692727/50000000000 : ℝ) (500533854531/1000000000000 : ℝ) (25026692727/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33135/262144 : ℝ))) 6 (500533854531/1000000000000 : ℝ) (25026692727/50000000000 : ℝ) (500533854531/1000000000000 : ℝ) (25026692727/50000000000 : ℝ) (500533854531/1000000000000 : ℝ) (25026692727/50000000000 : ℝ) (500533854531/1000000000000 : ℝ) (25026692727/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33135/262144 : ℝ))) 7 (500533854531/1000000000000 : ℝ) (25026692727/50000000000 : ℝ) (500533854531/1000000000000 : ℝ) (25026692727/50000000000 : ℝ) (500533854531/1000000000000 : ℝ) (25026692727/50000000000 : ℝ) (500533854531/1000000000000 : ℝ) (25026692727/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33135/262144 : ℝ)) hmem 8 (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ) (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33135/262144 : ℝ))) hcmem 8 (500533854531/1000000000000 : ℝ) (25026692727/50000000000 : ℝ) (500533854531/1000000000000 : ℝ) (25026692727/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33135/262144 : ℝ)) (992146603111/1000000000000 : ℝ) (992146603113/1000000000000 : ℝ) (500533854531/1000000000000 : ℝ) (25026692727/50000000000 : ℝ) (396230122477/500000000000 : ℝ) (792460244971/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0354_exp_lower
  have heNumeric : (1027453195769/500000000000 : ℝ)/4 ≤ Real.exp (-21314050104697/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453195769/500000000000 : ℝ)/4 ≤ Real.exp ((16567/131072 : ℝ)-(792460244971/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16567/131072 : ℝ) (33135/262144 : ℝ) (792460244971/1000000000000 : ℝ) (1027453195769/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0355; no trusted numerical premise.
theorem cover8_leaf0355_exp_radius : (499013444818658617/500000000000000000 : ℝ) ≤ Real.exp ((-2071/131072 : ℝ)/8) ∧ Real.exp ((-2071/131072 : ℝ)/8) ≤ (199605377927463447/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2071/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0355_exp_lower : (920113716718078367/1000000000000000000 : ℝ) ≤ Real.exp ((-8525620372397/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525620372397/12800000000000 : ℝ)/8) ≤ (28753553647439949/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525620372397/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0355_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906338477/1000000000000 : ℝ) ≤ 4*Real.exp (33135/262144 : ℝ)*Real.exp (-mu (radius 8 (2071/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906338477/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2071/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0355_exp_radius
  have hrNumeric : (984323696591/1000000000000 : ℝ) ≤ Real.exp (-2071/131072 : ℝ) ∧ Real.exp (-2071/131072 : ℝ) ≤ (61520231037/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984323696591/1000000000000 : ℝ) ≤ (radius 8 (2071/16384 : ℝ)) ∧ (radius 8 (2071/16384 : ℝ)) ≤ (61520231037/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2071/16384 : ℝ)) (984323696591/1000000000000 : ℝ) (61520231037/62500000000 : ℝ) (88185685243/500000000000 : ℝ) (176371370493/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2071/16384 : ℝ)) (984323696591/1000000000000 : ℝ) (61520231037/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2071/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984323696591/1000000000000 : ℝ) (61520231037/62500000000 : ℝ) (198432369659/200000000000 : ℝ) (124020231037/125000000000 : ℝ) (124016360853/125000000000 : ℝ) (39685235473/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2071/16384 : ℝ)) 1 (198432369659/200000000000 : ℝ) (124020231037/125000000000 : ℝ) (124016360853/125000000000 : ℝ) (39685235473/40000000000 : ℝ) (992146367559/1000000000000 : ℝ) (992146367561/1000000000000 : ℝ) (496073183719/500000000000 : ℝ) (12401829593/12500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2071/16384 : ℝ)) 2 (992146367559/1000000000000 : ℝ) (992146367561/1000000000000 : ℝ) (496073183719/500000000000 : ℝ) (12401829593/12500000000 : ℝ) (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ) (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2071/16384 : ℝ)) 3 (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ) (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ) (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ) (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2071/16384 : ℝ)) 4 (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ) (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ) (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ) (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2071/16384 : ℝ)) 5 (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ) (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ) (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ) (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2071/16384 : ℝ)) 6 (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ) (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ) (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ) (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2071/16384 : ℝ)) 7 (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ) (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ) (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ) (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2071/16384 : ℝ))) (88185685243/500000000000 : ℝ) (176371370493/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2071/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88185685243/500000000000 : ℝ) (176371370493/1000000000000 : ℝ) (588185685243/1000000000000 : ℝ) (588185685247/1000000000000 : ℝ) (209982957931/500000000000 : ℝ) (419965915871/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2071/16384 : ℝ))) 1 (588185685243/1000000000000 : ℝ) (588185685247/1000000000000 : ℝ) (209982957931/500000000000 : ℝ) (419965915871/1000000000000 : ℝ) (63009475069/125000000000 : ℝ) (504075800559/1000000000000 : ℝ) (248504496941/500000000000 : ℝ) (49700899389/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2071/16384 : ℝ))) 2 (63009475069/125000000000 : ℝ) (504075800559/1000000000000 : ℝ) (248504496941/500000000000 : ℝ) (49700899389/100000000000 : ℝ) (500542397217/1000000000000 : ℝ) (20021695889/40000000000 : ℝ) (500529925651/1000000000000 : ℝ) (500529925659/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2071/16384 : ℝ))) 3 (500542397217/1000000000000 : ℝ) (20021695889/40000000000 : ℝ) (500529925651/1000000000000 : ℝ) (500529925659/1000000000000 : ℝ) (250268080717/500000000000 : ℝ) (250268080721/500000000000 : ℝ) (100107232279/200000000000 : ℝ) (125134040351/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2071/16384 : ℝ))) 4 (250268080717/500000000000 : ℝ) (250268080721/500000000000 : ℝ) (100107232279/200000000000 : ℝ) (125134040351/250000000000 : ℝ) (250268080707/500000000000 : ℝ) (500536161423/1000000000000 : ℝ) (250268080707/500000000000 : ℝ) (500536161423/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2071/16384 : ℝ))) 5 (250268080707/500000000000 : ℝ) (500536161423/1000000000000 : ℝ) (250268080707/500000000000 : ℝ) (500536161423/1000000000000 : ℝ) (250268080707/500000000000 : ℝ) (500536161423/1000000000000 : ℝ) (250268080707/500000000000 : ℝ) (500536161423/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2071/16384 : ℝ))) 6 (250268080707/500000000000 : ℝ) (500536161423/1000000000000 : ℝ) (250268080707/500000000000 : ℝ) (500536161423/1000000000000 : ℝ) (250268080707/500000000000 : ℝ) (500536161423/1000000000000 : ℝ) (250268080707/500000000000 : ℝ) (500536161423/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2071/16384 : ℝ))) 7 (250268080707/500000000000 : ℝ) (500536161423/1000000000000 : ℝ) (250268080707/500000000000 : ℝ) (500536161423/1000000000000 : ℝ) (250268080707/500000000000 : ℝ) (500536161423/1000000000000 : ℝ) (250268080707/500000000000 : ℝ) (500536161423/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2071/16384 : ℝ)) hmem 8 (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ) (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2071/16384 : ℝ))) hcmem 8 (250268080707/500000000000 : ℝ) (500536161423/1000000000000 : ℝ) (250268080707/500000000000 : ℝ) (500536161423/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2071/16384 : ℝ)) (496073183749/500000000000 : ℝ) (992146367501/1000000000000 : ℝ) (250268080707/500000000000 : ℝ) (500536161423/1000000000000 : ℝ) (792464085473/1000000000000 : ℝ) (79246408549/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0355_exp_lower
  have heNumeric : (2054906338477/1000000000000 : ℝ)/4 ≤ Real.exp (-8525620372397/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906338477/1000000000000 : ℝ)/4 ≤ Real.exp ((33135/262144 : ℝ)-(79246408549/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33135/262144 : ℝ) (2071/16384 : ℝ) (79246408549/100000000000 : ℝ) (2054906338477/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0356; no trusted numerical premise.
theorem cover8_leaf0356_exp_radius : (499013415075140387/500000000000000000 : ℝ) ≤ Real.exp ((-33137/2097152 : ℝ)/8) ∧ Real.exp ((-33137/2097152 : ℝ)/8) ≤ (39921073206011231/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33137/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0356_exp_lower : (920113713757988081/1000000000000000000 : ℝ) ≤ Real.exp ((-2664256469321/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664256469321/4000000000000 : ℝ)/8) ≤ (460056856878994041/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664256469321/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0356_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906285591/1000000000000 : ℝ) ≤ 4*Real.exp (2071/16384 : ℝ)*Real.exp (-mu (radius 8 (33137/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906285591/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33137/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0356_exp_radius
  have hrNumeric : (984323227229/1000000000000 : ℝ) ≤ Real.exp (-33137/2097152 : ℝ) ∧ Real.exp (-33137/2097152 : ℝ) ≤ (98432322723/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984323227229/1000000000000 : ℝ) ≤ (radius 8 (33137/262144 : ℝ)) ∧ (radius 8 (33137/262144 : ℝ)) ≤ (98432322723/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33137/262144 : ℝ)) (984323227229/1000000000000 : ℝ) (98432322723/100000000000 : ℝ) (176373989963/1000000000000 : ℝ) (176373989969/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33137/262144 : ℝ)) (984323227229/1000000000000 : ℝ) (98432322723/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33137/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984323227229/1000000000000 : ℝ) (98432322723/100000000000 : ℝ) (496080806807/500000000000 : ℝ) (198432322723/200000000000 : ℝ) (496065325141/500000000000 : ℝ) (992130650283/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33137/262144 : ℝ)) 1 (496080806807/500000000000 : ℝ) (198432322723/200000000000 : ℝ) (496065325141/500000000000 : ℝ) (992130650283/1000000000000 : ℝ) (248036532987/250000000000 : ℝ) (992146131949/1000000000000 : ℝ) (992146131827/1000000000000 : ℝ) (992146131829/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33137/262144 : ℝ)) 2 (248036532987/250000000000 : ℝ) (992146131949/1000000000000 : ℝ) (992146131827/1000000000000 : ℝ) (992146131829/1000000000000 : ℝ) (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ) (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33137/262144 : ℝ)) 3 (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ) (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ) (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ) (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33137/262144 : ℝ)) 4 (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ) (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ) (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ) (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33137/262144 : ℝ)) 5 (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ) (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ) (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ) (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33137/262144 : ℝ)) 6 (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ) (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ) (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ) (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33137/262144 : ℝ)) 7 (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ) (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ) (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ) (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33137/262144 : ℝ))) (176373989963/1000000000000 : ℝ) (176373989969/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33137/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176373989963/1000000000000 : ℝ) (176373989969/1000000000000 : ℝ) (588186994981/1000000000000 : ℝ) (117637398997/200000000000 : ℝ) (13124032329/31250000000 : ℝ) (52496129317/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33137/262144 : ℝ))) 1 (588186994981/1000000000000 : ℝ) (117637398997/200000000000 : ℝ) (13124032329/31250000000 : ℝ) (52496129317/125000000000 : ℝ) (252039007377/500000000000 : ℝ) (504078014761/1000000000000 : ℝ) (49701139263/100000000000 : ℝ) (497011392637/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33137/262144 : ℝ))) 2 (252039007377/500000000000 : ℝ) (504078014761/1000000000000 : ℝ) (49701139263/100000000000 : ℝ) (497011392637/1000000000000 : ℝ) (125136175923/250000000000 : ℝ) (500544703699/1000000000000 : ℝ) (100106446567/200000000000 : ℝ) (500532232843/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33137/262144 : ℝ))) 3 (125136175923/250000000000 : ℝ) (500544703699/1000000000000 : ℝ) (100106446567/200000000000 : ℝ) (500532232843/1000000000000 : ℝ) (500538468263/1000000000000 : ℝ) (500538468271/1000000000000 : ℝ) (3910456783/7812500000 : ℝ) (500538468233/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33137/262144 : ℝ))) 4 (500538468263/1000000000000 : ℝ) (500538468271/1000000000000 : ℝ) (3910456783/7812500000 : ℝ) (500538468233/1000000000000 : ℝ) (500538468243/1000000000000 : ℝ) (125134617063/250000000000 : ℝ) (500538468243/1000000000000 : ℝ) (125134617063/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33137/262144 : ℝ))) 5 (500538468243/1000000000000 : ℝ) (125134617063/250000000000 : ℝ) (500538468243/1000000000000 : ℝ) (125134617063/250000000000 : ℝ) (500538468243/1000000000000 : ℝ) (125134617063/250000000000 : ℝ) (500538468243/1000000000000 : ℝ) (125134617063/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33137/262144 : ℝ))) 6 (500538468243/1000000000000 : ℝ) (125134617063/250000000000 : ℝ) (500538468243/1000000000000 : ℝ) (125134617063/250000000000 : ℝ) (500538468243/1000000000000 : ℝ) (125134617063/250000000000 : ℝ) (500538468243/1000000000000 : ℝ) (125134617063/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33137/262144 : ℝ))) 7 (500538468243/1000000000000 : ℝ) (125134617063/250000000000 : ℝ) (500538468243/1000000000000 : ℝ) (125134617063/250000000000 : ℝ) (500538468243/1000000000000 : ℝ) (125134617063/250000000000 : ℝ) (500538468243/1000000000000 : ℝ) (125134617063/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33137/262144 : ℝ)) hmem 8 (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ) (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33137/262144 : ℝ))) hcmem 8 (500538468243/1000000000000 : ℝ) (125134617063/250000000000 : ℝ) (500538468243/1000000000000 : ℝ) (125134617063/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33137/262144 : ℝ)) (992146131887/1000000000000 : ℝ) (992146131889/1000000000000 : ℝ) (500538468243/1000000000000 : ℝ) (125134617063/250000000000 : ℝ) (792467925907/1000000000000 : ℝ) (198116981481/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0356_exp_lower
  have heNumeric : (2054906285591/1000000000000 : ℝ)/4 ≤ Real.exp (-2664256469321/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906285591/1000000000000 : ℝ)/4 ≤ Real.exp ((2071/16384 : ℝ)-(198116981481/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2071/16384 : ℝ) (33137/262144 : ℝ) (198116981481/250000000000 : ℝ) (2054906285591/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0357; no trusted numerical premise.
theorem cover8_leaf0357_exp_radius : (998026770663247859/1000000000000000000 : ℝ) ≤ Real.exp ((-16569/1048576 : ℝ)/8) ∧ Real.exp ((-16569/1048576 : ℝ)/8) ≤ (49901338533162393/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16569/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0357_exp_lower : (184022742161488797/200000000000000000 : ℝ) ≤ Real.exp ((-1705124206039/2560000000000 : ℝ)/8) ∧ Real.exp ((-1705124206039/2560000000000 : ℝ)/8) ≤ (460056855403721993/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1705124206039/2560000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0357_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (16439249863/8000000000 : ℝ) ≤ 4*Real.exp (33137/262144 : ℝ)*Real.exp (-mu (radius 8 (16569/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (16439249863/8000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16569/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0357_exp_radius
  have hrNumeric : (246080689467/250000000000 : ℝ) ≤ Real.exp (-16569/1048576 : ℝ) ∧ Real.exp (-16569/1048576 : ℝ) ≤ (984322757869/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246080689467/250000000000 : ℝ) ≤ (radius 8 (16569/131072 : ℝ)) ∧ (radius 8 (16569/131072 : ℝ)) ≤ (984322757869/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16569/131072 : ℝ)) (246080689467/250000000000 : ℝ) (984322757869/1000000000000 : ℝ) (176376609393/1000000000000 : ℝ) (881883047/5000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16569/131072 : ℝ)) (246080689467/250000000000 : ℝ) (984322757869/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16569/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246080689467/250000000000 : ℝ) (984322757869/1000000000000 : ℝ) (496080689467/500000000000 : ℝ) (198432275787/200000000000 : ℝ) (49606520687/50000000000 : ℝ) (992130413741/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16569/131072 : ℝ)) 1 (496080689467/500000000000 : ℝ) (198432275787/200000000000 : ℝ) (49606520687/50000000000 : ℝ) (992130413741/1000000000000 : ℝ) (992145896337/1000000000000 : ℝ) (496072948169/500000000000 : ℝ) (124018237027/125000000000 : ℝ) (496072948109/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16569/131072 : ℝ)) 2 (992145896337/1000000000000 : ℝ) (496072948169/500000000000 : ℝ) (124018237027/125000000000 : ℝ) (496072948109/500000000000 : ℝ) (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ) (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16569/131072 : ℝ)) 3 (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ) (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ) (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ) (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16569/131072 : ℝ)) 4 (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ) (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ) (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ) (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16569/131072 : ℝ)) 5 (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ) (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ) (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ) (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16569/131072 : ℝ)) 6 (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ) (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ) (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ) (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16569/131072 : ℝ)) 7 (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ) (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ) (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ) (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16569/131072 : ℝ))) (176376609393/1000000000000 : ℝ) (881883047/5000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16569/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176376609393/1000000000000 : ℝ) (881883047/5000000000 : ℝ) (73523538087/125000000000 : ℝ) (5881883047/10000000000 : ℝ) (104993038279/250000000000 : ℝ) (134391089/320000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16569/131072 : ℝ))) 1 (73523538087/125000000000 : ℝ) (5881883047/10000000000 : ℝ) (104993038279/250000000000 : ℝ) (134391089/320000000 : ℝ) (252040114453/500000000000 : ℝ) (504080228913/1000000000000 : ℝ) (248506895659/500000000000 : ℝ) (248506895663/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16569/131072 : ℝ))) 2 (252040114453/500000000000 : ℝ) (504080228913/1000000000000 : ℝ) (248506895659/500000000000 : ℝ) (248506895663/500000000000 : ℝ) (7821047033/15625000000 : ℝ) (12513675253/25000000000 : ℝ) (125133634991/250000000000 : ℝ) (125133634993/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16569/131072 : ℝ))) 3 (7821047033/15625000000 : ℝ) (12513675253/25000000000 : ℝ) (125133634991/250000000000 : ℝ) (125133634993/250000000000 : ℝ) (250270387519/500000000000 : ℝ) (250270387523/500000000000 : ℝ) (500540774999/1000000000000 : ℝ) (15641899219/31250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16569/131072 : ℝ))) 4 (250270387519/500000000000 : ℝ) (250270387523/500000000000 : ℝ) (500540774999/1000000000000 : ℝ) (15641899219/31250000000 : ℝ) (250270387509/500000000000 : ℝ) (500540775027/1000000000000 : ℝ) (250270387509/500000000000 : ℝ) (500540775027/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16569/131072 : ℝ))) 5 (250270387509/500000000000 : ℝ) (500540775027/1000000000000 : ℝ) (250270387509/500000000000 : ℝ) (500540775027/1000000000000 : ℝ) (250270387509/500000000000 : ℝ) (500540775027/1000000000000 : ℝ) (250270387509/500000000000 : ℝ) (500540775027/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16569/131072 : ℝ))) 6 (250270387509/500000000000 : ℝ) (500540775027/1000000000000 : ℝ) (250270387509/500000000000 : ℝ) (500540775027/1000000000000 : ℝ) (250270387509/500000000000 : ℝ) (500540775027/1000000000000 : ℝ) (250270387509/500000000000 : ℝ) (500540775027/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16569/131072 : ℝ))) 7 (250270387509/500000000000 : ℝ) (500540775027/1000000000000 : ℝ) (250270387509/500000000000 : ℝ) (500540775027/1000000000000 : ℝ) (250270387509/500000000000 : ℝ) (500540775027/1000000000000 : ℝ) (250270387509/500000000000 : ℝ) (500540775027/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16569/131072 : ℝ)) hmem 8 (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ) (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16569/131072 : ℝ))) hcmem 8 (250270387509/500000000000 : ℝ) (500540775027/1000000000000 : ℝ) (250270387509/500000000000 : ℝ) (500540775027/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16569/131072 : ℝ)) (248036474069/250000000000 : ℝ) (496072948139/500000000000 : ℝ) (250270387509/500000000000 : ℝ) (500540775027/1000000000000 : ℝ) (396235883129/500000000000 : ℝ) (31698870651/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0357_exp_lower
  have heNumeric : (16439249863/8000000000 : ℝ)/4 ≤ Real.exp (-1705124206039/2560000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (16439249863/8000000000 : ℝ)/4 ≤ Real.exp ((33137/262144 : ℝ)-(31698870651/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33137/262144 : ℝ) (16569/131072 : ℝ) (31698870651/40000000000 : ℝ) (16439249863/8000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0358; no trusted numerical premise.
theorem cover8_leaf0358_exp_radius : (99802671117621849/100000000000000000 : ℝ) ≤ Real.exp ((-33139/2097152 : ℝ)/8) ∧ Real.exp ((-33139/2097152 : ℝ)/8) ≤ (998026711176218491/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33139/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0358_exp_lower : (920113707864950893/1000000000000000000 : ℝ) ≤ Real.exp ((-21314053394167/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314053394167/32000000000000 : ℝ)/8) ≤ (460056853932475447/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314053394167/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0358_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453090151/500000000000 : ℝ) ≤ 4*Real.exp (16569/131072 : ℝ)*Real.exp (-mu (radius 8 (33139/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453090151/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33139/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0358_exp_radius
  have hrNumeric : (492161144253/500000000000 : ℝ) ≤ Real.exp (-33139/2097152 : ℝ) ∧ Real.exp (-33139/2097152 : ℝ) ≤ (984322288507/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492161144253/500000000000 : ℝ) ≤ (radius 8 (33139/262144 : ℝ)) ∧ (radius 8 (33139/262144 : ℝ)) ≤ (984322288507/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33139/262144 : ℝ)) (492161144253/500000000000 : ℝ) (984322288507/1000000000000 : ℝ) (176379228789/1000000000000 : ℝ) (35275845759/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33139/262144 : ℝ)) (492161144253/500000000000 : ℝ) (984322288507/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33139/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492161144253/500000000000 : ℝ) (984322288507/1000000000000 : ℝ) (992161144253/1000000000000 : ℝ) (496080572127/500000000000 : ℝ) (992130177197/1000000000000 : ℝ) (992130177199/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33139/262144 : ℝ)) 1 (992161144253/1000000000000 : ℝ) (496080572127/500000000000 : ℝ) (992130177197/1000000000000 : ℝ) (992130177199/1000000000000 : ℝ) (39685826429/40000000000 : ℝ) (992145660727/1000000000000 : ℝ) (248036415151/250000000000 : ℝ) (496072830303/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33139/262144 : ℝ)) 2 (39685826429/40000000000 : ℝ) (992145660727/1000000000000 : ℝ) (248036415151/250000000000 : ℝ) (496072830303/500000000000 : ℝ) (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ) (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33139/262144 : ℝ)) 3 (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ) (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ) (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ) (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33139/262144 : ℝ)) 4 (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ) (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ) (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ) (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33139/262144 : ℝ)) 5 (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ) (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ) (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ) (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33139/262144 : ℝ)) 6 (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ) (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ) (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ) (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33139/262144 : ℝ)) 7 (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ) (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ) (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ) (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33139/262144 : ℝ))) (176379228789/1000000000000 : ℝ) (35275845759/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33139/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176379228789/1000000000000 : ℝ) (35275845759/200000000000 : ℝ) (294094807197/500000000000 : ℝ) (294094807199/500000000000 : ℝ) (419975271639/1000000000000 : ℝ) (13124227239/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33139/262144 : ℝ))) 1 (294094807197/500000000000 : ℝ) (294094807199/500000000000 : ℝ) (419975271639/1000000000000 : ℝ) (13124227239/31250000000 : ℝ) (63010305377/125000000000 : ℝ) (504082443023/1000000000000 : ℝ) (497016189957/1000000000000 : ℝ) (248508094983/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33139/262144 : ℝ))) 2 (63010305377/125000000000 : ℝ) (504082443023/1000000000000 : ℝ) (497016189957/1000000000000 : ℝ) (248508094983/500000000000 : ℝ) (250274658243/500000000000 : ℝ) (100109863299/200000000000 : ℝ) (500536847047/1000000000000 : ℝ) (31283552941/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33139/262144 : ℝ))) 3 (250274658243/500000000000 : ℝ) (100109863299/200000000000 : ℝ) (500536847047/1000000000000 : ℝ) (31283552941/62500000000 : ℝ) (250271540883/500000000000 : ℝ) (31283942611/62500000000 : ℝ) (500543081727/1000000000000 : ℝ) (500543081737/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33139/262144 : ℝ))) 4 (250271540883/500000000000 : ℝ) (31283942611/62500000000 : ℝ) (500543081727/1000000000000 : ℝ) (500543081737/1000000000000 : ℝ) (250271540873/500000000000 : ℝ) (500543081757/1000000000000 : ℝ) (250271540873/500000000000 : ℝ) (500543081757/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33139/262144 : ℝ))) 5 (250271540873/500000000000 : ℝ) (500543081757/1000000000000 : ℝ) (250271540873/500000000000 : ℝ) (500543081757/1000000000000 : ℝ) (250271540873/500000000000 : ℝ) (500543081757/1000000000000 : ℝ) (250271540873/500000000000 : ℝ) (500543081757/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33139/262144 : ℝ))) 6 (250271540873/500000000000 : ℝ) (500543081757/1000000000000 : ℝ) (250271540873/500000000000 : ℝ) (500543081757/1000000000000 : ℝ) (250271540873/500000000000 : ℝ) (500543081757/1000000000000 : ℝ) (250271540873/500000000000 : ℝ) (500543081757/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33139/262144 : ℝ))) 7 (250271540873/500000000000 : ℝ) (500543081757/1000000000000 : ℝ) (250271540873/500000000000 : ℝ) (500543081757/1000000000000 : ℝ) (250271540873/500000000000 : ℝ) (500543081757/1000000000000 : ℝ) (250271540873/500000000000 : ℝ) (500543081757/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33139/262144 : ℝ)) hmem 8 (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ) (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33139/262144 : ℝ))) hcmem 8 (250271540873/500000000000 : ℝ) (500543081757/1000000000000 : ℝ) (250271540873/500000000000 : ℝ) (500543081757/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33139/262144 : ℝ)) (124018207583/125000000000 : ℝ) (992145660667/1000000000000 : ℝ) (250271540873/500000000000 : ℝ) (500543081757/1000000000000 : ℝ) (99059450817/125000000000 : ℝ) (198118901639/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0358_exp_lower
  have heNumeric : (1027453090151/500000000000 : ℝ)/4 ≤ Real.exp (-21314053394167/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453090151/500000000000 : ℝ)/4 ≤ Real.exp ((16569/131072 : ℝ)-(198118901639/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16569/131072 : ℝ) (33139/262144 : ℝ) (198118901639/250000000000 : ℝ) (1027453090151/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0359; no trusted numerical premise.
theorem cover8_leaf0359_exp_radius : (998026651689192667/1000000000000000000 : ℝ) ≤ Real.exp ((-8285/524288 : ℝ)/8) ∧ Real.exp ((-8285/524288 : ℝ)/8) ≤ (249506662922298167/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8285/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0359_exp_lower : (184022740986423801/200000000000000000 : ℝ) ≤ Real.exp ((-42628108420317/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628108420317/64000000000000 : ℝ)/8) ≤ (460056852466059503/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628108420317/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0359_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906127903/1000000000000 : ℝ) ≤ 4*Real.exp (33139/262144 : ℝ)*Real.exp (-mu (radius 8 (8285/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906127903/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8285/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0359_exp_radius
  have hrNumeric : (196864363829/200000000000 : ℝ) ≤ Real.exp (-8285/524288 : ℝ) ∧ Real.exp (-8285/524288 : ℝ) ≤ (492160909573/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196864363829/200000000000 : ℝ) ≤ (radius 8 (8285/65536 : ℝ)) ∧ (radius 8 (8285/65536 : ℝ)) ≤ (492160909573/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8285/65536 : ℝ)) (196864363829/200000000000 : ℝ) (492160909573/500000000000 : ℝ) (176381848139/1000000000000 : ℝ) (88190924073/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8285/65536 : ℝ)) (196864363829/200000000000 : ℝ) (492160909573/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8285/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196864363829/200000000000 : ℝ) (492160909573/500000000000 : ℝ) (248040227393/250000000000 : ℝ) (992160909573/1000000000000 : ℝ) (198425988131/200000000000 : ℝ) (62008121291/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8285/65536 : ℝ)) 1 (248040227393/250000000000 : ℝ) (992160909573/1000000000000 : ℝ) (198425988131/200000000000 : ℝ) (62008121291/62500000000 : ℝ) (992145425113/1000000000000 : ℝ) (198429085023/200000000000 : ℝ) (31004544531/31250000000 : ℝ) (496072712497/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8285/65536 : ℝ)) 2 (992145425113/1000000000000 : ℝ) (198429085023/200000000000 : ℝ) (31004544531/31250000000 : ℝ) (496072712497/500000000000 : ℝ) (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ) (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8285/65536 : ℝ)) 3 (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ) (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ) (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ) (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8285/65536 : ℝ)) 4 (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ) (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ) (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ) (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8285/65536 : ℝ)) 5 (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ) (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ) (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ) (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8285/65536 : ℝ)) 6 (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ) (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ) (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ) (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8285/65536 : ℝ)) 7 (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ) (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ) (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ) (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8285/65536 : ℝ))) (176381848139/1000000000000 : ℝ) (88190924073/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8285/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176381848139/1000000000000 : ℝ) (88190924073/500000000000 : ℝ) (588190924069/1000000000000 : ℝ) (588190924073/1000000000000 : ℝ) (83995678017/200000000000 : ℝ) (83995678019/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8285/65536 : ℝ))) 1 (588190924069/1000000000000 : ℝ) (588190924073/1000000000000 : ℝ) (83995678017/200000000000 : ℝ) (83995678019/200000000000 : ℝ) (504084657077/1000000000000 : ℝ) (126021164271/250000000000 : ℝ) (248509294269/500000000000 : ℝ) (497018588547/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8285/65536 : ℝ))) 2 (504084657077/1000000000000 : ℝ) (126021164271/250000000000 : ℝ) (248509294269/500000000000 : ℝ) (497018588547/1000000000000 : ℝ) (500551622807/1000000000000 : ℝ) (15642238213/31250000000 : ℝ) (125134788519/250000000000 : ℝ) (100107830817/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8285/65536 : ℝ))) 3 (500551622807/1000000000000 : ℝ) (15642238213/31250000000 : ℝ) (125134788519/250000000000 : ℝ) (100107830817/200000000000 : ℝ) (500545388441/1000000000000 : ℝ) (500545388451/1000000000000 : ℝ) (250272694201/500000000000 : ℝ) (125136347103/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8285/65536 : ℝ))) 4 (500545388441/1000000000000 : ℝ) (500545388451/1000000000000 : ℝ) (250272694201/500000000000 : ℝ) (125136347103/250000000000 : ℝ) (500545388421/1000000000000 : ℝ) (31284086777/62500000000 : ℝ) (500545388421/1000000000000 : ℝ) (31284086777/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8285/65536 : ℝ))) 5 (500545388421/1000000000000 : ℝ) (31284086777/62500000000 : ℝ) (500545388421/1000000000000 : ℝ) (31284086777/62500000000 : ℝ) (500545388421/1000000000000 : ℝ) (31284086777/62500000000 : ℝ) (500545388421/1000000000000 : ℝ) (31284086777/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8285/65536 : ℝ))) 6 (500545388421/1000000000000 : ℝ) (31284086777/62500000000 : ℝ) (500545388421/1000000000000 : ℝ) (31284086777/62500000000 : ℝ) (500545388421/1000000000000 : ℝ) (31284086777/62500000000 : ℝ) (500545388421/1000000000000 : ℝ) (31284086777/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8285/65536 : ℝ))) 7 (500545388421/1000000000000 : ℝ) (31284086777/62500000000 : ℝ) (500545388421/1000000000000 : ℝ) (31284086777/62500000000 : ℝ) (500545388421/1000000000000 : ℝ) (31284086777/62500000000 : ℝ) (500545388421/1000000000000 : ℝ) (31284086777/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8285/65536 : ℝ)) hmem 8 (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ) (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8285/65536 : ℝ))) hcmem 8 (500545388421/1000000000000 : ℝ) (31284086777/62500000000 : ℝ) (500545388421/1000000000000 : ℝ) (31284086777/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8285/65536 : ℝ)) (248036356263/250000000000 : ℝ) (198429085011/200000000000 : ℝ) (500545388421/1000000000000 : ℝ) (31284086777/62500000000 : ℝ) (198119861683/250000000000 : ℝ) (792479446753/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0359_exp_lower
  have heNumeric : (2054906127903/1000000000000 : ℝ)/4 ≤ Real.exp (-42628108420317/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906127903/1000000000000 : ℝ)/4 ≤ Real.exp ((33139/262144 : ℝ)-(792479446753/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33139/262144 : ℝ) (8285/65536 : ℝ) (792479446753/1000000000000 : ℝ) (2054906127903/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0360; no trusted numerical premise.
theorem cover8_leaf0360_exp_radius : (99802659220217039/100000000000000000 : ℝ) ≤ Real.exp ((-33141/2097152 : ℝ)/8) ∧ Real.exp ((-33141/2097152 : ℝ)/8) ≤ (998026592202170391/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33141/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0360_exp_lower : (56159283569847/61035156250000 : ℝ) ≤ Real.exp ((-10657027511811/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657027511811/16000000000000 : ℝ)/8) ≤ (920113702008373249/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657027511811/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0360_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453037833/500000000000 : ℝ) ≤ 4*Real.exp (8285/65536 : ℝ)*Real.exp (-mu (radius 8 (33141/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453037833/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33141/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0360_exp_radius
  have hrNumeric : (123040168723/125000000000 : ℝ) ≤ Real.exp (-33141/2097152 : ℝ) ∧ Real.exp (-33141/2097152 : ℝ) ≤ (196864269957/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123040168723/125000000000 : ℝ) ≤ (radius 8 (33141/262144 : ℝ)) ∧ (radius 8 (33141/262144 : ℝ)) ≤ (196864269957/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33141/262144 : ℝ)) (123040168723/125000000000 : ℝ) (196864269957/200000000000 : ℝ) (176384467449/1000000000000 : ℝ) (344500913/1953125000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33141/262144 : ℝ)) (123040168723/125000000000 : ℝ) (196864269957/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33141/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123040168723/125000000000 : ℝ) (196864269957/200000000000 : ℝ) (248040168723/250000000000 : ℝ) (992160674893/1000000000000 : ℝ) (992129704113/1000000000000 : ℝ) (496064852057/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33141/262144 : ℝ)) 1 (248040168723/250000000000 : ℝ) (992160674893/1000000000000 : ℝ) (992129704113/1000000000000 : ℝ) (496064852057/500000000000 : ℝ) (496072594751/500000000000 : ℝ) (7751134293/7812500000 : ℝ) (992145189381/1000000000000 : ℝ) (992145189383/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33141/262144 : ℝ)) 2 (496072594751/500000000000 : ℝ) (7751134293/7812500000 : ℝ) (992145189381/1000000000000 : ℝ) (992145189383/1000000000000 : ℝ) (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ) (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33141/262144 : ℝ)) 3 (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ) (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ) (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ) (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33141/262144 : ℝ)) 4 (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ) (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ) (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ) (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33141/262144 : ℝ)) 5 (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ) (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ) (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ) (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33141/262144 : ℝ)) 6 (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ) (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ) (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ) (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33141/262144 : ℝ)) 7 (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ) (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ) (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ) (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33141/262144 : ℝ))) (176384467449/1000000000000 : ℝ) (344500913/1953125000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33141/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176384467449/1000000000000 : ℝ) (344500913/1953125000 : ℝ) (147048058431/250000000000 : ℝ) (2297625913/3906250000 : ℝ) (20999075423/50000000000 : ℝ) (41998150847/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33141/262144 : ℝ))) 1 (147048058431/250000000000 : ℝ) (2297625913/3906250000 : ℝ) (20999075423/50000000000 : ℝ) (41998150847/100000000000 : ℝ) (126021717773/250000000000 : ℝ) (504086871099/1000000000000 : ℝ) (99404197413/200000000000 : ℝ) (248510493537/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33141/262144 : ℝ))) 2 (126021717773/250000000000 : ℝ) (504086871099/1000000000000 : ℝ) (99404197413/200000000000 : ℝ) (248510493537/500000000000 : ℝ) (250276964539/500000000000 : ℝ) (500553929087/1000000000000 : ℝ) (7820960329/15625000000 : ℝ) (100108292213/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33141/262144 : ℝ))) 3 (250276964539/500000000000 : ℝ) (500553929087/1000000000000 : ℝ) (7820960329/15625000000 : ℝ) (100108292213/200000000000 : ℝ) (500547695067/1000000000000 : ℝ) (125136923769/250000000000 : ℝ) (125136923757/250000000000 : ℝ) (250273847519/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33141/262144 : ℝ))) 4 (500547695067/1000000000000 : ℝ) (125136923769/250000000000 : ℝ) (125136923757/250000000000 : ℝ) (250273847519/500000000000 : ℝ) (500547695047/1000000000000 : ℝ) (500547695057/1000000000000 : ℝ) (500547695047/1000000000000 : ℝ) (500547695057/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33141/262144 : ℝ))) 5 (500547695047/1000000000000 : ℝ) (500547695057/1000000000000 : ℝ) (500547695047/1000000000000 : ℝ) (500547695057/1000000000000 : ℝ) (500547695047/1000000000000 : ℝ) (500547695057/1000000000000 : ℝ) (500547695047/1000000000000 : ℝ) (500547695057/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33141/262144 : ℝ))) 6 (500547695047/1000000000000 : ℝ) (500547695057/1000000000000 : ℝ) (500547695047/1000000000000 : ℝ) (500547695057/1000000000000 : ℝ) (500547695047/1000000000000 : ℝ) (500547695057/1000000000000 : ℝ) (500547695047/1000000000000 : ℝ) (500547695057/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33141/262144 : ℝ))) 7 (500547695047/1000000000000 : ℝ) (500547695057/1000000000000 : ℝ) (500547695047/1000000000000 : ℝ) (500547695057/1000000000000 : ℝ) (500547695047/1000000000000 : ℝ) (500547695057/1000000000000 : ℝ) (500547695047/1000000000000 : ℝ) (500547695057/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33141/262144 : ℝ)) hmem 8 (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ) (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33141/262144 : ℝ))) hcmem 8 (500547695047/1000000000000 : ℝ) (500547695057/1000000000000 : ℝ) (500547695047/1000000000000 : ℝ) (500547695057/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33141/262144 : ℝ)) (992145189441/1000000000000 : ℝ) (248036297361/250000000000 : ℝ) (500547695047/1000000000000 : ℝ) (500547695057/1000000000000 : ℝ) (198120821713/250000000000 : ℝ) (792483286871/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0360_exp_lower
  have heNumeric : (1027453037833/500000000000 : ℝ)/4 ≤ Real.exp (-10657027511811/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453037833/500000000000 : ℝ)/4 ≤ Real.exp ((8285/65536 : ℝ)-(792483286871/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8285/65536 : ℝ) (33141/262144 : ℝ) (792483286871/1000000000000 : ℝ) (1027453037833/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0361; no trusted numerical premise.
theorem cover8_leaf0361_exp_radius : (499013266357575829/500000000000000000 : ℝ) ≤ Real.exp ((-16571/1048576 : ℝ)/8) ∧ Real.exp ((-16571/1048576 : ℝ)/8) ≤ (998026532715151659/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16571/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0361_exp_lower : (230028424773370899/250000000000000000 : ℝ) ≤ Real.exp ((-42628111669243/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628111669243/64000000000000 : ℝ)/8) ≤ (920113699093483597/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628111669243/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0361_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906023587/1000000000000 : ℝ) ≤ 4*Real.exp (33141/262144 : ℝ)*Real.exp (-mu (radius 8 (16571/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906023587/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16571/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0361_exp_radius
  have hrNumeric : (984320880423/1000000000000 : ℝ) ≤ Real.exp (-16571/1048576 : ℝ) ∧ Real.exp (-16571/1048576 : ℝ) ≤ (123040110053/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984320880423/1000000000000 : ℝ) ≤ (radius 8 (16571/131072 : ℝ)) ∧ (radius 8 (16571/131072 : ℝ)) ≤ (123040110053/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16571/131072 : ℝ)) (984320880423/1000000000000 : ℝ) (123040110053/125000000000 : ℝ) (176387086719/1000000000000 : ℝ) (7055483469/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16571/131072 : ℝ)) (984320880423/1000000000000 : ℝ) (123040110053/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16571/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984320880423/1000000000000 : ℝ) (123040110053/125000000000 : ℝ) (992160440211/1000000000000 : ℝ) (248040110053/250000000000 : ℝ) (992129467571/1000000000000 : ℝ) (248032366893/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16571/131072 : ℝ)) 1 (992160440211/1000000000000 : ℝ) (248040110053/250000000000 : ℝ) (992129467571/1000000000000 : ℝ) (248032366893/250000000000 : ℝ) (992144953891/1000000000000 : ℝ) (248036238473/250000000000 : ℝ) (99214495377/100000000000 : ℝ) (248036238443/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16571/131072 : ℝ)) 2 (992144953891/1000000000000 : ℝ) (248036238473/250000000000 : ℝ) (99214495377/100000000000 : ℝ) (248036238443/250000000000 : ℝ) (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ) (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16571/131072 : ℝ)) 3 (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ) (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ) (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ) (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16571/131072 : ℝ)) 4 (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ) (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ) (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ) (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16571/131072 : ℝ)) 5 (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ) (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ) (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ) (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16571/131072 : ℝ)) 6 (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ) (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ) (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ) (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16571/131072 : ℝ)) 7 (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ) (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ) (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ) (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16571/131072 : ℝ))) (176387086719/1000000000000 : ℝ) (7055483469/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16571/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176387086719/1000000000000 : ℝ) (7055483469/40000000000 : ℝ) (588193543359/1000000000000 : ℝ) (588193543363/1000000000000 : ℝ) (83996925353/200000000000 : ℝ) (419984626773/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16571/131072 : ℝ))) 1 (588193543359/1000000000000 : ℝ) (588193543363/1000000000000 : ℝ) (83996925353/200000000000 : ℝ) (419984626773/1000000000000 : ℝ) (252044542531/500000000000 : ℝ) (126022271267/250000000000 : ℝ) (497023385539/1000000000000 : ℝ) (248511692773/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16571/131072 : ℝ))) 2 (252044542531/500000000000 : ℝ) (126022271267/250000000000 : ℝ) (497023385539/1000000000000 : ℝ) (248511692773/500000000000 : ℝ) (5005562353/10000000000 : ℝ) (500556235307/1000000000000 : ℝ) (500543767987/1000000000000 : ℝ) (250271883997/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16571/131072 : ℝ))) 3 (5005562353/10000000000 : ℝ) (500556235307/1000000000000 : ℝ) (500543767987/1000000000000 : ℝ) (250271883997/500000000000 : ℝ) (500550001643/1000000000000 : ℝ) (500550001651/1000000000000 : ℝ) (125137500401/250000000000 : ℝ) (125137500403/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16571/131072 : ℝ))) 4 (500550001643/1000000000000 : ℝ) (500550001651/1000000000000 : ℝ) (125137500401/250000000000 : ℝ) (125137500403/250000000000 : ℝ) (500550001623/1000000000000 : ℝ) (15642187551/31250000000 : ℝ) (500550001623/1000000000000 : ℝ) (15642187551/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16571/131072 : ℝ))) 5 (500550001623/1000000000000 : ℝ) (15642187551/31250000000 : ℝ) (500550001623/1000000000000 : ℝ) (15642187551/31250000000 : ℝ) (500550001623/1000000000000 : ℝ) (15642187551/31250000000 : ℝ) (500550001623/1000000000000 : ℝ) (15642187551/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16571/131072 : ℝ))) 6 (500550001623/1000000000000 : ℝ) (15642187551/31250000000 : ℝ) (500550001623/1000000000000 : ℝ) (15642187551/31250000000 : ℝ) (500550001623/1000000000000 : ℝ) (15642187551/31250000000 : ℝ) (500550001623/1000000000000 : ℝ) (15642187551/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16571/131072 : ℝ))) 7 (500550001623/1000000000000 : ℝ) (15642187551/31250000000 : ℝ) (500550001623/1000000000000 : ℝ) (15642187551/31250000000 : ℝ) (500550001623/1000000000000 : ℝ) (15642187551/31250000000 : ℝ) (500550001623/1000000000000 : ℝ) (15642187551/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16571/131072 : ℝ)) hmem 8 (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ) (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16571/131072 : ℝ))) hcmem 8 (500550001623/1000000000000 : ℝ) (15642187551/31250000000 : ℝ) (500550001623/1000000000000 : ℝ) (15642187551/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16571/131072 : ℝ)) (99214495383/100000000000 : ℝ) (124018119229/125000000000 : ℝ) (500550001623/1000000000000 : ℝ) (15642187551/31250000000 : ℝ) (158497425379/200000000000 : ℝ) (6191305679/7812500000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0361_exp_lower
  have heNumeric : (2054906023587/1000000000000 : ℝ)/4 ≤ Real.exp (-42628111669243/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906023587/1000000000000 : ℝ)/4 ≤ Real.exp ((33141/262144 : ℝ)-(6191305679/7812500000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33141/262144 : ℝ) (16571/131072 : ℝ) (6191305679/7812500000 : ℝ) (2054906023587/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0362; no trusted numerical premise.
theorem cover8_leaf0362_exp_radius : (124753309153517059/125000000000000000 : ℝ) ≤ Real.exp ((-33143/2097152 : ℝ)/8) ∧ Real.exp ((-33143/2097152 : ℝ)/8) ≤ (998026473228136473/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33143/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0362_exp_lower : (460056848093610009/500000000000000000 : ℝ) ≤ Real.exp ((-21314056643221/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314056643221/32000000000000 : ℝ)/8) ≤ (920113696187220019/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314056643221/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0362_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452985831/500000000000 : ℝ) ≤ 4*Real.exp (16571/131072 : ℝ)*Real.exp (-mu (radius 8 (33143/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452985831/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33143/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0362_exp_radius
  have hrNumeric : (492160205531/500000000000 : ℝ) ≤ Real.exp (-33143/2097152 : ℝ) ∧ Real.exp (-33143/2097152 : ℝ) ≤ (984320411063/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492160205531/500000000000 : ℝ) ≤ (radius 8 (33143/262144 : ℝ)) ∧ (radius 8 (33143/262144 : ℝ)) ≤ (984320411063/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33143/262144 : ℝ)) (492160205531/500000000000 : ℝ) (984320411063/1000000000000 : ℝ) (44097426487/250000000000 : ℝ) (35277941191/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33143/262144 : ℝ)) (492160205531/500000000000 : ℝ) (984320411063/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33143/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492160205531/500000000000 : ℝ) (984320411063/1000000000000 : ℝ) (992160205531/1000000000000 : ℝ) (248040051383/250000000000 : ℝ) (248032307757/250000000000 : ℝ) (99212923103/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33143/262144 : ℝ)) 1 (992160205531/1000000000000 : ℝ) (248040051383/250000000000 : ℝ) (248032307757/250000000000 : ℝ) (99212923103/100000000000 : ℝ) (992144718279/1000000000000 : ℝ) (992144718281/1000000000000 : ℝ) (496072359079/500000000000 : ℝ) (992144718161/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33143/262144 : ℝ)) 2 (992144718279/1000000000000 : ℝ) (992144718281/1000000000000 : ℝ) (496072359079/500000000000 : ℝ) (992144718161/1000000000000 : ℝ) (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ) (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33143/262144 : ℝ)) 3 (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ) (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ) (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ) (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33143/262144 : ℝ)) 4 (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ) (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ) (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ) (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33143/262144 : ℝ)) 5 (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ) (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ) (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ) (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33143/262144 : ℝ)) 6 (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ) (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ) (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ) (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33143/262144 : ℝ)) 7 (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ) (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ) (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ) (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33143/262144 : ℝ))) (44097426487/250000000000 : ℝ) (35277941191/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33143/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44097426487/250000000000 : ℝ) (35277941191/200000000000 : ℝ) (294097426487/500000000000 : ℝ) (294097426489/500000000000 : ℝ) (419987744997/1000000000000 : ℝ) (209993872503/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33143/262144 : ℝ))) 1 (294097426487/500000000000 : ℝ) (294097426489/500000000000 : ℝ) (419987744997/1000000000000 : ℝ) (209993872503/500000000000 : ℝ) (100818259797/200000000000 : ℝ) (31505706187/62500000000 : ℝ) (248512891979/500000000000 : ℝ) (248512891983/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33143/262144 : ℝ))) 2 (100818259797/200000000000 : ℝ) (31505706187/62500000000 : ℝ) (248512891979/500000000000 : ℝ) (248512891983/500000000000 : ℝ) (500558541471/1000000000000 : ℝ) (500558541479/1000000000000 : ℝ) (250273037433/500000000000 : ℝ) (4004368599/8000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33143/262144 : ℝ))) 3 (500558541471/1000000000000 : ℝ) (500558541479/1000000000000 : ℝ) (250273037433/500000000000 : ℝ) (4004368599/8000000000 : ℝ) (62569038521/125000000000 : ℝ) (500552308177/1000000000000 : ℝ) (500552308129/1000000000000 : ℝ) (500552308139/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33143/262144 : ℝ))) 4 (62569038521/125000000000 : ℝ) (500552308177/1000000000000 : ℝ) (500552308129/1000000000000 : ℝ) (500552308139/1000000000000 : ℝ) (125138077037/250000000000 : ℝ) (250276154079/500000000000 : ℝ) (125138077037/250000000000 : ℝ) (250276154079/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33143/262144 : ℝ))) 5 (125138077037/250000000000 : ℝ) (250276154079/500000000000 : ℝ) (125138077037/250000000000 : ℝ) (250276154079/500000000000 : ℝ) (125138077037/250000000000 : ℝ) (250276154079/500000000000 : ℝ) (125138077037/250000000000 : ℝ) (250276154079/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33143/262144 : ℝ))) 6 (125138077037/250000000000 : ℝ) (250276154079/500000000000 : ℝ) (125138077037/250000000000 : ℝ) (250276154079/500000000000 : ℝ) (125138077037/250000000000 : ℝ) (250276154079/500000000000 : ℝ) (125138077037/250000000000 : ℝ) (250276154079/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33143/262144 : ℝ))) 7 (125138077037/250000000000 : ℝ) (250276154079/500000000000 : ℝ) (125138077037/250000000000 : ℝ) (250276154079/500000000000 : ℝ) (125138077037/250000000000 : ℝ) (250276154079/500000000000 : ℝ) (125138077037/250000000000 : ℝ) (250276154079/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33143/262144 : ℝ)) hmem 8 (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ) (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33143/262144 : ℝ))) hcmem 8 (125138077037/250000000000 : ℝ) (250276154079/500000000000 : ℝ) (125138077037/250000000000 : ℝ) (250276154079/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33143/262144 : ℝ)) (496072359109/500000000000 : ℝ) (992144718221/1000000000000 : ℝ) (125138077037/250000000000 : ℝ) (250276154079/500000000000 : ℝ) (792490966859/1000000000000 : ℝ) (396245483439/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0362_exp_lower
  have heNumeric : (1027452985831/500000000000 : ℝ)/4 ≤ Real.exp (-21314056643221/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452985831/500000000000 : ℝ)/4 ≤ Real.exp ((16571/131072 : ℝ)-(396245483439/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16571/131072 : ℝ) (33143/262144 : ℝ) (396245483439/500000000000 : ℝ) (1027452985831/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0363; no trusted numerical premise.
theorem cover8_leaf0363_exp_radius : (31188325429410151/31250000000000000 : ℝ) ≤ Real.exp ((-4143/262144 : ℝ)/8) ∧ Real.exp ((-4143/262144 : ℝ)/8) ≤ (998026413741124833/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4143/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0363_exp_lower : (460056846645366329/500000000000000000 : ℝ) ≤ Real.exp ((-42628114898201/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628114898201/64000000000000 : ℝ)/8) ≤ (920113693290732659/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628114898201/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0363_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256863239989/125000000000 : ℝ) ≤ 4*Real.exp (33143/262144 : ℝ)*Real.exp (-mu (radius 8 (4143/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (256863239989/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4143/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0363_exp_radius
  have hrNumeric : (492159970851/500000000000 : ℝ) ≤ Real.exp (-4143/262144 : ℝ) ∧ Real.exp (-4143/262144 : ℝ) ≤ (984319941703/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492159970851/500000000000 : ℝ) ≤ (radius 8 (4143/32768 : ℝ)) ∧ (radius 8 (4143/32768 : ℝ)) ≤ (984319941703/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4143/32768 : ℝ)) (492159970851/500000000000 : ℝ) (984319941703/1000000000000 : ℝ) (44098081283/250000000000 : ℝ) (176392325139/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4143/32768 : ℝ)) (492159970851/500000000000 : ℝ) (984319941703/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4143/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492159970851/500000000000 : ℝ) (984319941703/1000000000000 : ℝ) (992159970851/1000000000000 : ℝ) (248039992713/250000000000 : ℝ) (992128994487/1000000000000 : ℝ) (124016124311/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4143/32768 : ℝ)) 1 (992159970851/1000000000000 : ℝ) (248039992713/250000000000 : ℝ) (992128994487/1000000000000 : ℝ) (124016124311/125000000000 : ℝ) (992144482669/1000000000000 : ℝ) (99214448267/100000000000 : ℝ) (248036120637/250000000000 : ℝ) (19842889651/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4143/32768 : ℝ)) 2 (992144482669/1000000000000 : ℝ) (99214448267/100000000000 : ℝ) (248036120637/250000000000 : ℝ) (19842889651/20000000000 : ℝ) (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ) (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4143/32768 : ℝ)) 3 (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ) (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ) (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ) (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4143/32768 : ℝ)) 4 (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ) (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ) (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ) (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4143/32768 : ℝ)) 5 (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ) (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ) (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ) (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4143/32768 : ℝ)) 6 (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ) (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ) (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ) (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4143/32768 : ℝ)) 7 (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ) (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ) (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ) (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4143/32768 : ℝ))) (44098081283/250000000000 : ℝ) (176392325139/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4143/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44098081283/250000000000 : ℝ) (176392325139/1000000000000 : ℝ) (294098081283/500000000000 : ℝ) (58819616257/100000000000 : ℝ) (26249428947/62500000000 : ℝ) (209995431581/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4143/32768 : ℝ))) 1 (294098081283/500000000000 : ℝ) (58819616257/100000000000 : ℝ) (26249428947/62500000000 : ℝ) (209995431581/500000000000 : ℝ) (504093512859/1000000000000 : ℝ) (252046756433/500000000000 : ℝ) (248514091159/500000000000 : ℝ) (497028182327/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4143/32768 : ℝ))) 2 (504093512859/1000000000000 : ℝ) (252046756433/500000000000 : ℝ) (248514091159/500000000000 : ℝ) (497028182327/1000000000000 : ℝ) (125140211897/250000000000 : ℝ) (500560847597/1000000000000 : ℝ) (125137095423/250000000000 : ℝ) (500548381701/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4143/32768 : ℝ))) 3 (125140211897/250000000000 : ℝ) (500560847597/1000000000000 : ℝ) (125137095423/250000000000 : ℝ) (500548381701/1000000000000 : ℝ) (6256932683/12500000000 : ℝ) (500554614649/1000000000000 : ℝ) (500554614601/1000000000000 : ℝ) (500554614611/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4143/32768 : ℝ))) 4 (6256932683/12500000000 : ℝ) (500554614649/1000000000000 : ℝ) (500554614601/1000000000000 : ℝ) (500554614611/1000000000000 : ℝ) (25027730731/50000000000 : ℝ) (50055461463/100000000000 : ℝ) (25027730731/50000000000 : ℝ) (50055461463/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4143/32768 : ℝ))) 5 (25027730731/50000000000 : ℝ) (50055461463/100000000000 : ℝ) (25027730731/50000000000 : ℝ) (50055461463/100000000000 : ℝ) (25027730731/50000000000 : ℝ) (50055461463/100000000000 : ℝ) (25027730731/50000000000 : ℝ) (50055461463/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4143/32768 : ℝ))) 6 (25027730731/50000000000 : ℝ) (50055461463/100000000000 : ℝ) (25027730731/50000000000 : ℝ) (50055461463/100000000000 : ℝ) (25027730731/50000000000 : ℝ) (50055461463/100000000000 : ℝ) (25027730731/50000000000 : ℝ) (50055461463/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4143/32768 : ℝ))) 7 (25027730731/50000000000 : ℝ) (50055461463/100000000000 : ℝ) (25027730731/50000000000 : ℝ) (50055461463/100000000000 : ℝ) (25027730731/50000000000 : ℝ) (50055461463/100000000000 : ℝ) (25027730731/50000000000 : ℝ) (50055461463/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4143/32768 : ℝ)) hmem 8 (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ) (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4143/32768 : ℝ))) hcmem 8 (25027730731/50000000000 : ℝ) (50055461463/100000000000 : ℝ) (25027730731/50000000000 : ℝ) (50055461463/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4143/32768 : ℝ)) (62009030163/62500000000 : ℝ) (99214448261/100000000000 : ℝ) (25027730731/50000000000 : ℝ) (50055461463/100000000000 : ℝ) (792494806741/1000000000000 : ℝ) (792494806759/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0363_exp_lower
  have heNumeric : (256863239989/125000000000 : ℝ)/4 ≤ Real.exp (-42628114898201/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256863239989/125000000000 : ℝ)/4 ≤ Real.exp ((33143/262144 : ℝ)-(792494806759/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33143/262144 : ℝ) (4143/32768 : ℝ) (792494806759/1000000000000 : ℝ) (256863239989/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0364; no trusted numerical premise.
theorem cover8_leaf0364_exp_radius : (998026354254116737/1000000000000000000 : ℝ) ≤ Real.exp ((-33145/2097152 : ℝ)/8) ∧ Real.exp ((-33145/2097152 : ℝ)/8) ≤ (499013177127058369/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33145/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0364_exp_lower : (920113690402296301/1000000000000000000 : ℝ) ≤ Real.exp ((-1065702912637/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065702912637/1600000000000 : ℝ)/8) ≤ (460056845201148151/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065702912637/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0364_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410981173661/200000000000 : ℝ) ≤ 4*Real.exp (4143/32768 : ℝ)*Real.exp (-mu (radius 8 (33145/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410981173661/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33145/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0364_exp_radius
  have hrNumeric : (984319472341/1000000000000 : ℝ) ≤ Real.exp (-33145/2097152 : ℝ) ∧ Real.exp (-33145/2097152 : ℝ) ≤ (492159736171/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984319472341/1000000000000 : ℝ) ≤ (radius 8 (33145/262144 : ℝ)) ∧ (radius 8 (33145/262144 : ℝ)) ≤ (492159736171/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33145/262144 : ℝ)) (984319472341/1000000000000 : ℝ) (492159736171/500000000000 : ℝ) (88197472141/500000000000 : ℝ) (5512342009/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33145/262144 : ℝ)) (984319472341/1000000000000 : ℝ) (492159736171/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33145/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984319472341/1000000000000 : ℝ) (492159736171/500000000000 : ℝ) (99215973617/100000000000 : ℝ) (992159736171/1000000000000 : ℝ) (124016094743/125000000000 : ℝ) (496064378973/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33145/262144 : ℝ)) 1 (99215973617/100000000000 : ℝ) (992159736171/1000000000000 : ℝ) (124016094743/125000000000 : ℝ) (496064378973/500000000000 : ℝ) (992144247057/1000000000000 : ℝ) (992144247059/1000000000000 : ℝ) (124018030867/125000000000 : ℝ) (496072123469/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33145/262144 : ℝ)) 2 (992144247057/1000000000000 : ℝ) (992144247059/1000000000000 : ℝ) (124018030867/125000000000 : ℝ) (496072123469/500000000000 : ℝ) (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ) (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33145/262144 : ℝ)) 3 (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ) (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ) (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ) (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33145/262144 : ℝ)) 4 (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ) (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ) (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ) (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33145/262144 : ℝ)) 5 (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ) (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ) (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ) (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33145/262144 : ℝ)) 6 (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ) (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ) (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ) (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33145/262144 : ℝ)) 7 (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ) (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ) (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ) (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33145/262144 : ℝ))) (88197472141/500000000000 : ℝ) (5512342009/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33145/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88197472141/500000000000 : ℝ) (5512342009/31250000000 : ℝ) (588197472141/1000000000000 : ℝ) (36762342009/62500000000 : ℝ) (104998495311/250000000000 : ℝ) (419993981253/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33145/262144 : ℝ))) 1 (588197472141/1000000000000 : ℝ) (36762342009/62500000000 : ℝ) (104998495311/250000000000 : ℝ) (419993981253/1000000000000 : ℝ) (126023931673/250000000000 : ℝ) (504095726699/1000000000000 : ℝ) (49703058063/100000000000 : ℝ) (248515290319/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33145/262144 : ℝ))) 2 (126023931673/250000000000 : ℝ) (504095726699/1000000000000 : ℝ) (49703058063/100000000000 : ℝ) (248515290319/500000000000 : ℝ) (500563153661/1000000000000 : ℝ) (500563153669/1000000000000 : ℝ) (500550688473/1000000000000 : ℝ) (500550688481/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33145/262144 : ℝ))) 3 (500563153661/1000000000000 : ℝ) (500563153669/1000000000000 : ℝ) (500550688473/1000000000000 : ℝ) (500550688481/1000000000000 : ℝ) (500556921067/1000000000000 : ℝ) (20022276843/40000000000 : ℝ) (125139230257/250000000000 : ℝ) (500556921037/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33145/262144 : ℝ))) 4 (500556921067/1000000000000 : ℝ) (20022276843/40000000000 : ℝ) (125139230257/250000000000 : ℝ) (500556921037/1000000000000 : ℝ) (500556921047/1000000000000 : ℝ) (15642403783/31250000000 : ℝ) (500556921047/1000000000000 : ℝ) (15642403783/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33145/262144 : ℝ))) 5 (500556921047/1000000000000 : ℝ) (15642403783/31250000000 : ℝ) (500556921047/1000000000000 : ℝ) (15642403783/31250000000 : ℝ) (500556921047/1000000000000 : ℝ) (15642403783/31250000000 : ℝ) (500556921047/1000000000000 : ℝ) (15642403783/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33145/262144 : ℝ))) 6 (500556921047/1000000000000 : ℝ) (15642403783/31250000000 : ℝ) (500556921047/1000000000000 : ℝ) (15642403783/31250000000 : ℝ) (500556921047/1000000000000 : ℝ) (15642403783/31250000000 : ℝ) (500556921047/1000000000000 : ℝ) (15642403783/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33145/262144 : ℝ))) 7 (500556921047/1000000000000 : ℝ) (15642403783/31250000000 : ℝ) (500556921047/1000000000000 : ℝ) (15642403783/31250000000 : ℝ) (500556921047/1000000000000 : ℝ) (15642403783/31250000000 : ℝ) (500556921047/1000000000000 : ℝ) (15642403783/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33145/262144 : ℝ)) hmem 8 (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ) (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33145/262144 : ℝ))) hcmem 8 (500556921047/1000000000000 : ℝ) (15642403783/31250000000 : ℝ) (500556921047/1000000000000 : ℝ) (15642403783/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33145/262144 : ℝ)) (248036061749/250000000000 : ℝ) (992144246999/1000000000000 : ℝ) (500556921047/1000000000000 : ℝ) (15642403783/31250000000 : ℝ) (792498646553/1000000000000 : ℝ) (79249864657/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0364_exp_lower
  have heNumeric : (410981173661/200000000000 : ℝ)/4 ≤ Real.exp (-1065702912637/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410981173661/200000000000 : ℝ)/4 ≤ Real.exp ((4143/32768 : ℝ)-(79249864657/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4143/32768 : ℝ) (33145/262144 : ℝ) (79249864657/100000000000 : ℝ) (410981173661/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0365; no trusted numerical premise.
theorem cover8_leaf0365_exp_radius : (249506573691778047/250000000000000000 : ℝ) ≤ Real.exp ((-16573/1048576 : ℝ)/8) ∧ Real.exp ((-16573/1048576 : ℝ)/8) ≤ (998026294767112189/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16573/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0365_exp_lower : (920113687523521147/1000000000000000000 : ℝ) ≤ Real.exp ((-42628118107383/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628118107383/64000000000000 : ℝ)/8) ≤ (230028421880880287/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628118107383/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0365_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054905816871/1000000000000 : ℝ) ≤ 4*Real.exp (33145/262144 : ℝ)*Real.exp (-mu (radius 8 (16573/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054905816871/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16573/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0365_exp_radius
  have hrNumeric : (984319002981/1000000000000 : ℝ) ≤ Real.exp (-16573/1048576 : ℝ) ∧ Real.exp (-16573/1048576 : ℝ) ≤ (492159501491/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984319002981/1000000000000 : ℝ) ≤ (radius 8 (16573/131072 : ℝ)) ∧ (radius 8 (16573/131072 : ℝ)) ≤ (492159501491/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16573/131072 : ℝ)) (984319002981/1000000000000 : ℝ) (492159501491/500000000000 : ℝ) (88198781693/500000000000 : ℝ) (344526491/1953125000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16573/131072 : ℝ)) (984319002981/1000000000000 : ℝ) (492159501491/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16573/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984319002981/1000000000000 : ℝ) (492159501491/500000000000 : ℝ) (99215950149/100000000000 : ℝ) (992159501491/1000000000000 : ℝ) (496064260701/500000000000 : ℝ) (248032130351/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16573/131072 : ℝ)) 1 (99215950149/100000000000 : ℝ) (992159501491/1000000000000 : ℝ) (496064260701/500000000000 : ℝ) (248032130351/250000000000 : ℝ) (496072005723/500000000000 : ℝ) (124018001431/125000000000 : ℝ) (39685760453/40000000000 : ℝ) (992144011327/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16573/131072 : ℝ)) 2 (496072005723/500000000000 : ℝ) (124018001431/125000000000 : ℝ) (39685760453/40000000000 : ℝ) (992144011327/1000000000000 : ℝ) (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ) (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16573/131072 : ℝ)) 3 (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ) (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ) (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ) (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16573/131072 : ℝ)) 4 (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ) (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ) (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ) (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16573/131072 : ℝ)) 5 (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ) (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ) (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ) (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16573/131072 : ℝ)) 6 (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ) (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ) (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ) (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16573/131072 : ℝ)) 7 (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ) (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ) (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ) (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16573/131072 : ℝ))) (88198781693/500000000000 : ℝ) (344526491/1953125000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16573/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88198781693/500000000000 : ℝ) (344526491/1953125000 : ℝ) (588198781693/1000000000000 : ℝ) (2297651491/3906250000 : ℝ) (419997099259/1000000000000 : ℝ) (419997099267/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16573/131072 : ℝ))) 1 (588198781693/1000000000000 : ℝ) (2297651491/3906250000 : ℝ) (419997099259/1000000000000 : ℝ) (419997099267/1000000000000 : ℝ) (126024485119/250000000000 : ℝ) (252048970241/500000000000 : ℝ) (124258244721/250000000000 : ℝ) (497032978891/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16573/131072 : ℝ))) 2 (126024485119/250000000000 : ℝ) (252048970241/500000000000 : ℝ) (124258244721/250000000000 : ℝ) (497032978891/1000000000000 : ℝ) (3128534123/6250000000 : ℝ) (500565459687/1000000000000 : ℝ) (156422811/312500000 : ℝ) (500552995207/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16573/131072 : ℝ))) 3 (3128534123/6250000000 : ℝ) (500565459687/1000000000000 : ℝ) (156422811/312500000 : ℝ) (500552995207/1000000000000 : ℝ) (6256990343/12500000000 : ℝ) (500559227447/1000000000000 : ℝ) (500559227401/1000000000000 : ℝ) (500559227409/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16573/131072 : ℝ))) 4 (6256990343/12500000000 : ℝ) (500559227447/1000000000000 : ℝ) (500559227401/1000000000000 : ℝ) (500559227409/1000000000000 : ℝ) (25027961371/50000000000 : ℝ) (125139806857/250000000000 : ℝ) (25027961371/50000000000 : ℝ) (125139806857/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16573/131072 : ℝ))) 5 (25027961371/50000000000 : ℝ) (125139806857/250000000000 : ℝ) (25027961371/50000000000 : ℝ) (125139806857/250000000000 : ℝ) (25027961371/50000000000 : ℝ) (125139806857/250000000000 : ℝ) (25027961371/50000000000 : ℝ) (125139806857/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16573/131072 : ℝ))) 6 (25027961371/50000000000 : ℝ) (125139806857/250000000000 : ℝ) (25027961371/50000000000 : ℝ) (125139806857/250000000000 : ℝ) (25027961371/50000000000 : ℝ) (125139806857/250000000000 : ℝ) (25027961371/50000000000 : ℝ) (125139806857/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16573/131072 : ℝ))) 7 (25027961371/50000000000 : ℝ) (125139806857/250000000000 : ℝ) (25027961371/50000000000 : ℝ) (125139806857/250000000000 : ℝ) (25027961371/50000000000 : ℝ) (125139806857/250000000000 : ℝ) (25027961371/50000000000 : ℝ) (125139806857/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16573/131072 : ℝ)) hmem 8 (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ) (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16573/131072 : ℝ))) hcmem 8 (25027961371/50000000000 : ℝ) (125139806857/250000000000 : ℝ) (25027961371/50000000000 : ℝ) (125139806857/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16573/131072 : ℝ)) (198428802277/200000000000 : ℝ) (248036002847/250000000000 : ℝ) (25027961371/50000000000 : ℝ) (125139806857/250000000000 : ℝ) (792502486281/1000000000000 : ℝ) (792502486297/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0365_exp_lower
  have heNumeric : (2054905816871/1000000000000 : ℝ)/4 ≤ Real.exp (-42628118107383/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054905816871/1000000000000 : ℝ)/4 ≤ Real.exp ((33145/262144 : ℝ)-(792502486297/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33145/262144 : ℝ) (16573/131072 : ℝ) (792502486297/1000000000000 : ℝ) (2054905816871/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0366; no trusted numerical premise.
theorem cover8_leaf0366_exp_radius : (199605247056022237/200000000000000000 : ℝ) ≤ Real.exp ((-33147/2097152 : ℝ)/8) ∧ Real.exp ((-33147/2097152 : ℝ)/8) ≤ (499013117640055593/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33147/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0366_exp_lower : (230028421163601799/250000000000000000 : ℝ) ≤ Real.exp ((-4262811970391/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262811970391/6400000000000 : ℝ)/8) ≤ (920113684654407197/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262811970391/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0366_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490576561/100000000000 : ℝ) ≤ 4*Real.exp (16573/131072 : ℝ)*Real.exp (-mu (radius 8 (33147/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (205490576561/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33147/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0366_exp_radius
  have hrNumeric : (492159266811/500000000000 : ℝ) ≤ Real.exp (-33147/2097152 : ℝ) ∧ Real.exp (-33147/2097152 : ℝ) ≤ (984318533623/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492159266811/500000000000 : ℝ) ≤ (radius 8 (33147/262144 : ℝ)) ∧ (radius 8 (33147/262144 : ℝ)) ≤ (984318533623/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33147/262144 : ℝ)) (492159266811/500000000000 : ℝ) (984318533623/1000000000000 : ℝ) (176400182443/1000000000000 : ℝ) (3528003649/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33147/262144 : ℝ)) (492159266811/500000000000 : ℝ) (984318533623/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33147/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492159266811/500000000000 : ℝ) (984318533623/1000000000000 : ℝ) (992159266811/1000000000000 : ℝ) (248039816703/250000000000 : ℝ) (992128284861/1000000000000 : ℝ) (496064142431/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33147/262144 : ℝ)) 1 (992159266811/1000000000000 : ℝ) (248039816703/250000000000 : ℝ) (992128284861/1000000000000 : ℝ) (496064142431/500000000000 : ℝ) (248035943959/250000000000 : ℝ) (992143775837/1000000000000 : ℝ) (198428755143/200000000000 : ℝ) (992143775717/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33147/262144 : ℝ)) 2 (248035943959/250000000000 : ℝ) (992143775837/1000000000000 : ℝ) (198428755143/200000000000 : ℝ) (992143775717/1000000000000 : ℝ) (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ) (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33147/262144 : ℝ)) 3 (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ) (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ) (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ) (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33147/262144 : ℝ)) 4 (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ) (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ) (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ) (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33147/262144 : ℝ)) 5 (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ) (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ) (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ) (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33147/262144 : ℝ)) 6 (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ) (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ) (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ) (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33147/262144 : ℝ)) 7 (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ) (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ) (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ) (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33147/262144 : ℝ))) (176400182443/1000000000000 : ℝ) (3528003649/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33147/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176400182443/1000000000000 : ℝ) (3528003649/20000000000 : ℝ) (588200091221/1000000000000 : ℝ) (23528003649/40000000000 : ℝ) (420000217193/1000000000000 : ℝ) (420000217203/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33147/262144 : ℝ))) 1 (588200091221/1000000000000 : ℝ) (23528003649/40000000000 : ℝ) (420000217193/1000000000000 : ℝ) (420000217203/1000000000000 : ℝ) (504100154207/1000000000000 : ℝ) (252050077107/500000000000 : ℝ) (124258844269/250000000000 : ℝ) (99407075417/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33147/262144 : ℝ))) 2 (504100154207/1000000000000 : ℝ) (252050077107/500000000000 : ℝ) (124258844269/250000000000 : ℝ) (99407075417/200000000000 : ℝ) (500567765641/1000000000000 : ℝ) (10011355313/20000000000 : ℝ) (50055530187/100000000000 : ℝ) (500555301879/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33147/262144 : ℝ))) 3 (500567765641/1000000000000 : ℝ) (10011355313/20000000000 : ℝ) (50055530187/100000000000 : ℝ) (500555301879/1000000000000 : ℝ) (100112306751/200000000000 : ℝ) (100112306753/200000000000 : ℝ) (125140383429/250000000000 : ℝ) (250280766863/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33147/262144 : ℝ))) 4 (100112306751/200000000000 : ℝ) (100112306753/200000000000 : ℝ) (125140383429/250000000000 : ℝ) (250280766863/500000000000 : ℝ) (100112306747/200000000000 : ℝ) (250280766873/500000000000 : ℝ) (100112306747/200000000000 : ℝ) (250280766873/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33147/262144 : ℝ))) 5 (100112306747/200000000000 : ℝ) (250280766873/500000000000 : ℝ) (100112306747/200000000000 : ℝ) (250280766873/500000000000 : ℝ) (100112306747/200000000000 : ℝ) (250280766873/500000000000 : ℝ) (100112306747/200000000000 : ℝ) (250280766873/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33147/262144 : ℝ))) 6 (100112306747/200000000000 : ℝ) (250280766873/500000000000 : ℝ) (100112306747/200000000000 : ℝ) (250280766873/500000000000 : ℝ) (100112306747/200000000000 : ℝ) (250280766873/500000000000 : ℝ) (100112306747/200000000000 : ℝ) (250280766873/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33147/262144 : ℝ))) 7 (100112306747/200000000000 : ℝ) (250280766873/500000000000 : ℝ) (100112306747/200000000000 : ℝ) (250280766873/500000000000 : ℝ) (100112306747/200000000000 : ℝ) (250280766873/500000000000 : ℝ) (100112306747/200000000000 : ℝ) (250280766873/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33147/262144 : ℝ)) hmem 8 (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ) (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33147/262144 : ℝ))) hcmem 8 (100112306747/200000000000 : ℝ) (250280766873/500000000000 : ℝ) (100112306747/200000000000 : ℝ) (250280766873/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33147/262144 : ℝ)) (39685751031/40000000000 : ℝ) (992143775777/1000000000000 : ℝ) (100112306747/200000000000 : ℝ) (250280766873/500000000000 : ℝ) (4953164537/6250000000 : ℝ) (39625316297/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0366_exp_lower
  have heNumeric : (205490576561/100000000000 : ℝ)/4 ≤ Real.exp (-4262811970391/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490576561/100000000000 : ℝ)/4 ≤ Real.exp ((16573/131072 : ℝ)-(39625316297/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16573/131072 : ℝ) (33147/262144 : ℝ) (39625316297/50000000000 : ℝ) (205490576561/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0367; no trusted numerical premise.
theorem cover8_leaf0367_exp_radius : (998026175793113727/1000000000000000000 : ℝ) ≤ Real.exp ((-8287/524288 : ℝ)/8) ∧ Real.exp ((-8287/524288 : ℝ)/8) ≤ (7797079498383701/7812500000000000 : ℝ) := by
  have h := exp_small_bounds ((-8287/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0367_exp_lower : (920113681793459263/1000000000000000000 : ℝ) ≤ Real.exp ((-42628121295893/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628121295893/64000000000000 : ℝ)/8) ≤ (14376776278022801/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628121295893/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0367_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410981142899/200000000000 : ℝ) ≤ 4*Real.exp (33147/262144 : ℝ)*Real.exp (-mu (radius 8 (8287/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (410981142899/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8287/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0367_exp_radius
  have hrNumeric : (492159032131/500000000000 : ℝ) ≤ Real.exp (-8287/524288 : ℝ) ∧ Real.exp (-8287/524288 : ℝ) ≤ (984318064263/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492159032131/500000000000 : ℝ) ≤ (radius 8 (8287/65536 : ℝ)) ∧ (radius 8 (8287/65536 : ℝ)) ≤ (984318064263/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8287/65536 : ℝ)) (492159032131/500000000000 : ℝ) (984318064263/1000000000000 : ℝ) (176402801467/1000000000000 : ℝ) (176402801473/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8287/65536 : ℝ)) (492159032131/500000000000 : ℝ) (984318064263/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8287/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492159032131/500000000000 : ℝ) (984318064263/1000000000000 : ℝ) (992159032131/1000000000000 : ℝ) (248039758033/250000000000 : ℝ) (992128048319/1000000000000 : ℝ) (3100400151/3125000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8287/65536 : ℝ)) 1 (992159032131/1000000000000 : ℝ) (248039758033/250000000000 : ℝ) (992128048319/1000000000000 : ℝ) (3100400151/3125000000 : ℝ) (39685741609/40000000000 : ℝ) (496071770113/500000000000 : ℝ) (124017942513/125000000000 : ℝ) (496071770053/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8287/65536 : ℝ)) 2 (39685741609/40000000000 : ℝ) (496071770113/500000000000 : ℝ) (124017942513/125000000000 : ℝ) (496071770053/500000000000 : ℝ) (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ) (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8287/65536 : ℝ)) 3 (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ) (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ) (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ) (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8287/65536 : ℝ)) 4 (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ) (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ) (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ) (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8287/65536 : ℝ)) 5 (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ) (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ) (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ) (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8287/65536 : ℝ)) 6 (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ) (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ) (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ) (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8287/65536 : ℝ)) 7 (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ) (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ) (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ) (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8287/65536 : ℝ))) (176402801467/1000000000000 : ℝ) (176402801473/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8287/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176402801467/1000000000000 : ℝ) (176402801473/1000000000000 : ℝ) (588201400733/1000000000000 : ℝ) (588201400737/1000000000000 : ℝ) (210001667533/500000000000 : ℝ) (210001667537/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8287/65536 : ℝ))) 1 (588201400733/1000000000000 : ℝ) (588201400737/1000000000000 : ℝ) (210001667533/500000000000 : ℝ) (210001667537/500000000000 : ℝ) (504102367899/1000000000000 : ℝ) (252051183953/500000000000 : ℝ) (248518887611/500000000000 : ℝ) (49703777523/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8287/65536 : ℝ))) 2 (504102367899/1000000000000 : ℝ) (252051183953/500000000000 : ℝ) (248518887611/500000000000 : ℝ) (49703777523/100000000000 : ℝ) (12514251789/25000000000 : ℝ) (31285629473/62500000000 : ℝ) (500557608497/1000000000000 : ℝ) (100111521701/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8287/65536 : ℝ))) 3 (12514251789/25000000000 : ℝ) (31285629473/62500000000 : ℝ) (500557608497/1000000000000 : ℝ) (100111521701/200000000000 : ℝ) (125140960007/250000000000 : ℝ) (500563840037/1000000000000 : ℝ) (500563839989/1000000000000 : ℝ) (250281919999/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8287/65536 : ℝ))) 4 (125140960007/250000000000 : ℝ) (500563840037/1000000000000 : ℝ) (500563839989/1000000000000 : ℝ) (250281919999/500000000000 : ℝ) (62570480001/125000000000 : ℝ) (250281920009/500000000000 : ℝ) (62570480001/125000000000 : ℝ) (250281920009/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8287/65536 : ℝ))) 5 (62570480001/125000000000 : ℝ) (250281920009/500000000000 : ℝ) (62570480001/125000000000 : ℝ) (250281920009/500000000000 : ℝ) (62570480001/125000000000 : ℝ) (250281920009/500000000000 : ℝ) (62570480001/125000000000 : ℝ) (250281920009/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8287/65536 : ℝ))) 6 (62570480001/125000000000 : ℝ) (250281920009/500000000000 : ℝ) (62570480001/125000000000 : ℝ) (250281920009/500000000000 : ℝ) (62570480001/125000000000 : ℝ) (250281920009/500000000000 : ℝ) (62570480001/125000000000 : ℝ) (250281920009/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8287/65536 : ℝ))) 7 (62570480001/125000000000 : ℝ) (250281920009/500000000000 : ℝ) (62570480001/125000000000 : ℝ) (250281920009/500000000000 : ℝ) (62570480001/125000000000 : ℝ) (250281920009/500000000000 : ℝ) (62570480001/125000000000 : ℝ) (250281920009/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8287/65536 : ℝ)) hmem 8 (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ) (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8287/65536 : ℝ))) hcmem 8 (62570480001/125000000000 : ℝ) (250281920009/500000000000 : ℝ) (62570480001/125000000000 : ℝ) (250281920009/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8287/65536 : ℝ)) (248035885041/250000000000 : ℝ) (496071770083/500000000000 : ℝ) (62570480001/125000000000 : ℝ) (250281920009/500000000000 : ℝ) (396255082747/500000000000 : ℝ) (99063770689/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0367_exp_lower
  have heNumeric : (410981142899/200000000000 : ℝ)/4 ≤ Real.exp (-42628121295893/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410981142899/200000000000 : ℝ)/4 ≤ Real.exp ((33147/262144 : ℝ)-(99063770689/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33147/262144 : ℝ) (8287/65536 : ℝ) (99063770689/125000000000 : ℝ) (410981142899/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0368; no trusted numerical premise.
theorem cover8_leaf0368_exp_radius : (199605223261223963/200000000000000000 : ℝ) ≤ Real.exp ((-33149/2097152 : ℝ)/8) ∧ Real.exp ((-33149/2097152 : ℝ)/8) ≤ (124753264538264977/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33149/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0368_exp_lower : (920113678942057519/1000000000000000000 : ℝ) ≤ Real.exp ((-10657030720641/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657030720641/16000000000000 : ℝ)/8) ≤ (11501420986775719/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657030720641/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0368_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (41098113271/20000000000 : ℝ) ≤ 4*Real.exp (8287/65536 : ℝ)*Real.exp (-mu (radius 8 (33149/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (41098113271/20000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33149/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0368_exp_radius
  have hrNumeric : (984317594903/1000000000000 : ℝ) ≤ Real.exp (-33149/2097152 : ℝ) ∧ Real.exp (-33149/2097152 : ℝ) ≤ (123039699363/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984317594903/1000000000000 : ℝ) ≤ (radius 8 (33149/262144 : ℝ)) ∧ (radius 8 (33149/262144 : ℝ)) ≤ (123039699363/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33149/262144 : ℝ)) (984317594903/1000000000000 : ℝ) (123039699363/125000000000 : ℝ) (35281084089/200000000000 : ℝ) (176405420451/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33149/262144 : ℝ)) (984317594903/1000000000000 : ℝ) (123039699363/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33149/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984317594903/1000000000000 : ℝ) (123039699363/125000000000 : ℝ) (992158797451/1000000000000 : ℝ) (248039699363/250000000000 : ℝ) (992127811777/1000000000000 : ℝ) (992127811779/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33149/262144 : ℝ)) 1 (992158797451/1000000000000 : ℝ) (248039699363/250000000000 : ℝ) (992127811777/1000000000000 : ℝ) (992127811779/1000000000000 : ℝ) (496071652307/500000000000 : ℝ) (124017913077/125000000000 : ℝ) (992143304493/1000000000000 : ℝ) (198428660899/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33149/262144 : ℝ)) 2 (496071652307/500000000000 : ℝ) (124017913077/125000000000 : ℝ) (992143304493/1000000000000 : ℝ) (198428660899/200000000000 : ℝ) (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ) (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33149/262144 : ℝ)) 3 (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ) (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ) (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ) (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33149/262144 : ℝ)) 4 (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ) (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ) (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ) (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33149/262144 : ℝ)) 5 (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ) (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ) (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ) (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33149/262144 : ℝ)) 6 (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ) (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ) (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ) (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33149/262144 : ℝ)) 7 (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ) (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ) (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ) (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33149/262144 : ℝ))) (35281084089/200000000000 : ℝ) (176405420451/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33149/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35281084089/200000000000 : ℝ) (176405420451/1000000000000 : ℝ) (294101355111/500000000000 : ℝ) (294101355113/500000000000 : ℝ) (420006452861/1000000000000 : ℝ) (420006452869/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33149/262144 : ℝ))) 1 (294101355111/500000000000 : ℝ) (294101355113/500000000000 : ℝ) (420006452861/1000000000000 : ℝ) (420006452869/1000000000000 : ℝ) (504104581541/1000000000000 : ℝ) (126026145387/250000000000 : ℝ) (497040173309/1000000000000 : ℝ) (124260043329/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33149/262144 : ℝ))) 2 (504104581541/1000000000000 : ℝ) (126026145387/250000000000 : ℝ) (497040173309/1000000000000 : ℝ) (124260043329/250000000000 : ℝ) (20022895097/40000000000 : ℝ) (62571547179/125000000000 : ℝ) (50055991507/100000000000 : ℝ) (250279957539/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33149/262144 : ℝ))) 3 (20022895097/40000000000 : ℝ) (62571547179/125000000000 : ℝ) (50055991507/100000000000 : ℝ) (250279957539/500000000000 : ℝ) (500566146247/1000000000000 : ℝ) (100113229251/200000000000 : ℝ) (15642692069/31250000000 : ℝ) (500566146217/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33149/262144 : ℝ))) 4 (500566146247/1000000000000 : ℝ) (100113229251/200000000000 : ℝ) (15642692069/31250000000 : ℝ) (500566146217/1000000000000 : ℝ) (500566146227/1000000000000 : ℝ) (125141536559/250000000000 : ℝ) (500566146227/1000000000000 : ℝ) (125141536559/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33149/262144 : ℝ))) 5 (500566146227/1000000000000 : ℝ) (125141536559/250000000000 : ℝ) (500566146227/1000000000000 : ℝ) (125141536559/250000000000 : ℝ) (500566146227/1000000000000 : ℝ) (125141536559/250000000000 : ℝ) (500566146227/1000000000000 : ℝ) (125141536559/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33149/262144 : ℝ))) 6 (500566146227/1000000000000 : ℝ) (125141536559/250000000000 : ℝ) (500566146227/1000000000000 : ℝ) (125141536559/250000000000 : ℝ) (500566146227/1000000000000 : ℝ) (125141536559/250000000000 : ℝ) (500566146227/1000000000000 : ℝ) (125141536559/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33149/262144 : ℝ))) 7 (500566146227/1000000000000 : ℝ) (125141536559/250000000000 : ℝ) (500566146227/1000000000000 : ℝ) (125141536559/250000000000 : ℝ) (500566146227/1000000000000 : ℝ) (125141536559/250000000000 : ℝ) (500566146227/1000000000000 : ℝ) (125141536559/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33149/262144 : ℝ)) hmem 8 (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ) (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33149/262144 : ℝ))) hcmem 8 (500566146227/1000000000000 : ℝ) (125141536559/250000000000 : ℝ) (500566146227/1000000000000 : ℝ) (125141536559/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33149/262144 : ℝ)) (992143304553/1000000000000 : ℝ) (248035826139/250000000000 : ℝ) (500566146227/1000000000000 : ℝ) (125141536559/250000000000 : ℝ) (792514004983/1000000000000 : ℝ) (792514005001/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0368_exp_lower
  have heNumeric : (41098113271/20000000000 : ℝ)/4 ≤ Real.exp (-10657030720641/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (41098113271/20000000000 : ℝ)/4 ≤ Real.exp ((8287/65536 : ℝ)-(792514005001/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8287/65536 : ℝ) (33149/262144 : ℝ) (792514005001/1000000000000 : ℝ) (41098113271/20000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0369; no trusted numerical premise.
theorem cover8_leaf0369_exp_radius : (998026056819129449/1000000000000000000 : ℝ) ≤ Real.exp ((-16575/1048576 : ℝ)/8) ∧ Real.exp ((-16575/1048576 : ℝ)/8) ≤ (19960521136382589/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16575/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0369_exp_lower : (920113676099511877/1000000000000000000 : ℝ) ≤ Real.exp ((-42628124464307/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628124464307/64000000000000 : ℝ)/8) ≤ (460056838049755939/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628124464307/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0369_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726403191/250000000000 : ℝ) ≤ 4*Real.exp (33149/262144 : ℝ)*Real.exp (-mu (radius 8 (16575/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513726403191/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16575/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0369_exp_radius
  have hrNumeric : (123039640693/125000000000 : ℝ) ≤ Real.exp (-16575/1048576 : ℝ) ∧ Real.exp (-16575/1048576 : ℝ) ≤ (196863425109/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123039640693/125000000000 : ℝ) ≤ (radius 8 (16575/131072 : ℝ)) ∧ (radius 8 (16575/131072 : ℝ)) ≤ (196863425109/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16575/131072 : ℝ)) (123039640693/125000000000 : ℝ) (196863425109/200000000000 : ℝ) (88204019691/500000000000 : ℝ) (176408039389/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16575/131072 : ℝ)) (123039640693/125000000000 : ℝ) (196863425109/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16575/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123039640693/125000000000 : ℝ) (196863425109/200000000000 : ℝ) (248039640693/250000000000 : ℝ) (992158562773/1000000000000 : ℝ) (248031893809/250000000000 : ℝ) (992127575237/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16575/131072 : ℝ)) 1 (248039640693/250000000000 : ℝ) (992158562773/1000000000000 : ℝ) (248031893809/250000000000 : ℝ) (992127575237/1000000000000 : ℝ) (248035767251/250000000000 : ℝ) (198428613801/200000000000 : ℝ) (992143068883/1000000000000 : ℝ) (198428613777/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16575/131072 : ℝ)) 2 (248035767251/250000000000 : ℝ) (198428613801/200000000000 : ℝ) (992143068883/1000000000000 : ℝ) (198428613777/200000000000 : ℝ) (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ) (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16575/131072 : ℝ)) 3 (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ) (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ) (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ) (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16575/131072 : ℝ)) 4 (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ) (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ) (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ) (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16575/131072 : ℝ)) 5 (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ) (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ) (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ) (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16575/131072 : ℝ)) 6 (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ) (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ) (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ) (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16575/131072 : ℝ)) 7 (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ) (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ) (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ) (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16575/131072 : ℝ))) (88204019691/500000000000 : ℝ) (176408039389/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16575/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88204019691/500000000000 : ℝ) (176408039389/1000000000000 : ℝ) (588204019691/1000000000000 : ℝ) (117640803939/200000000000 : ℝ) (420009570583/1000000000000 : ℝ) (420009570593/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16575/131072 : ℝ))) 1 (588204019691/1000000000000 : ℝ) (117640803939/200000000000 : ℝ) (420009570583/1000000000000 : ℝ) (420009570593/1000000000000 : ℝ) (504106795137/1000000000000 : ℝ) (63013349393/125000000000 : ℝ) (497042571341/1000000000000 : ℝ) (497042571349/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16575/131072 : ℝ))) 2 (504106795137/1000000000000 : ℝ) (63013349393/125000000000 : ℝ) (497042571341/1000000000000 : ℝ) (497042571349/1000000000000 : ℝ) (500574683239/1000000000000 : ℝ) (500574683247/1000000000000 : ℝ) (62570277699/125000000000 : ℝ) (625702777/1250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16575/131072 : ℝ))) 3 (500574683239/1000000000000 : ℝ) (500574683247/1000000000000 : ℝ) (62570277699/125000000000 : ℝ) (625702777/1250000000 : ℝ) (100113690483/200000000000 : ℝ) (62571056553/125000000000 : ℝ) (62571056547/125000000000 : ℝ) (100113690477/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16575/131072 : ℝ))) 4 (100113690483/200000000000 : ℝ) (62571056553/125000000000 : ℝ) (62571056547/125000000000 : ℝ) (100113690477/200000000000 : ℝ) (100113690479/200000000000 : ℝ) (100113690481/200000000000 : ℝ) (100113690479/200000000000 : ℝ) (100113690481/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16575/131072 : ℝ))) 5 (100113690479/200000000000 : ℝ) (100113690481/200000000000 : ℝ) (100113690479/200000000000 : ℝ) (100113690481/200000000000 : ℝ) (100113690479/200000000000 : ℝ) (100113690481/200000000000 : ℝ) (100113690479/200000000000 : ℝ) (100113690481/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16575/131072 : ℝ))) 6 (100113690479/200000000000 : ℝ) (100113690481/200000000000 : ℝ) (100113690479/200000000000 : ℝ) (100113690481/200000000000 : ℝ) (100113690479/200000000000 : ℝ) (100113690481/200000000000 : ℝ) (100113690479/200000000000 : ℝ) (100113690481/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16575/131072 : ℝ))) 7 (100113690479/200000000000 : ℝ) (100113690481/200000000000 : ℝ) (100113690479/200000000000 : ℝ) (100113690481/200000000000 : ℝ) (100113690479/200000000000 : ℝ) (100113690481/200000000000 : ℝ) (100113690479/200000000000 : ℝ) (100113690481/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16575/131072 : ℝ)) hmem 8 (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ) (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16575/131072 : ℝ))) hcmem 8 (100113690479/200000000000 : ℝ) (100113690481/200000000000 : ℝ) (100113690479/200000000000 : ℝ) (100113690481/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16575/131072 : ℝ)) (992143068943/1000000000000 : ℝ) (198428613789/200000000000 : ℝ) (100113690479/200000000000 : ℝ) (100113690481/200000000000 : ℝ) (396258922197/500000000000 : ℝ) (792517844413/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0369_exp_lower
  have heNumeric : (513726403191/250000000000 : ℝ)/4 ≤ Real.exp (-42628124464307/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726403191/250000000000 : ℝ)/4 ≤ Real.exp ((33149/262144 : ℝ)-(792517844413/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33149/262144 : ℝ) (16575/131072 : ℝ) (792517844413/1000000000000 : ℝ) (513726403191/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0370; no trusted numerical premise.
theorem cover8_leaf0370_exp_radius : (998025997332142629/1000000000000000000 : ℝ) ≤ Real.exp ((-33151/2097152 : ℝ)/8) ∧ Real.exp ((-33151/2097152 : ℝ)/8) ≤ (99802599733214263/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33151/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0370_exp_lower : (115014209158242169/125000000000000000 : ℝ) ≤ Real.exp ((-21314063020529/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314063020529/32000000000000 : ℝ)/8) ≤ (920113673265937353/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314063020529/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0370_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452781069/500000000000 : ℝ) ≤ 4*Real.exp (16575/131072 : ℝ)*Real.exp (-mu (radius 8 (33151/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452781069/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33151/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0370_exp_radius
  have hrNumeric : (196863331237/200000000000 : ℝ) ≤ Real.exp (-33151/2097152 : ℝ) ∧ Real.exp (-33151/2097152 : ℝ) ≤ (492158328093/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196863331237/200000000000 : ℝ) ≤ (radius 8 (33151/262144 : ℝ)) ∧ (radius 8 (33151/262144 : ℝ)) ≤ (492158328093/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33151/262144 : ℝ)) (196863331237/200000000000 : ℝ) (492158328093/500000000000 : ℝ) (4410266457/25000000000 : ℝ) (88205329143/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33151/262144 : ℝ)) (196863331237/200000000000 : ℝ) (492158328093/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33151/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196863331237/200000000000 : ℝ) (492158328093/500000000000 : ℝ) (248039582023/250000000000 : ℝ) (992158328093/1000000000000 : ℝ) (496063669347/500000000000 : ℝ) (198425467739/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33151/262144 : ℝ)) 1 (248039582023/250000000000 : ℝ) (992158328093/1000000000000 : ℝ) (496063669347/500000000000 : ℝ) (198425467739/200000000000 : ℝ) (992142833393/1000000000000 : ℝ) (496071416697/500000000000 : ℝ) (124017854159/125000000000 : ℝ) (496071416637/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33151/262144 : ℝ)) 2 (992142833393/1000000000000 : ℝ) (496071416697/500000000000 : ℝ) (124017854159/125000000000 : ℝ) (496071416637/500000000000 : ℝ) (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ) (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33151/262144 : ℝ)) 3 (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ) (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ) (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ) (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33151/262144 : ℝ)) 4 (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ) (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ) (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ) (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33151/262144 : ℝ)) 5 (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ) (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ) (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ) (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33151/262144 : ℝ)) 6 (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ) (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ) (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ) (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33151/262144 : ℝ)) 7 (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ) (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ) (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ) (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33151/262144 : ℝ))) (4410266457/25000000000 : ℝ) (88205329143/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33151/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4410266457/25000000000 : ℝ) (88205329143/500000000000 : ℝ) (29410266457/50000000000 : ℝ) (588205329143/1000000000000 : ℝ) (105003172059/250000000000 : ℝ) (84002537649/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33151/262144 : ℝ))) 1 (29410266457/50000000000 : ℝ) (588205329143/1000000000000 : ℝ) (105003172059/250000000000 : ℝ) (84002537649/200000000000 : ℝ) (31506813043/62500000000 : ℝ) (252054504347/500000000000 : ℝ) (12426124233/25000000000 : ℝ) (31065310583/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33151/262144 : ℝ))) 2 (31506813043/62500000000 : ℝ) (252054504347/500000000000 : ℝ) (12426124233/25000000000 : ℝ) (31065310583/62500000000 : ℝ) (125144247251/250000000000 : ℝ) (500576989011/1000000000000 : ℝ) (100112905613/200000000000 : ℝ) (500564528073/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33151/262144 : ℝ))) 3 (125144247251/250000000000 : ℝ) (500576989011/1000000000000 : ℝ) (100112905613/200000000000 : ℝ) (500564528073/1000000000000 : ℝ) (250285379267/500000000000 : ℝ) (250285379271/500000000000 : ℝ) (100114151699/200000000000 : ℝ) (62571344813/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33151/262144 : ℝ))) 4 (250285379267/500000000000 : ℝ) (250285379271/500000000000 : ℝ) (100114151699/200000000000 : ℝ) (62571344813/125000000000 : ℝ) (250285379257/500000000000 : ℝ) (500570758523/1000000000000 : ℝ) (250285379257/500000000000 : ℝ) (500570758523/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33151/262144 : ℝ))) 5 (250285379257/500000000000 : ℝ) (500570758523/1000000000000 : ℝ) (250285379257/500000000000 : ℝ) (500570758523/1000000000000 : ℝ) (250285379257/500000000000 : ℝ) (500570758523/1000000000000 : ℝ) (250285379257/500000000000 : ℝ) (500570758523/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33151/262144 : ℝ))) 6 (250285379257/500000000000 : ℝ) (500570758523/1000000000000 : ℝ) (250285379257/500000000000 : ℝ) (500570758523/1000000000000 : ℝ) (250285379257/500000000000 : ℝ) (500570758523/1000000000000 : ℝ) (250285379257/500000000000 : ℝ) (500570758523/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33151/262144 : ℝ))) 7 (250285379257/500000000000 : ℝ) (500570758523/1000000000000 : ℝ) (250285379257/500000000000 : ℝ) (500570758523/1000000000000 : ℝ) (250285379257/500000000000 : ℝ) (500570758523/1000000000000 : ℝ) (250285379257/500000000000 : ℝ) (500570758523/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33151/262144 : ℝ)) hmem 8 (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ) (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33151/262144 : ℝ))) hcmem 8 (250285379257/500000000000 : ℝ) (500570758523/1000000000000 : ℝ) (250285379257/500000000000 : ℝ) (500570758523/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33151/262144 : ℝ)) (248035708333/250000000000 : ℝ) (496071416667/500000000000 : ℝ) (250285379257/500000000000 : ℝ) (500570758523/1000000000000 : ℝ) (79252168373/100000000000 : ℝ) (792521683747/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0370_exp_lower
  have heNumeric : (1027452781069/500000000000 : ℝ)/4 ≤ Real.exp (-21314063020529/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452781069/500000000000 : ℝ)/4 ≤ Real.exp ((16575/131072 : ℝ)-(792521683747/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16575/131072 : ℝ) (33151/262144 : ℝ) (792521683747/1000000000000 : ℝ) (1027452781069/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0371; no trusted numerical premise.
theorem cover8_leaf0371_exp_radius : (499012968922579677/500000000000000000 : ℝ) ≤ Real.exp ((-259/16384 : ℝ)/8) ∧ Real.exp ((-259/16384 : ℝ)/8) ≤ (199605187569031871/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-259/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0371_exp_lower : (230028417610275979/250000000000000000 : ℝ) ≤ Real.exp ((-8525625522589/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525625522589/12800000000000 : ℝ)/8) ≤ (920113670441103917/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525625522589/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0371_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726377917/250000000000 : ℝ) ≤ 4*Real.exp (33151/262144 : ℝ)*Real.exp (-mu (radius 8 (259/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (513726377917/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (259/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0371_exp_radius
  have hrNumeric : (492158093413/500000000000 : ℝ) ≤ Real.exp (-259/16384 : ℝ) ∧ Real.exp (-259/16384 : ℝ) ≤ (984316186827/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492158093413/500000000000 : ℝ) ≤ (radius 8 (259/2048 : ℝ)) ∧ (radius 8 (259/2048 : ℝ)) ≤ (984316186827/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (259/2048 : ℝ)) (492158093413/500000000000 : ℝ) (984316186827/1000000000000 : ℝ) (176413277137/1000000000000 : ℝ) (176413277143/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (259/2048 : ℝ)) (492158093413/500000000000 : ℝ) (984316186827/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (259/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492158093413/500000000000 : ℝ) (984316186827/1000000000000 : ℝ) (992158093413/1000000000000 : ℝ) (496079046707/500000000000 : ℝ) (124015887769/125000000000 : ℝ) (496063551077/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (259/2048 : ℝ)) 1 (992158093413/1000000000000 : ℝ) (496079046707/500000000000 : ℝ) (124015887769/125000000000 : ℝ) (496063551077/500000000000 : ℝ) (496071298891/500000000000 : ℝ) (124017824723/125000000000 : ℝ) (992142597661/1000000000000 : ℝ) (992142597663/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (259/2048 : ℝ)) 2 (496071298891/500000000000 : ℝ) (124017824723/125000000000 : ℝ) (992142597661/1000000000000 : ℝ) (992142597663/1000000000000 : ℝ) (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ) (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (259/2048 : ℝ)) 3 (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ) (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ) (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ) (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (259/2048 : ℝ)) 4 (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ) (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ) (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ) (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (259/2048 : ℝ)) 5 (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ) (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ) (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ) (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (259/2048 : ℝ)) 6 (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ) (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ) (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ) (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (259/2048 : ℝ)) 7 (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ) (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ) (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ) (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (259/2048 : ℝ))) (176413277137/1000000000000 : ℝ) (176413277143/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (259/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176413277137/1000000000000 : ℝ) (176413277143/1000000000000 : ℝ) (73525829821/125000000000 : ℝ) (147051659643/250000000000 : ℝ) (210007902909/500000000000 : ℝ) (210007902913/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (259/2048 : ℝ))) 1 (73525829821/125000000000 : ℝ) (147051659643/250000000000 : ℝ) (210007902909/500000000000 : ℝ) (210007902913/500000000000 : ℝ) (504111222193/1000000000000 : ℝ) (504111222199/1000000000000 : ℝ) (99409473449/200000000000 : ℝ) (124261841813/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (259/2048 : ℝ))) 2 (504111222193/1000000000000 : ℝ) (504111222199/1000000000000 : ℝ) (99409473449/200000000000 : ℝ) (124261841813/250000000000 : ℝ) (500579294719/1000000000000 : ℝ) (250289647363/500000000000 : ℝ) (62570854311/125000000000 : ℝ) (100113366899/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (259/2048 : ℝ))) 3 (500579294719/1000000000000 : ℝ) (250289647363/500000000000 : ℝ) (62570854311/125000000000 : ℝ) (100113366899/200000000000 : ℝ) (500573064603/1000000000000 : ℝ) (500573064611/1000000000000 : ℝ) (125143266141/250000000000 : ℝ) (125143266143/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (259/2048 : ℝ))) 4 (500573064603/1000000000000 : ℝ) (500573064611/1000000000000 : ℝ) (125143266141/250000000000 : ℝ) (125143266143/250000000000 : ℝ) (500573064583/1000000000000 : ℝ) (31285816537/62500000000 : ℝ) (500573064583/1000000000000 : ℝ) (31285816537/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (259/2048 : ℝ))) 5 (500573064583/1000000000000 : ℝ) (31285816537/62500000000 : ℝ) (500573064583/1000000000000 : ℝ) (31285816537/62500000000 : ℝ) (500573064583/1000000000000 : ℝ) (31285816537/62500000000 : ℝ) (500573064583/1000000000000 : ℝ) (31285816537/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (259/2048 : ℝ))) 6 (500573064583/1000000000000 : ℝ) (31285816537/62500000000 : ℝ) (500573064583/1000000000000 : ℝ) (31285816537/62500000000 : ℝ) (500573064583/1000000000000 : ℝ) (31285816537/62500000000 : ℝ) (500573064583/1000000000000 : ℝ) (31285816537/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (259/2048 : ℝ))) 7 (500573064583/1000000000000 : ℝ) (31285816537/62500000000 : ℝ) (500573064583/1000000000000 : ℝ) (31285816537/62500000000 : ℝ) (500573064583/1000000000000 : ℝ) (31285816537/62500000000 : ℝ) (500573064583/1000000000000 : ℝ) (31285816537/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (259/2048 : ℝ)) hmem 8 (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ) (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (259/2048 : ℝ))) hcmem 8 (500573064583/1000000000000 : ℝ) (31285816537/62500000000 : ℝ) (500573064583/1000000000000 : ℝ) (31285816537/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (259/2048 : ℝ)) (992142597721/1000000000000 : ℝ) (248035649431/250000000000 : ℝ) (500573064583/1000000000000 : ℝ) (31285816537/62500000000 : ℝ) (792525522987/1000000000000 : ℝ) (158505104601/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0371_exp_lower
  have heNumeric : (513726377917/250000000000 : ℝ)/4 ≤ Real.exp (-8525625522589/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726377917/250000000000 : ℝ)/4 ≤ Real.exp ((33151/262144 : ℝ)-(158505104601/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33151/262144 : ℝ) (259/2048 : ℝ) (158505104601/200000000000 : ℝ) (513726377917/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0372; no trusted numerical premise.
theorem cover8_leaf0372_exp_radius : (7984207026865437/8000000000000000 : ℝ) ≤ Real.exp ((-33153/2097152 : ℝ)/8) ∧ Real.exp ((-33153/2097152 : ℝ)/8) ≤ (499012939179089813/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33153/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0372_exp_lower : (115014208453255837/125000000000000000 : ℝ) ≤ Real.exp ((-166516129607/250000000000 : ℝ)/8) ∧ Real.exp ((-166516129607/250000000000 : ℝ)/8) ≤ (920113667626046697/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-166516129607/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0372_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726365343/250000000000 : ℝ) ≤ 4*Real.exp (259/2048 : ℝ)*Real.exp (-mu (radius 8 (33153/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513726365343/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33153/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0372_exp_radius
  have hrNumeric : (246078929367/250000000000 : ℝ) ≤ Real.exp (-33153/2097152 : ℝ) ∧ Real.exp (-33153/2097152 : ℝ) ≤ (984315717469/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246078929367/250000000000 : ℝ) ≤ (radius 8 (33153/262144 : ℝ)) ∧ (radius 8 (33153/262144 : ℝ)) ≤ (984315717469/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33153/262144 : ℝ)) (246078929367/250000000000 : ℝ) (984315717469/1000000000000 : ℝ) (44103973987/250000000000 : ℝ) (35283179191/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33153/262144 : ℝ)) (246078929367/250000000000 : ℝ) (984315717469/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33153/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246078929367/250000000000 : ℝ) (984315717469/1000000000000 : ℝ) (496078929367/500000000000 : ℝ) (198431571747/200000000000 : ℝ) (992126865611/1000000000000 : ℝ) (248031716403/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33153/262144 : ℝ)) 1 (496078929367/500000000000 : ℝ) (198431571747/200000000000 : ℝ) (992126865611/1000000000000 : ℝ) (248031716403/250000000000 : ℝ) (248035590543/250000000000 : ℝ) (496071181087/500000000000 : ℝ) (992142362051/1000000000000 : ℝ) (992142362053/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33153/262144 : ℝ)) 2 (248035590543/250000000000 : ℝ) (496071181087/500000000000 : ℝ) (992142362051/1000000000000 : ℝ) (992142362053/1000000000000 : ℝ) (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ) (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33153/262144 : ℝ)) 3 (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ) (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ) (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ) (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33153/262144 : ℝ)) 4 (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ) (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ) (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ) (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33153/262144 : ℝ)) 5 (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ) (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ) (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ) (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33153/262144 : ℝ)) 6 (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ) (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ) (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ) (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33153/262144 : ℝ)) 7 (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ) (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ) (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ) (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33153/262144 : ℝ))) (44103973987/250000000000 : ℝ) (35283179191/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33153/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44103973987/250000000000 : ℝ) (35283179191/200000000000 : ℝ) (294103973987/500000000000 : ℝ) (294103973989/500000000000 : ℝ) (420018923321/1000000000000 : ℝ) (42001892333/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33153/262144 : ℝ))) 1 (294103973987/500000000000 : ℝ) (294103973989/500000000000 : ℝ) (420018923321/1000000000000 : ℝ) (42001892333/100000000000 : ℝ) (504113435647/1000000000000 : ℝ) (252056717827/500000000000 : ℝ) (49704976511/100000000000 : ℝ) (497049765119/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33153/262144 : ℝ))) 2 (504113435647/1000000000000 : ℝ) (252056717827/500000000000 : ℝ) (49704976511/100000000000 : ℝ) (497049765119/1000000000000 : ℝ) (250290800189/500000000000 : ℝ) (500581600387/1000000000000 : ℝ) (100113828171/200000000000 : ℝ) (3910696413/7812500000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33153/262144 : ℝ))) 3 (250290800189/500000000000 : ℝ) (500581600387/1000000000000 : ℝ) (100113828171/200000000000 : ℝ) (3910696413/7812500000 : ℝ) (62571921327/125000000000 : ℝ) (250287685313/500000000000 : ℝ) (500575370577/1000000000000 : ℝ) (500575370587/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33153/262144 : ℝ))) 4 (62571921327/125000000000 : ℝ) (250287685313/500000000000 : ℝ) (500575370577/1000000000000 : ℝ) (500575370587/1000000000000 : ℝ) (125143842649/250000000000 : ℝ) (500575370607/1000000000000 : ℝ) (125143842649/250000000000 : ℝ) (500575370607/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33153/262144 : ℝ))) 5 (125143842649/250000000000 : ℝ) (500575370607/1000000000000 : ℝ) (125143842649/250000000000 : ℝ) (500575370607/1000000000000 : ℝ) (125143842649/250000000000 : ℝ) (500575370607/1000000000000 : ℝ) (125143842649/250000000000 : ℝ) (500575370607/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33153/262144 : ℝ))) 6 (125143842649/250000000000 : ℝ) (500575370607/1000000000000 : ℝ) (125143842649/250000000000 : ℝ) (500575370607/1000000000000 : ℝ) (125143842649/250000000000 : ℝ) (500575370607/1000000000000 : ℝ) (125143842649/250000000000 : ℝ) (500575370607/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33153/262144 : ℝ))) 7 (125143842649/250000000000 : ℝ) (500575370607/1000000000000 : ℝ) (125143842649/250000000000 : ℝ) (500575370607/1000000000000 : ℝ) (125143842649/250000000000 : ℝ) (500575370607/1000000000000 : ℝ) (125143842649/250000000000 : ℝ) (500575370607/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33153/262144 : ℝ)) hmem 8 (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ) (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33153/262144 : ℝ))) hcmem 8 (125143842649/250000000000 : ℝ) (500575370607/1000000000000 : ℝ) (125143842649/250000000000 : ℝ) (500575370607/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33153/262144 : ℝ)) (992142362111/1000000000000 : ℝ) (496071181057/500000000000 : ℝ) (125143842649/250000000000 : ℝ) (500575370607/1000000000000 : ℝ) (396264681079/500000000000 : ℝ) (396264681089/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0372_exp_lower
  have heNumeric : (513726365343/250000000000 : ℝ)/4 ≤ Real.exp (-166516129607/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726365343/250000000000 : ℝ)/4 ≤ Real.exp ((259/2048 : ℝ)-(396264681089/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (259/2048 : ℝ) (33153/262144 : ℝ) (396264681089/500000000000 : ℝ) (513726365343/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0373; no trusted numerical premise.
theorem cover8_leaf0373_exp_radius : (499012909435601721/500000000000000000 : ℝ) ≤ Real.exp ((-16577/1048576 : ℝ)/8) ∧ Real.exp ((-16577/1048576 : ℝ)/8) ≤ (998025818871203443/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16577/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0373_exp_lower : (184022732963946113/200000000000000000 : ℝ) ≤ Real.exp ((-1705125229639/2560000000000 : ℝ)/8) ∧ Real.exp ((-1705125229639/2560000000000 : ℝ)/8) ≤ (460056832409865283/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1705125229639/2560000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0373_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054905411233/1000000000000 : ℝ) ≤ 4*Real.exp (33153/262144 : ℝ)*Real.exp (-mu (radius 8 (16577/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054905411233/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16577/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0373_exp_radius
  have hrNumeric : (98431524811/100000000000 : ℝ) ≤ Real.exp (-16577/1048576 : ℝ) ∧ Real.exp (-16577/1048576 : ℝ) ≤ (984315248111/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98431524811/100000000000 : ℝ) ≤ (radius 8 (16577/131072 : ℝ)) ∧ (radius 8 (16577/131072 : ℝ)) ≤ (984315248111/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16577/131072 : ℝ)) (98431524811/100000000000 : ℝ) (984315248111/1000000000000 : ℝ) (1102615717/6250000000 : ℝ) (176418514727/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16577/131072 : ℝ)) (98431524811/100000000000 : ℝ) (984315248111/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16577/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98431524811/100000000000 : ℝ) (984315248111/1000000000000 : ℝ) (198431524811/200000000000 : ℝ) (124019703007/125000000000 : ℝ) (99212662907/100000000000 : ℝ) (992126629071/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16577/131072 : ℝ)) 1 (198431524811/200000000000 : ℝ) (124019703007/125000000000 : ℝ) (99212662907/100000000000 : ℝ) (992126629071/1000000000000 : ℝ) (496071063281/500000000000 : ℝ) (248035531641/250000000000 : ℝ) (992142126441/1000000000000 : ℝ) (992142126443/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16577/131072 : ℝ)) 2 (496071063281/500000000000 : ℝ) (248035531641/250000000000 : ℝ) (992142126441/1000000000000 : ℝ) (992142126443/1000000000000 : ℝ) (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ) (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16577/131072 : ℝ)) 3 (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ) (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ) (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ) (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16577/131072 : ℝ)) 4 (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ) (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ) (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ) (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16577/131072 : ℝ)) 5 (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ) (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ) (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ) (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16577/131072 : ℝ)) 6 (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ) (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ) (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ) (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16577/131072 : ℝ)) 7 (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ) (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ) (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ) (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16577/131072 : ℝ))) (1102615717/6250000000 : ℝ) (176418514727/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16577/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1102615717/6250000000 : ℝ) (176418514727/1000000000000 : ℝ) (7352615717/12500000000 : ℝ) (147052314341/250000000000 : ℝ) (84004408151/200000000000 : ℝ) (105005510191/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16577/131072 : ℝ))) 1 (7352615717/12500000000 : ℝ) (147052314341/250000000000 : ℝ) (84004408151/200000000000 : ℝ) (105005510191/250000000000 : ℝ) (504115649057/1000000000000 : ℝ) (63014456133/125000000000 : ℝ) (497052162923/1000000000000 : ℝ) (497052162931/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16577/131072 : ℝ))) 2 (504115649057/1000000000000 : ℝ) (63014456133/125000000000 : ℝ) (497052162923/1000000000000 : ℝ) (497052162931/1000000000000 : ℝ) (50058390599/100000000000 : ℝ) (250291952999/500000000000 : ℝ) (20022857887/40000000000 : ℝ) (500571447183/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16577/131072 : ℝ))) 3 (50058390599/100000000000 : ℝ) (250291952999/500000000000 : ℝ) (20022857887/40000000000 : ℝ) (500571447183/1000000000000 : ℝ) (250288838291/500000000000 : ℝ) (500577676591/1000000000000 : ℝ) (500577676543/1000000000000 : ℝ) (62572209569/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16577/131072 : ℝ))) 4 (250288838291/500000000000 : ℝ) (500577676591/1000000000000 : ℝ) (500577676543/1000000000000 : ℝ) (62572209569/125000000000 : ℝ) (250288838281/500000000000 : ℝ) (125144419143/250000000000 : ℝ) (250288838281/500000000000 : ℝ) (125144419143/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16577/131072 : ℝ))) 5 (250288838281/500000000000 : ℝ) (125144419143/250000000000 : ℝ) (250288838281/500000000000 : ℝ) (125144419143/250000000000 : ℝ) (250288838281/500000000000 : ℝ) (125144419143/250000000000 : ℝ) (250288838281/500000000000 : ℝ) (125144419143/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16577/131072 : ℝ))) 6 (250288838281/500000000000 : ℝ) (125144419143/250000000000 : ℝ) (250288838281/500000000000 : ℝ) (125144419143/250000000000 : ℝ) (250288838281/500000000000 : ℝ) (125144419143/250000000000 : ℝ) (250288838281/500000000000 : ℝ) (125144419143/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16577/131072 : ℝ))) 7 (250288838281/500000000000 : ℝ) (125144419143/250000000000 : ℝ) (250288838281/500000000000 : ℝ) (125144419143/250000000000 : ℝ) (250288838281/500000000000 : ℝ) (125144419143/250000000000 : ℝ) (250288838281/500000000000 : ℝ) (125144419143/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16577/131072 : ℝ)) hmem 8 (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ) (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16577/131072 : ℝ))) hcmem 8 (250288838281/500000000000 : ℝ) (125144419143/250000000000 : ℝ) (250288838281/500000000000 : ℝ) (125144419143/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16577/131072 : ℝ)) (992142126501/1000000000000 : ℝ) (124017765813/125000000000 : ℝ) (250288838281/500000000000 : ℝ) (125144419143/250000000000 : ℝ) (158506640251/200000000000 : ℝ) (31701328051/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0373_exp_lower
  have heNumeric : (2054905411233/1000000000000 : ℝ)/4 ≤ Real.exp (-1705125229639/2560000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054905411233/1000000000000 : ℝ)/4 ≤ Real.exp ((33153/262144 : ℝ)-(31701328051/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33153/262144 : ℝ) (16577/131072 : ℝ) (31701328051/40000000000 : ℝ) (2054905411233/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0374; no trusted numerical premise.
theorem cover8_leaf0374_exp_radius : (249506439846057701/250000000000000000 : ℝ) ≤ Real.exp ((-33155/2097152 : ℝ)/8) ∧ Real.exp ((-33155/2097152 : ℝ)/8) ≤ (199605151876846161/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33155/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0374_exp_lower : (18402273240447711/20000000000000000 : ℝ) ≤ Real.exp ((-21314066148783/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314066148783/32000000000000 : ℝ)/8) ≤ (920113662022385551/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314066148783/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0374_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452680627/500000000000 : ℝ) ≤ 4*Real.exp (16577/131072 : ℝ)*Real.exp (-mu (radius 8 (33155/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452680627/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33155/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0374_exp_radius
  have hrNumeric : (7689959209/7812500000 : ℝ) ≤ Real.exp (-33155/2097152 : ℝ) ∧ Real.exp (-33155/2097152 : ℝ) ≤ (984314778753/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (7689959209/7812500000 : ℝ) ≤ (radius 8 (33155/262144 : ℝ)) ∧ (radius 8 (33155/262144 : ℝ)) ≤ (984314778753/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33155/262144 : ℝ)) (7689959209/7812500000 : ℝ) (984314778753/1000000000000 : ℝ) (176421133451/1000000000000 : ℝ) (88210566729/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33155/262144 : ℝ)) (7689959209/7812500000 : ℝ) (984314778753/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33155/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (7689959209/7812500000 : ℝ) (984314778753/1000000000000 : ℝ) (15502459209/15625000000 : ℝ) (992157389377/1000000000000 : ℝ) (62007899533/62500000000 : ℝ) (99212639253/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33155/262144 : ℝ)) 1 (15502459209/15625000000 : ℝ) (992157389377/1000000000000 : ℝ) (62007899533/62500000000 : ℝ) (99212639253/100000000000 : ℝ) (124017736369/125000000000 : ℝ) (496070945477/500000000000 : ℝ) (99214189083/100000000000 : ℝ) (992141890833/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33155/262144 : ℝ)) 2 (124017736369/125000000000 : ℝ) (496070945477/500000000000 : ℝ) (99214189083/100000000000 : ℝ) (992141890833/1000000000000 : ℝ) (992141890891/1000000000000 : ℝ) (496070945447/500000000000 : ℝ) (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33155/262144 : ℝ)) 3 (992141890891/1000000000000 : ℝ) (496070945447/500000000000 : ℝ) (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ) (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ) (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33155/262144 : ℝ)) 4 (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ) (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ) (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ) (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33155/262144 : ℝ)) 5 (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ) (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ) (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ) (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33155/262144 : ℝ)) 6 (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ) (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ) (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ) (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33155/262144 : ℝ)) 7 (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ) (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ) (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ) (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33155/262144 : ℝ))) (176421133451/1000000000000 : ℝ) (88210566729/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33155/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176421133451/1000000000000 : ℝ) (88210566729/500000000000 : ℝ) (23528422669/40000000000 : ℝ) (588210566729/1000000000000 : ℝ) (105006289529/250000000000 : ℝ) (210012579063/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33155/262144 : ℝ))) 1 (23528422669/40000000000 : ℝ) (588210566729/1000000000000 : ℝ) (105006289529/250000000000 : ℝ) (210012579063/500000000000 : ℝ) (25205893121/50000000000 : ℝ) (126029465607/250000000000 : ℝ) (497054560681/1000000000000 : ℝ) (497054560689/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33155/262144 : ℝ))) 2 (25205893121/50000000000 : ℝ) (126029465607/250000000000 : ℝ) (497054560681/1000000000000 : ℝ) (497054560689/1000000000000 : ℝ) (10011724231/20000000000 : ℝ) (500586211559/1000000000000 : ℝ) (500573753443/1000000000000 : ℝ) (125143438363/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33155/262144 : ℝ))) 3 (10011724231/20000000000 : ℝ) (500586211559/1000000000000 : ℝ) (500573753443/1000000000000 : ℝ) (125143438363/250000000000 : ℝ) (15643124453/31250000000 : ℝ) (250289991253/500000000000 : ℝ) (500579982457/1000000000000 : ℝ) (500579982467/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33155/262144 : ℝ))) 4 (15643124453/31250000000 : ℝ) (250289991253/500000000000 : ℝ) (500579982457/1000000000000 : ℝ) (500579982467/1000000000000 : ℝ) (125144995619/250000000000 : ℝ) (500579982487/1000000000000 : ℝ) (125144995619/250000000000 : ℝ) (500579982487/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33155/262144 : ℝ))) 5 (125144995619/250000000000 : ℝ) (500579982487/1000000000000 : ℝ) (125144995619/250000000000 : ℝ) (500579982487/1000000000000 : ℝ) (125144995619/250000000000 : ℝ) (500579982487/1000000000000 : ℝ) (125144995619/250000000000 : ℝ) (500579982487/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33155/262144 : ℝ))) 6 (125144995619/250000000000 : ℝ) (500579982487/1000000000000 : ℝ) (125144995619/250000000000 : ℝ) (500579982487/1000000000000 : ℝ) (125144995619/250000000000 : ℝ) (500579982487/1000000000000 : ℝ) (125144995619/250000000000 : ℝ) (500579982487/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33155/262144 : ℝ))) 7 (125144995619/250000000000 : ℝ) (500579982487/1000000000000 : ℝ) (125144995619/250000000000 : ℝ) (500579982487/1000000000000 : ℝ) (125144995619/250000000000 : ℝ) (500579982487/1000000000000 : ℝ) (125144995619/250000000000 : ℝ) (500579982487/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33155/262144 : ℝ)) hmem 8 (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ) (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33155/262144 : ℝ))) hcmem 8 (125144995619/250000000000 : ℝ) (500579982487/1000000000000 : ℝ) (125144995619/250000000000 : ℝ) (500579982487/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33155/262144 : ℝ)) (99214189089/100000000000 : ℝ) (496070945447/500000000000 : ℝ) (125144995619/250000000000 : ℝ) (500579982487/1000000000000 : ℝ) (792537040273/1000000000000 : ℝ) (396268520147/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0374_exp_lower
  have heNumeric : (1027452680627/500000000000 : ℝ)/4 ≤ Real.exp (-21314066148783/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452680627/500000000000 : ℝ)/4 ≤ Real.exp ((16577/131072 : ℝ)-(396268520147/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16577/131072 : ℝ) (33155/262144 : ℝ) (396268520147/500000000000 : ℝ) (1027452680627/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0350_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0350_certificate
#check SmaleRate.Proofs.cover8_leaf0351_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0351_certificate
#check SmaleRate.Proofs.cover8_leaf0352_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0352_certificate
#check SmaleRate.Proofs.cover8_leaf0353_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0353_certificate
#check SmaleRate.Proofs.cover8_leaf0354_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0354_certificate
#check SmaleRate.Proofs.cover8_leaf0355_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0355_certificate
#check SmaleRate.Proofs.cover8_leaf0356_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0356_certificate
#check SmaleRate.Proofs.cover8_leaf0357_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0357_certificate
#check SmaleRate.Proofs.cover8_leaf0358_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0358_certificate
#check SmaleRate.Proofs.cover8_leaf0359_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0359_certificate
#check SmaleRate.Proofs.cover8_leaf0360_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0360_certificate
#check SmaleRate.Proofs.cover8_leaf0361_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0361_certificate
#check SmaleRate.Proofs.cover8_leaf0362_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0362_certificate
#check SmaleRate.Proofs.cover8_leaf0363_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0363_certificate
#check SmaleRate.Proofs.cover8_leaf0364_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0364_certificate
#check SmaleRate.Proofs.cover8_leaf0365_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0365_certificate
#check SmaleRate.Proofs.cover8_leaf0366_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0366_certificate
#check SmaleRate.Proofs.cover8_leaf0367_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0367_certificate
#check SmaleRate.Proofs.cover8_leaf0368_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0368_certificate
#check SmaleRate.Proofs.cover8_leaf0369_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0369_certificate
#check SmaleRate.Proofs.cover8_leaf0370_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0370_certificate
#check SmaleRate.Proofs.cover8_leaf0371_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0371_certificate
#check SmaleRate.Proofs.cover8_leaf0372_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0372_certificate
#check SmaleRate.Proofs.cover8_leaf0373_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0373_certificate
#check SmaleRate.Proofs.cover8_leaf0374_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0374_certificate
