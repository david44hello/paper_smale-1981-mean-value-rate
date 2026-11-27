/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0375; no trusted numerical premise.
theorem cover8_leaf0375_exp_radius : (62376606243578857/62500000000000000 : ℝ) ≤ Real.exp ((-8289/524288 : ℝ)/8) ∧ Real.exp ((-8289/524288 : ℝ)/8) ≤ (998025699897261713/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8289/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0375_exp_lower : (460056829616948319/500000000000000000 : ℝ) ≤ Real.exp ((-42628133849229/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628133849229/64000000000000 : ℝ)/8) ≤ (920113659233896639/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628133849229/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0375_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452655717/500000000000 : ℝ) ≤ 4*Real.exp (33155/262144 : ℝ)*Real.exp (-mu (radius 8 (8289/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452655717/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8289/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0375_exp_radius
  have hrNumeric : (492157154697/500000000000 : ℝ) ≤ Real.exp (-8289/524288 : ℝ) ∧ Real.exp (-8289/524288 : ℝ) ≤ (196862861879/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492157154697/500000000000 : ℝ) ≤ (radius 8 (8289/65536 : ℝ)) ∧ (radius 8 (8289/65536 : ℝ)) ≤ (196862861879/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8289/65536 : ℝ)) (492157154697/500000000000 : ℝ) (196862861879/200000000000 : ℝ) (176423752143/1000000000000 : ℝ) (176423752149/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8289/65536 : ℝ)) (492157154697/500000000000 : ℝ) (196862861879/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8289/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492157154697/500000000000 : ℝ) (196862861879/200000000000 : ℝ) (992157154697/1000000000000 : ℝ) (496078577349/500000000000 : ℝ) (992126155987/1000000000000 : ℝ) (248031538997/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8289/65536 : ℝ)) 1 (992157154697/1000000000000 : ℝ) (496078577349/500000000000 : ℝ) (992126155987/1000000000000 : ℝ) (248031538997/250000000000 : ℝ) (496070827671/500000000000 : ℝ) (992141655343/1000000000000 : ℝ) (49607082761/50000000000 : ℝ) (496070827611/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8289/65536 : ℝ)) 2 (496070827671/500000000000 : ℝ) (992141655343/1000000000000 : ℝ) (49607082761/50000000000 : ℝ) (496070827611/500000000000 : ℝ) (992141655281/1000000000000 : ℝ) (992141655283/1000000000000 : ℝ) (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8289/65536 : ℝ)) 3 (992141655281/1000000000000 : ℝ) (992141655283/1000000000000 : ℝ) (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ) (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ) (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8289/65536 : ℝ)) 4 (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ) (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ) (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ) (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8289/65536 : ℝ)) 5 (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ) (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ) (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ) (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8289/65536 : ℝ)) 6 (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ) (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ) (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ) (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8289/65536 : ℝ)) 7 (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ) (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ) (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ) (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8289/65536 : ℝ))) (176423752143/1000000000000 : ℝ) (176423752149/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8289/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176423752143/1000000000000 : ℝ) (176423752149/1000000000000 : ℝ) (588211876071/1000000000000 : ℝ) (23528475043/40000000000 : ℝ) (26251767213/62500000000 : ℝ) (420028275417/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8289/65536 : ℝ))) 1 (588211876071/1000000000000 : ℝ) (23528475043/40000000000 : ℝ) (26251767213/62500000000 : ℝ) (420028275417/1000000000000 : ℝ) (504120075739/1000000000000 : ℝ) (252060037873/500000000000 : ℝ) (248528479193/500000000000 : ℝ) (248528479197/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8289/65536 : ℝ))) 2 (504120075739/1000000000000 : ℝ) (252060037873/500000000000 : ℝ) (248528479193/500000000000 : ℝ) (248528479197/500000000000 : ℝ) (250294258531/500000000000 : ℝ) (50058851707/100000000000 : ℝ) (500576059663/1000000000000 : ℝ) (500576059671/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8289/65536 : ℝ))) 3 (250294258531/500000000000 : ℝ) (50058851707/100000000000 : ℝ) (500576059663/1000000000000 : ℝ) (500576059671/1000000000000 : ℝ) (250291144181/500000000000 : ℝ) (500582288371/1000000000000 : ℝ) (500582288323/1000000000000 : ℝ) (125145572083/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8289/65536 : ℝ))) 4 (250291144181/500000000000 : ℝ) (500582288371/1000000000000 : ℝ) (500582288323/1000000000000 : ℝ) (125145572083/250000000000 : ℝ) (250291144171/500000000000 : ℝ) (15643196511/31250000000 : ℝ) (250291144171/500000000000 : ℝ) (15643196511/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8289/65536 : ℝ))) 5 (250291144171/500000000000 : ℝ) (15643196511/31250000000 : ℝ) (250291144171/500000000000 : ℝ) (15643196511/31250000000 : ℝ) (250291144171/500000000000 : ℝ) (15643196511/31250000000 : ℝ) (250291144171/500000000000 : ℝ) (15643196511/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8289/65536 : ℝ))) 6 (250291144171/500000000000 : ℝ) (15643196511/31250000000 : ℝ) (250291144171/500000000000 : ℝ) (15643196511/31250000000 : ℝ) (250291144171/500000000000 : ℝ) (15643196511/31250000000 : ℝ) (250291144171/500000000000 : ℝ) (15643196511/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8289/65536 : ℝ))) 7 (250291144171/500000000000 : ℝ) (15643196511/31250000000 : ℝ) (250291144171/500000000000 : ℝ) (15643196511/31250000000 : ℝ) (250291144171/500000000000 : ℝ) (15643196511/31250000000 : ℝ) (250291144171/500000000000 : ℝ) (15643196511/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8289/65536 : ℝ)) hmem 8 (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ) (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8289/65536 : ℝ))) hcmem 8 (250291144171/500000000000 : ℝ) (15643196511/31250000000 : ℝ) (250291144171/500000000000 : ℝ) (15643196511/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8289/65536 : ℝ)) (12401770691/12500000000 : ℝ) (992141655283/1000000000000 : ℝ) (250291144171/500000000000 : ℝ) (15643196511/31250000000 : ℝ) (792540879217/1000000000000 : ℝ) (198135219809/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0375_exp_lower
  have heNumeric : (1027452655717/500000000000 : ℝ)/4 ≤ Real.exp (-42628133849229/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452655717/500000000000 : ℝ)/4 ≤ Real.exp ((33155/262144 : ℝ)-(198135219809/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33155/262144 : ℝ) (8289/65536 : ℝ) (198135219809/250000000000 : ℝ) (1027452655717/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0376; no trusted numerical premise.
theorem cover8_leaf0376_exp_radius : (499012820205148083/500000000000000000 : ℝ) ≤ Real.exp ((-33157/2097152 : ℝ)/8) ∧ Real.exp ((-33157/2097152 : ℝ)/8) ≤ (998025640410296167/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33157/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0376_exp_lower : (460056828227074407/500000000000000000 : ℝ) ≤ Real.exp ((-10657033849007/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657033849007/16000000000000 : ℝ)/8) ≤ (184022731290829763/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657033849007/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0376_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054905261769/1000000000000 : ℝ) ≤ 4*Real.exp (8289/65536 : ℝ)*Real.exp (-mu (radius 8 (33157/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054905261769/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33157/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0376_exp_radius
  have hrNumeric : (246078460009/250000000000 : ℝ) ≤ Real.exp (-33157/2097152 : ℝ) ∧ Real.exp (-33157/2097152 : ℝ) ≤ (984313840037/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246078460009/250000000000 : ℝ) ≤ (radius 8 (33157/262144 : ℝ)) ∧ (radius 8 (33157/262144 : ℝ)) ≤ (984313840037/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33157/262144 : ℝ)) (246078460009/250000000000 : ℝ) (984313840037/1000000000000 : ℝ) (88213185397/500000000000 : ℝ) (441065927/2500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33157/262144 : ℝ)) (246078460009/250000000000 : ℝ) (984313840037/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33157/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246078460009/250000000000 : ℝ) (984313840037/1000000000000 : ℝ) (496078460009/500000000000 : ℝ) (992156920019/1000000000000 : ℝ) (198425183889/200000000000 : ℝ) (992125919447/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33157/262144 : ℝ)) 1 (496078460009/500000000000 : ℝ) (992156920019/1000000000000 : ℝ) (198425183889/200000000000 : ℝ) (992125919447/1000000000000 : ℝ) (992141419731/1000000000000 : ℝ) (992141419733/1000000000000 : ℝ) (99214141961/100000000000 : ℝ) (248035354903/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33157/262144 : ℝ)) 2 (992141419731/1000000000000 : ℝ) (992141419733/1000000000000 : ℝ) (99214141961/100000000000 : ℝ) (248035354903/250000000000 : ℝ) (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ) (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33157/262144 : ℝ)) 3 (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ) (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ) (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ) (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33157/262144 : ℝ)) 4 (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ) (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ) (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ) (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33157/262144 : ℝ)) 5 (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ) (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ) (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ) (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33157/262144 : ℝ)) 6 (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ) (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ) (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ) (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33157/262144 : ℝ)) 7 (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ) (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ) (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ) (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33157/262144 : ℝ))) (88213185397/500000000000 : ℝ) (441065927/2500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33157/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88213185397/500000000000 : ℝ) (441065927/2500000000 : ℝ) (588213185397/1000000000000 : ℝ) (2941065927/5000000000 : ℝ) (420031392629/1000000000000 : ℝ) (420031392637/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33157/262144 : ℝ))) 1 (588213185397/1000000000000 : ℝ) (2941065927/5000000000 : ℝ) (420031392629/1000000000000 : ℝ) (420031392637/1000000000000 : ℝ) (504122289013/1000000000000 : ℝ) (504122289019/1000000000000 : ℝ) (248529678019/500000000000 : ℝ) (99411871209/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33157/262144 : ℝ))) 2 (504122289013/1000000000000 : ℝ) (504122289019/1000000000000 : ℝ) (248529678019/500000000000 : ℝ) (99411871209/200000000000 : ℝ) (20023632901/40000000000 : ℝ) (125147705633/250000000000 : ℝ) (250289182917/500000000000 : ℝ) (500578365841/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33157/262144 : ℝ))) 3 (20023632901/40000000000 : ℝ) (125147705633/250000000000 : ℝ) (250289182917/500000000000 : ℝ) (500578365841/1000000000000 : ℝ) (500584594179/1000000000000 : ℝ) (500584594187/1000000000000 : ℝ) (25029229707/50000000000 : ℝ) (125146148537/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33157/262144 : ℝ))) 4 (500584594179/1000000000000 : ℝ) (500584594187/1000000000000 : ℝ) (25029229707/50000000000 : ℝ) (125146148537/250000000000 : ℝ) (500584594159/1000000000000 : ℝ) (62573074271/125000000000 : ℝ) (500584594159/1000000000000 : ℝ) (62573074271/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33157/262144 : ℝ))) 5 (500584594159/1000000000000 : ℝ) (62573074271/125000000000 : ℝ) (500584594159/1000000000000 : ℝ) (62573074271/125000000000 : ℝ) (500584594159/1000000000000 : ℝ) (62573074271/125000000000 : ℝ) (500584594159/1000000000000 : ℝ) (62573074271/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33157/262144 : ℝ))) 6 (500584594159/1000000000000 : ℝ) (62573074271/125000000000 : ℝ) (500584594159/1000000000000 : ℝ) (62573074271/125000000000 : ℝ) (500584594159/1000000000000 : ℝ) (62573074271/125000000000 : ℝ) (500584594159/1000000000000 : ℝ) (62573074271/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33157/262144 : ℝ))) 7 (500584594159/1000000000000 : ℝ) (62573074271/125000000000 : ℝ) (500584594159/1000000000000 : ℝ) (62573074271/125000000000 : ℝ) (500584594159/1000000000000 : ℝ) (62573074271/125000000000 : ℝ) (500584594159/1000000000000 : ℝ) (62573074271/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33157/262144 : ℝ)) hmem 8 (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ) (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33157/262144 : ℝ))) hcmem 8 (500584594159/1000000000000 : ℝ) (62573074271/125000000000 : ℝ) (500584594159/1000000000000 : ℝ) (62573074271/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33157/262144 : ℝ)) (99214141967/100000000000 : ℝ) (992141419673/1000000000000 : ℝ) (500584594159/1000000000000 : ℝ) (62573074271/125000000000 : ℝ) (198136179521/250000000000 : ℝ) (396272359051/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0376_exp_lower
  have heNumeric : (2054905261769/1000000000000 : ℝ)/4 ≤ Real.exp (-10657033849007/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054905261769/1000000000000 : ℝ)/4 ≤ Real.exp ((8289/65536 : ℝ)-(396272359051/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8289/65536 : ℝ) (33157/262144 : ℝ) (396272359051/500000000000 : ℝ) (2054905261769/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0377; no trusted numerical premise.
theorem cover8_leaf0377_exp_radius : (199605116184666833/200000000000000000 : ℝ) ≤ Real.exp ((-16579/1048576 : ℝ)/8) ∧ Real.exp ((-16579/1048576 : ℝ)/8) ≤ (499012790461667083/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16579/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0377_exp_lower : (460056826842088603/500000000000000000 : ℝ) ≤ Real.exp ((-42628136937387/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628136937387/64000000000000 : ℝ)/8) ≤ (920113653684177207/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628136937387/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0377_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (51372630307/25000000000 : ℝ) ≤ 4*Real.exp (33157/262144 : ℝ)*Real.exp (-mu (radius 8 (16579/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (51372630307/25000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16579/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0377_exp_radius
  have hrNumeric : (984313370679/1000000000000 : ℝ) ≤ Real.exp (-16579/1048576 : ℝ) ∧ Real.exp (-16579/1048576 : ℝ) ≤ (24607834267/25000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984313370679/1000000000000 : ℝ) ≤ (radius 8 (16579/131072 : ℝ)) ∧ (radius 8 (16579/131072 : ℝ)) ≤ (24607834267/25000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16579/131072 : ℝ)) (984313370679/1000000000000 : ℝ) (24607834267/25000000000 : ℝ) (176428989399/1000000000000 : ℝ) (88214494703/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16579/131072 : ℝ)) (984313370679/1000000000000 : ℝ) (24607834267/25000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16579/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984313370679/1000000000000 : ℝ) (24607834267/25000000000 : ℝ) (992156685339/1000000000000 : ℝ) (49607834267/50000000000 : ℝ) (124015710363/125000000000 : ℝ) (496062841453/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16579/131072 : ℝ)) 1 (992156685339/1000000000000 : ℝ) (49607834267/50000000000 : ℝ) (124015710363/125000000000 : ℝ) (496062841453/500000000000 : ℝ) (992141184121/1000000000000 : ℝ) (992141184123/1000000000000 : ℝ) (7751103/7812500 : ℝ) (496070592001/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16579/131072 : ℝ)) 2 (992141184121/1000000000000 : ℝ) (992141184123/1000000000000 : ℝ) (7751103/7812500 : ℝ) (496070592001/500000000000 : ℝ) (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ) (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16579/131072 : ℝ)) 3 (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ) (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ) (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ) (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16579/131072 : ℝ)) 4 (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ) (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ) (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ) (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16579/131072 : ℝ)) 5 (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ) (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ) (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ) (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16579/131072 : ℝ)) 6 (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ) (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ) (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ) (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16579/131072 : ℝ)) 7 (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ) (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ) (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ) (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16579/131072 : ℝ))) (176428989399/1000000000000 : ℝ) (88214494703/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16579/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176428989399/1000000000000 : ℝ) (88214494703/500000000000 : ℝ) (588214494699/1000000000000 : ℝ) (588214494703/1000000000000 : ℝ) (420034509771/1000000000000 : ℝ) (21001725489/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16579/131072 : ℝ))) 1 (588214494699/1000000000000 : ℝ) (588214494703/1000000000000 : ℝ) (420034509771/1000000000000 : ℝ) (21001725489/50000000000 : ℝ) (100824900447/200000000000 : ℝ) (252062251121/500000000000 : ℝ) (497061753629/1000000000000 : ℝ) (497061753637/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16579/131072 : ℝ))) 2 (100824900447/200000000000 : ℝ) (252062251121/500000000000 : ℝ) (497061753629/1000000000000 : ℝ) (497061753637/1000000000000 : ℝ) (125148281983/250000000000 : ℝ) (25029656397/50000000000 : ℝ) (125145167987/250000000000 : ℝ) (125145167989/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16579/131072 : ℝ))) 3 (125148281983/250000000000 : ℝ) (25029656397/50000000000 : ℝ) (125145167987/250000000000 : ℝ) (125145167989/250000000000 : ℝ) (25029344997/50000000000 : ℝ) (125146724987/250000000000 : ℝ) (500586899901/1000000000000 : ℝ) (50058689991/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16579/131072 : ℝ))) 4 (25029344997/50000000000 : ℝ) (125146724987/250000000000 : ℝ) (500586899901/1000000000000 : ℝ) (50058689991/100000000000 : ℝ) (6257336249/12500000000 : ℝ) (500586899929/1000000000000 : ℝ) (6257336249/12500000000 : ℝ) (500586899929/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16579/131072 : ℝ))) 5 (6257336249/12500000000 : ℝ) (500586899929/1000000000000 : ℝ) (6257336249/12500000000 : ℝ) (500586899929/1000000000000 : ℝ) (6257336249/12500000000 : ℝ) (500586899929/1000000000000 : ℝ) (6257336249/12500000000 : ℝ) (500586899929/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16579/131072 : ℝ))) 6 (6257336249/12500000000 : ℝ) (500586899929/1000000000000 : ℝ) (6257336249/12500000000 : ℝ) (500586899929/1000000000000 : ℝ) (6257336249/12500000000 : ℝ) (500586899929/1000000000000 : ℝ) (6257336249/12500000000 : ℝ) (500586899929/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16579/131072 : ℝ))) 7 (6257336249/12500000000 : ℝ) (500586899929/1000000000000 : ℝ) (6257336249/12500000000 : ℝ) (500586899929/1000000000000 : ℝ) (6257336249/12500000000 : ℝ) (500586899929/1000000000000 : ℝ) (6257336249/12500000000 : ℝ) (500586899929/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16579/131072 : ℝ)) hmem 8 (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ) (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16579/131072 : ℝ))) hcmem 8 (6257336249/12500000000 : ℝ) (500586899929/1000000000000 : ℝ) (6257336249/12500000000 : ℝ) (500586899929/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16579/131072 : ℝ)) (49607059203/50000000000 : ℝ) (992141184063/1000000000000 : ℝ) (6257336249/12500000000 : ℝ) (500586899929/1000000000000 : ℝ) (158509711373/200000000000 : ℝ) (792548556883/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0377_exp_lower
  have heNumeric : (51372630307/25000000000 : ℝ)/4 ≤ Real.exp (-42628136937387/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (51372630307/25000000000 : ℝ)/4 ≤ Real.exp ((33157/262144 : ℝ)-(792548556883/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33157/262144 : ℝ) (16579/131072 : ℝ) (792548556883/1000000000000 : ℝ) (51372630307/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0378; no trusted numerical premise.
theorem cover8_leaf0378_exp_radius : (99802552143637571/100000000000000000 : ℝ) ≤ Real.exp ((-33159/2097152 : ℝ)/8) ∧ Real.exp ((-33159/2097152 : ℝ)/8) ≤ (998025521436375711/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33159/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0378_exp_lower : (460056825461473343/500000000000000000 : ℝ) ≤ Real.exp ((-21314069236941/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314069236941/32000000000000 : ℝ)/8) ≤ (920113650922946687/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314069236941/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0378_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452581473/500000000000 : ℝ) ≤ 4*Real.exp (16579/131072 : ℝ)*Real.exp (-mu (radius 8 (33159/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452581473/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33159/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0378_exp_radius
  have hrNumeric : (492156450661/500000000000 : ℝ) ≤ Real.exp (-33159/2097152 : ℝ) ∧ Real.exp (-33159/2097152 : ℝ) ≤ (984312901323/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492156450661/500000000000 : ℝ) ≤ (radius 8 (33159/262144 : ℝ)) ∧ (radius 8 (33159/262144 : ℝ)) ≤ (984312901323/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33159/262144 : ℝ)) (492156450661/500000000000 : ℝ) (984312901323/1000000000000 : ℝ) (44107901991/250000000000 : ℝ) (176431607971/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33159/262144 : ℝ)) (492156450661/500000000000 : ℝ) (984312901323/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33159/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492156450661/500000000000 : ℝ) (984312901323/1000000000000 : ℝ) (992156450661/1000000000000 : ℝ) (496078225331/500000000000 : ℝ) (992125446363/1000000000000 : ℝ) (198425089273/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33159/262144 : ℝ)) 1 (992156450661/1000000000000 : ℝ) (496078225331/500000000000 : ℝ) (992125446363/1000000000000 : ℝ) (198425089273/200000000000 : ℝ) (31004404641/31250000000 : ℝ) (496070474257/500000000000 : ℝ) (99214094839/100000000000 : ℝ) (992140948393/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33159/262144 : ℝ)) 2 (31004404641/31250000000 : ℝ) (496070474257/500000000000 : ℝ) (99214094839/100000000000 : ℝ) (992140948393/1000000000000 : ℝ) (992140948451/1000000000000 : ℝ) (496070474227/500000000000 : ℝ) (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33159/262144 : ℝ)) 3 (992140948451/1000000000000 : ℝ) (496070474227/500000000000 : ℝ) (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ) (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ) (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33159/262144 : ℝ)) 4 (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ) (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ) (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ) (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33159/262144 : ℝ)) 5 (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ) (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ) (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ) (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33159/262144 : ℝ)) 6 (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ) (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ) (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ) (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33159/262144 : ℝ)) 7 (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ) (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ) (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ) (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33159/262144 : ℝ))) (44107901991/250000000000 : ℝ) (176431607971/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33159/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44107901991/250000000000 : ℝ) (176431607971/1000000000000 : ℝ) (294107901991/500000000000 : ℝ) (294107901993/500000000000 : ℝ) (420037626843/1000000000000 : ℝ) (105009406713/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33159/262144 : ℝ))) 1 (294107901991/500000000000 : ℝ) (294107901993/500000000000 : ℝ) (420037626843/1000000000000 : ℝ) (105009406713/250000000000 : ℝ) (126031678853/250000000000 : ℝ) (504126715419/1000000000000 : ℝ) (497064151167/1000000000000 : ℝ) (19882566047/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33159/262144 : ℝ))) 2 (126031678853/250000000000 : ℝ) (504126715419/1000000000000 : ℝ) (497064151167/1000000000000 : ℝ) (19882566047/40000000000 : ℝ) (500595433289/1000000000000 : ℝ) (500595433297/1000000000000 : ℝ) (500582978013/1000000000000 : ℝ) (250291489011/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33159/262144 : ℝ))) 3 (500595433289/1000000000000 : ℝ) (500595433297/1000000000000 : ℝ) (500582978013/1000000000000 : ℝ) (250291489011/500000000000 : ℝ) (500589205651/1000000000000 : ℝ) (25029460283/50000000000 : ℝ) (125147301403/250000000000 : ℝ) (500589205621/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33159/262144 : ℝ))) 4 (500589205651/1000000000000 : ℝ) (25029460283/50000000000 : ℝ) (125147301403/250000000000 : ℝ) (500589205621/1000000000000 : ℝ) (500589205631/1000000000000 : ℝ) (500589205641/1000000000000 : ℝ) (500589205631/1000000000000 : ℝ) (500589205641/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33159/262144 : ℝ))) 5 (500589205631/1000000000000 : ℝ) (500589205641/1000000000000 : ℝ) (500589205631/1000000000000 : ℝ) (500589205641/1000000000000 : ℝ) (500589205631/1000000000000 : ℝ) (500589205641/1000000000000 : ℝ) (500589205631/1000000000000 : ℝ) (500589205641/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33159/262144 : ℝ))) 6 (500589205631/1000000000000 : ℝ) (500589205641/1000000000000 : ℝ) (500589205631/1000000000000 : ℝ) (500589205641/1000000000000 : ℝ) (500589205631/1000000000000 : ℝ) (500589205641/1000000000000 : ℝ) (500589205631/1000000000000 : ℝ) (500589205641/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33159/262144 : ℝ))) 7 (500589205631/1000000000000 : ℝ) (500589205641/1000000000000 : ℝ) (500589205631/1000000000000 : ℝ) (500589205641/1000000000000 : ℝ) (500589205631/1000000000000 : ℝ) (500589205641/1000000000000 : ℝ) (500589205631/1000000000000 : ℝ) (500589205641/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33159/262144 : ℝ)) hmem 8 (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ) (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33159/262144 : ℝ))) hcmem 8 (500589205631/1000000000000 : ℝ) (500589205641/1000000000000 : ℝ) (500589205631/1000000000000 : ℝ) (500589205641/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33159/262144 : ℝ)) (19842818969/20000000000 : ℝ) (496070474227/500000000000 : ℝ) (500589205631/1000000000000 : ℝ) (500589205641/1000000000000 : ℝ) (49534524723/62500000000 : ℝ) (198138098897/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0378_exp_lower
  have heNumeric : (1027452581473/500000000000 : ℝ)/4 ≤ Real.exp (-21314069236941/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452581473/500000000000 : ℝ)/4 ≤ Real.exp ((16579/131072 : ℝ)-(198138098897/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16579/131072 : ℝ) (33159/262144 : ℝ) (198138098897/250000000000 : ℝ) (1027452581473/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0379; no trusted numerical premise.
theorem cover8_leaf0379_exp_radius : (998025461949420801/1000000000000000000 : ℝ) ≤ Real.exp ((-4145/262144 : ℝ)/8) ∧ Real.exp ((-4145/262144 : ℝ)/8) ≤ (499012730974710401/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4145/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0379_exp_lower : (920113648170802297/1000000000000000000 : ℝ) ≤ Real.exp ((-42628140005321/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628140005321/64000000000000 : ℝ)/8) ≤ (460056824085401149/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628140005321/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0379_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (82196204551/40000000000 : ℝ) ≤ 4*Real.exp (33159/262144 : ℝ)*Real.exp (-mu (radius 8 (4145/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (82196204551/40000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4145/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0379_exp_radius
  have hrNumeric : (196862486393/200000000000 : ℝ) ≤ Real.exp (-4145/262144 : ℝ) ∧ Real.exp (-4145/262144 : ℝ) ≤ (492156215983/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196862486393/200000000000 : ℝ) ≤ (radius 8 (4145/32768 : ℝ)) ∧ (radius 8 (4145/32768 : ℝ)) ≤ (492156215983/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4145/32768 : ℝ)) (196862486393/200000000000 : ℝ) (492156215983/500000000000 : ℝ) (17643422649/100000000000 : ℝ) (2756784789/15625000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4145/32768 : ℝ)) (196862486393/200000000000 : ℝ) (492156215983/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4145/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196862486393/200000000000 : ℝ) (492156215983/500000000000 : ℝ) (496078107991/500000000000 : ℝ) (992156215983/1000000000000 : ℝ) (496062604911/500000000000 : ℝ) (992125209823/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4145/32768 : ℝ)) 1 (496078107991/500000000000 : ℝ) (992156215983/1000000000000 : ℝ) (496062604911/500000000000 : ℝ) (992125209823/1000000000000 : ℝ) (496070356451/500000000000 : ℝ) (992140712903/1000000000000 : ℝ) (49607035639/50000000000 : ℝ) (496070356391/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4145/32768 : ℝ)) 2 (496070356451/500000000000 : ℝ) (992140712903/1000000000000 : ℝ) (49607035639/50000000000 : ℝ) (496070356391/500000000000 : ℝ) (992140712841/1000000000000 : ℝ) (992140712843/1000000000000 : ℝ) (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4145/32768 : ℝ)) 3 (992140712841/1000000000000 : ℝ) (992140712843/1000000000000 : ℝ) (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ) (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ) (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4145/32768 : ℝ)) 4 (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ) (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ) (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ) (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4145/32768 : ℝ)) 5 (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ) (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ) (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ) (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4145/32768 : ℝ)) 6 (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ) (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ) (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ) (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4145/32768 : ℝ)) 7 (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ) (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ) (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ) (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4145/32768 : ℝ))) (17643422649/100000000000 : ℝ) (2756784789/15625000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4145/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17643422649/100000000000 : ℝ) (2756784789/15625000000 : ℝ) (117643422649/200000000000 : ℝ) (18381784789/31250000000 : ℝ) (84008148769/200000000000 : ℝ) (420040743853/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4145/32768 : ℝ))) 1 (117643422649/200000000000 : ℝ) (18381784789/31250000000 : ℝ) (84008148769/200000000000 : ℝ) (420040743853/1000000000000 : ℝ) (100825785709/200000000000 : ℝ) (504128928551/1000000000000 : ℝ) (124266637163/250000000000 : ℝ) (497066548659/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4145/32768 : ℝ))) 2 (100825785709/200000000000 : ℝ) (504128928551/1000000000000 : ℝ) (124266637163/250000000000 : ℝ) (497066548659/1000000000000 : ℝ) (250298869299/500000000000 : ℝ) (100119547721/200000000000 : ℝ) (50058528403/100000000000 : ℝ) (500585284037/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4145/32768 : ℝ))) 3 (250298869299/500000000000 : ℝ) (100119547721/200000000000 : ℝ) (50058528403/100000000000 : ℝ) (500585284037/1000000000000 : ℝ) (250295755657/500000000000 : ℝ) (500591511321/1000000000000 : ℝ) (20023660451/40000000000 : ℝ) (500591511283/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4145/32768 : ℝ))) 4 (250295755657/500000000000 : ℝ) (500591511321/1000000000000 : ℝ) (20023660451/40000000000 : ℝ) (500591511283/1000000000000 : ℝ) (250295755647/500000000000 : ℝ) (250295755651/500000000000 : ℝ) (250295755647/500000000000 : ℝ) (250295755651/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4145/32768 : ℝ))) 5 (250295755647/500000000000 : ℝ) (250295755651/500000000000 : ℝ) (250295755647/500000000000 : ℝ) (250295755651/500000000000 : ℝ) (250295755647/500000000000 : ℝ) (250295755651/500000000000 : ℝ) (250295755647/500000000000 : ℝ) (250295755651/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4145/32768 : ℝ))) 6 (250295755647/500000000000 : ℝ) (250295755651/500000000000 : ℝ) (250295755647/500000000000 : ℝ) (250295755651/500000000000 : ℝ) (250295755647/500000000000 : ℝ) (250295755651/500000000000 : ℝ) (250295755647/500000000000 : ℝ) (250295755651/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4145/32768 : ℝ))) 7 (250295755647/500000000000 : ℝ) (250295755651/500000000000 : ℝ) (250295755647/500000000000 : ℝ) (250295755651/500000000000 : ℝ) (250295755647/500000000000 : ℝ) (250295755651/500000000000 : ℝ) (250295755647/500000000000 : ℝ) (250295755651/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4145/32768 : ℝ)) hmem 8 (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ) (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4145/32768 : ℝ))) hcmem 8 (250295755647/500000000000 : ℝ) (250295755651/500000000000 : ℝ) (250295755647/500000000000 : ℝ) (250295755651/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4145/32768 : ℝ)) (24803517821/25000000000 : ℝ) (992140712843/1000000000000 : ℝ) (250295755647/500000000000 : ℝ) (250295755651/500000000000 : ℝ) (792556234197/1000000000000 : ℝ) (396278117107/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0379_exp_lower
  have heNumeric : (82196204551/40000000000 : ℝ)/4 ≤ Real.exp (-42628140005321/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (82196204551/40000000000 : ℝ)/4 ≤ Real.exp ((33159/262144 : ℝ)-(396278117107/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33159/262144 : ℝ) (4145/32768 : ℝ) (396278117107/500000000000 : ℝ) (82196204551/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0380; no trusted numerical premise.
theorem cover8_leaf0380_exp_radius : (499012701231234719/500000000000000000 : ℝ) ≤ Real.exp ((-33161/2097152 : ℝ)/8) ∧ Real.exp ((-33161/2097152 : ℝ)/8) ≤ (998025402462469439/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33161/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0380_exp_lower : (920113645427283981/1000000000000000000 : ℝ) ≤ Real.exp ((-1065703538299/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065703538299/1600000000000 : ℝ)/8) ≤ (460056822713641991/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065703538299/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0380_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054905064757/1000000000000 : ℝ) ≤ 4*Real.exp (4145/32768 : ℝ)*Real.exp (-mu (radius 8 (33161/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054905064757/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33161/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0380_exp_radius
  have hrNumeric : (61519497663/62500000000 : ℝ) ≤ Real.exp (-33161/2097152 : ℝ) ∧ Real.exp (-33161/2097152 : ℝ) ≤ (984311962609/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61519497663/62500000000 : ℝ) ≤ (radius 8 (33161/262144 : ℝ)) ∧ (radius 8 (33161/262144 : ℝ)) ≤ (984311962609/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33161/262144 : ℝ)) (61519497663/62500000000 : ℝ) (984311962609/1000000000000 : ℝ) (7057473799/40000000000 : ℝ) (176436844981/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33161/262144 : ℝ)) (61519497663/62500000000 : ℝ) (984311962609/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33161/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61519497663/62500000000 : ℝ) (984311962609/1000000000000 : ℝ) (124019497663/125000000000 : ℝ) (198431196261/200000000000 : ℝ) (992124973281/1000000000000 : ℝ) (496062486641/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33161/262144 : ℝ)) 1 (124019497663/125000000000 : ℝ) (198431196261/200000000000 : ℝ) (992124973281/1000000000000 : ℝ) (496062486641/500000000000 : ℝ) (248035119323/250000000000 : ℝ) (496070238647/500000000000 : ℝ) (992140477171/1000000000000 : ℝ) (992140477173/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33161/262144 : ℝ)) 2 (248035119323/250000000000 : ℝ) (496070238647/500000000000 : ℝ) (992140477171/1000000000000 : ℝ) (992140477173/1000000000000 : ℝ) (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ) (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33161/262144 : ℝ)) 3 (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ) (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ) (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ) (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33161/262144 : ℝ)) 4 (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ) (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ) (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ) (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33161/262144 : ℝ)) 5 (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ) (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ) (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ) (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33161/262144 : ℝ)) 6 (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ) (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ) (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ) (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33161/262144 : ℝ)) 7 (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ) (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ) (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ) (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33161/262144 : ℝ))) (7057473799/40000000000 : ℝ) (176436844981/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33161/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7057473799/40000000000 : ℝ) (176436844981/1000000000000 : ℝ) (588218422487/1000000000000 : ℝ) (588218422491/1000000000000 : ℝ) (16801754431/40000000000 : ℝ) (420043860783/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33161/262144 : ℝ))) 1 (588218422487/1000000000000 : ℝ) (588218422491/1000000000000 : ℝ) (16801754431/40000000000 : ℝ) (420043860783/1000000000000 : ℝ) (504131141631/1000000000000 : ℝ) (504131141637/1000000000000 : ℝ) (497068946083/1000000000000 : ℝ) (49706894609/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33161/262144 : ℝ))) 2 (504131141631/1000000000000 : ℝ) (504131141637/1000000000000 : ℝ) (497068946083/1000000000000 : ℝ) (49706894609/100000000000 : ℝ) (500600043857/1000000000000 : ℝ) (62575005483/125000000000 : ℝ) (125146897499/250000000000 : ℝ) (500587590003/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33161/262144 : ℝ))) 3 (500600043857/1000000000000 : ℝ) (62575005483/125000000000 : ℝ) (125146897499/250000000000 : ℝ) (500587590003/1000000000000 : ℝ) (250296908463/500000000000 : ℝ) (250296908467/500000000000 : ℝ) (500593816887/1000000000000 : ℝ) (100118763379/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33161/262144 : ℝ))) 4 (250296908463/500000000000 : ℝ) (250296908467/500000000000 : ℝ) (500593816887/1000000000000 : ℝ) (100118763379/200000000000 : ℝ) (250296908453/500000000000 : ℝ) (100118763383/200000000000 : ℝ) (250296908453/500000000000 : ℝ) (100118763383/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33161/262144 : ℝ))) 5 (250296908453/500000000000 : ℝ) (100118763383/200000000000 : ℝ) (250296908453/500000000000 : ℝ) (100118763383/200000000000 : ℝ) (250296908453/500000000000 : ℝ) (100118763383/200000000000 : ℝ) (250296908453/500000000000 : ℝ) (100118763383/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33161/262144 : ℝ))) 6 (250296908453/500000000000 : ℝ) (100118763383/200000000000 : ℝ) (250296908453/500000000000 : ℝ) (100118763383/200000000000 : ℝ) (250296908453/500000000000 : ℝ) (100118763383/200000000000 : ℝ) (250296908453/500000000000 : ℝ) (100118763383/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33161/262144 : ℝ))) 7 (250296908453/500000000000 : ℝ) (100118763383/200000000000 : ℝ) (250296908453/500000000000 : ℝ) (100118763383/200000000000 : ℝ) (250296908453/500000000000 : ℝ) (100118763383/200000000000 : ℝ) (250296908453/500000000000 : ℝ) (100118763383/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33161/262144 : ℝ)) hmem 8 (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ) (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33161/262144 : ℝ))) hcmem 8 (250296908453/500000000000 : ℝ) (100118763383/200000000000 : ℝ) (250296908453/500000000000 : ℝ) (100118763383/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33161/262144 : ℝ)) (992140477231/1000000000000 : ℝ) (496070238617/500000000000 : ℝ) (250296908453/500000000000 : ℝ) (100118763383/200000000000 : ℝ) (792560072747/1000000000000 : ℝ) (158512014553/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0380_exp_lower
  have heNumeric : (2054905064757/1000000000000 : ℝ)/4 ≤ Real.exp (-1065703538299/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054905064757/1000000000000 : ℝ)/4 ≤ Real.exp ((4145/32768 : ℝ)-(158512014553/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4145/32768 : ℝ) (33161/262144 : ℝ) (158512014553/200000000000 : ℝ) (2054905064757/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0381; no trusted numerical premise.
theorem cover8_leaf0381_exp_radius : (49901267148776081/50000000000000000 : ℝ) ≤ Real.exp ((-16581/1048576 : ℝ)/8) ∧ Real.exp ((-16581/1048576 : ℝ)/8) ≤ (998025342975521621/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16581/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0381_exp_lower : (920113642693541881/1000000000000000000 : ℝ) ≤ Real.exp ((-42628143053159/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628143053159/64000000000000 : ℝ)/8) ≤ (460056821346770941/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628143053159/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0381_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410981003183/200000000000 : ℝ) ≤ 4*Real.exp (33161/262144 : ℝ)*Real.exp (-mu (radius 8 (16581/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (410981003183/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16581/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0381_exp_radius
  have hrNumeric : (246077873313/250000000000 : ℝ) ≤ Real.exp (-16581/1048576 : ℝ) ∧ Real.exp (-16581/1048576 : ℝ) ≤ (984311493253/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246077873313/250000000000 : ℝ) ≤ (radius 8 (16581/131072 : ℝ)) ∧ (radius 8 (16581/131072 : ℝ)) ≤ (984311493253/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16581/131072 : ℝ)) (246077873313/250000000000 : ℝ) (984311493253/1000000000000 : ℝ) (88219731707/500000000000 : ℝ) (176439463421/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16581/131072 : ℝ)) (246077873313/250000000000 : ℝ) (984311493253/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16581/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246077873313/250000000000 : ℝ) (984311493253/1000000000000 : ℝ) (496077873313/500000000000 : ℝ) (992155746627/1000000000000 : ℝ) (49606236837/50000000000 : ℝ) (992124736741/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16581/131072 : ℝ)) 1 (496077873313/500000000000 : ℝ) (992155746627/1000000000000 : ℝ) (49606236837/50000000000 : ℝ) (992124736741/1000000000000 : ℝ) (992140241683/1000000000000 : ℝ) (248035060421/250000000000 : ℝ) (992140241561/1000000000000 : ℝ) (992140241563/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16581/131072 : ℝ)) 2 (992140241683/1000000000000 : ℝ) (248035060421/250000000000 : ℝ) (992140241561/1000000000000 : ℝ) (992140241563/1000000000000 : ℝ) (496070120811/500000000000 : ℝ) (124017530203/125000000000 : ℝ) (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16581/131072 : ℝ)) 3 (496070120811/500000000000 : ℝ) (124017530203/125000000000 : ℝ) (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ) (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ) (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16581/131072 : ℝ)) 4 (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ) (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ) (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ) (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16581/131072 : ℝ)) 5 (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ) (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ) (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ) (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16581/131072 : ℝ)) 6 (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ) (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ) (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ) (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16581/131072 : ℝ)) 7 (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ) (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ) (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ) (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16581/131072 : ℝ))) (88219731707/500000000000 : ℝ) (176439463421/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16581/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88219731707/500000000000 : ℝ) (176439463421/1000000000000 : ℝ) (588219731707/1000000000000 : ℝ) (588219731711/1000000000000 : ℝ) (420046977627/1000000000000 : ℝ) (105011744409/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16581/131072 : ℝ))) 1 (588219731707/1000000000000 : ℝ) (588219731711/1000000000000 : ℝ) (420046977627/1000000000000 : ℝ) (105011744409/250000000000 : ℝ) (504133354667/1000000000000 : ℝ) (252066677337/500000000000 : ℝ) (248535671727/500000000000 : ℝ) (248535671731/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16581/131072 : ℝ))) 2 (504133354667/1000000000000 : ℝ) (252066677337/500000000000 : ℝ) (248535671727/500000000000 : ℝ) (248535671731/500000000000 : ℝ) (25030117453/50000000000 : ℝ) (125150587267/250000000000 : ℝ) (500589895907/1000000000000 : ℝ) (100117979183/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16581/131072 : ℝ))) 3 (25030117453/50000000000 : ℝ) (125150587267/250000000000 : ℝ) (500589895907/1000000000000 : ℝ) (100117979183/200000000000 : ℝ) (500596122483/1000000000000 : ℝ) (125149030623/250000000000 : ℝ) (125149030611/250000000000 : ℝ) (500596122453/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16581/131072 : ℝ))) 4 (500596122483/1000000000000 : ℝ) (125149030623/250000000000 : ℝ) (125149030611/250000000000 : ℝ) (500596122453/1000000000000 : ℝ) (500596122463/1000000000000 : ℝ) (500596122473/1000000000000 : ℝ) (500596122463/1000000000000 : ℝ) (500596122473/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16581/131072 : ℝ))) 5 (500596122463/1000000000000 : ℝ) (500596122473/1000000000000 : ℝ) (500596122463/1000000000000 : ℝ) (500596122473/1000000000000 : ℝ) (500596122463/1000000000000 : ℝ) (500596122473/1000000000000 : ℝ) (500596122463/1000000000000 : ℝ) (500596122473/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16581/131072 : ℝ))) 6 (500596122463/1000000000000 : ℝ) (500596122473/1000000000000 : ℝ) (500596122463/1000000000000 : ℝ) (500596122473/1000000000000 : ℝ) (500596122463/1000000000000 : ℝ) (500596122473/1000000000000 : ℝ) (500596122463/1000000000000 : ℝ) (500596122473/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16581/131072 : ℝ))) 7 (500596122463/1000000000000 : ℝ) (500596122473/1000000000000 : ℝ) (500596122463/1000000000000 : ℝ) (500596122473/1000000000000 : ℝ) (500596122463/1000000000000 : ℝ) (500596122473/1000000000000 : ℝ) (500596122463/1000000000000 : ℝ) (500596122473/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16581/131072 : ℝ)) hmem 8 (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ) (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16581/131072 : ℝ))) hcmem 8 (500596122463/1000000000000 : ℝ) (500596122473/1000000000000 : ℝ) (500596122463/1000000000000 : ℝ) (500596122473/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16581/131072 : ℝ)) (992140241621/1000000000000 : ℝ) (124017530203/125000000000 : ℝ) (500596122463/1000000000000 : ℝ) (500596122473/1000000000000 : ℝ) (198140977803/250000000000 : ℝ) (792563911231/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0381_exp_lower
  have heNumeric : (410981003183/200000000000 : ℝ)/4 ≤ Real.exp (-42628143053159/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410981003183/200000000000 : ℝ)/4 ≤ Real.exp ((33161/262144 : ℝ)-(792563911231/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33161/262144 : ℝ) (16581/131072 : ℝ) (792563911231/1000000000000 : ℝ) (410981003183/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0382; no trusted numerical premise.
theorem cover8_leaf0382_exp_radius : (249506320872144337/250000000000000000 : ℝ) ≤ Real.exp ((-33163/2097152 : ℝ)/8) ∧ Real.exp ((-33163/2097152 : ℝ)/8) ≤ (998025283488577349/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33163/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0382_exp_lower : (920113639968770897/1000000000000000000 : ℝ) ≤ Real.exp ((-21314072284683/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314072284683/32000000000000 : ℝ)/8) ≤ (460056819984385449/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314072284683/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0382_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904967233/1000000000000 : ℝ) ≤ 4*Real.exp (16581/131072 : ℝ)*Real.exp (-mu (radius 8 (33163/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904967233/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33163/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0382_exp_radius
  have hrNumeric : (123038877987/125000000000 : ℝ) ≤ Real.exp (-33163/2097152 : ℝ) ∧ Real.exp (-33163/2097152 : ℝ) ≤ (984311023897/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123038877987/125000000000 : ℝ) ≤ (radius 8 (33163/262144 : ℝ)) ∧ (radius 8 (33163/262144 : ℝ)) ≤ (984311023897/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33163/262144 : ℝ)) (123038877987/125000000000 : ℝ) (984311023897/1000000000000 : ℝ) (176442081813/1000000000000 : ℝ) (8822104091/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33163/262144 : ℝ)) (123038877987/125000000000 : ℝ) (984311023897/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33163/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123038877987/125000000000 : ℝ) (984311023897/1000000000000 : ℝ) (248038877987/250000000000 : ℝ) (992155511949/1000000000000 : ℝ) (992124500199/1000000000000 : ℝ) (4960622501/5000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33163/262144 : ℝ)) 1 (248038877987/250000000000 : ℝ) (992155511949/1000000000000 : ℝ) (992124500199/1000000000000 : ℝ) (4960622501/5000000000 : ℝ) (992140006073/1000000000000 : ℝ) (39685600243/40000000000 : ℝ) (15502187593/15625000000 : ℝ) (496070002977/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33163/262144 : ℝ)) 2 (992140006073/1000000000000 : ℝ) (39685600243/40000000000 : ℝ) (15502187593/15625000000 : ℝ) (496070002977/500000000000 : ℝ) (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ) (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33163/262144 : ℝ)) 3 (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ) (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ) (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ) (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33163/262144 : ℝ)) 4 (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ) (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ) (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ) (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33163/262144 : ℝ)) 5 (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ) (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ) (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ) (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33163/262144 : ℝ)) 6 (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ) (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ) (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ) (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33163/262144 : ℝ)) 7 (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ) (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ) (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ) (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33163/262144 : ℝ))) (176442081813/1000000000000 : ℝ) (8822104091/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33163/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176442081813/1000000000000 : ℝ) (8822104091/50000000000 : ℝ) (294110520453/500000000000 : ℝ) (58822104091/100000000000 : ℝ) (52506261801/125000000000 : ℝ) (210025047209/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33163/262144 : ℝ))) 1 (294110520453/500000000000 : ℝ) (58822104091/100000000000 : ℝ) (52506261801/125000000000 : ℝ) (210025047209/500000000000 : ℝ) (504135567657/1000000000000 : ℝ) (31508472979/62500000000 : ℝ) (124268435193/250000000000 : ℝ) (24853687039/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33163/262144 : ℝ))) 2 (504135567657/1000000000000 : ℝ) (31508472979/62500000000 : ℝ) (124268435193/250000000000 : ℝ) (24853687039/50000000000 : ℝ) (250302327107/500000000000 : ℝ) (250302327111/500000000000 : ℝ) (62574025221/125000000000 : ℝ) (500592201777/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33163/262144 : ℝ))) 3 (250302327107/500000000000 : ℝ) (250302327111/500000000000 : ℝ) (62574025221/125000000000 : ℝ) (500592201777/1000000000000 : ℝ) (500598427991/1000000000000 : ℝ) (125149607/250000000 : ℝ) (31287401747/62500000000 : ℝ) (500598427961/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33163/262144 : ℝ))) 4 (500598427991/1000000000000 : ℝ) (125149607/250000000 : ℝ) (31287401747/62500000000 : ℝ) (500598427961/1000000000000 : ℝ) (500598427971/1000000000000 : ℝ) (500598427981/1000000000000 : ℝ) (500598427971/1000000000000 : ℝ) (500598427981/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33163/262144 : ℝ))) 5 (500598427971/1000000000000 : ℝ) (500598427981/1000000000000 : ℝ) (500598427971/1000000000000 : ℝ) (500598427981/1000000000000 : ℝ) (500598427971/1000000000000 : ℝ) (500598427981/1000000000000 : ℝ) (500598427971/1000000000000 : ℝ) (500598427981/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33163/262144 : ℝ))) 6 (500598427971/1000000000000 : ℝ) (500598427981/1000000000000 : ℝ) (500598427971/1000000000000 : ℝ) (500598427981/1000000000000 : ℝ) (500598427971/1000000000000 : ℝ) (500598427981/1000000000000 : ℝ) (500598427971/1000000000000 : ℝ) (500598427981/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33163/262144 : ℝ))) 7 (500598427971/1000000000000 : ℝ) (500598427981/1000000000000 : ℝ) (500598427971/1000000000000 : ℝ) (500598427981/1000000000000 : ℝ) (500598427971/1000000000000 : ℝ) (500598427981/1000000000000 : ℝ) (500598427971/1000000000000 : ℝ) (500598427981/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33163/262144 : ℝ)) hmem 8 (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ) (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33163/262144 : ℝ))) hcmem 8 (500598427971/1000000000000 : ℝ) (500598427981/1000000000000 : ℝ) (500598427971/1000000000000 : ℝ) (500598427981/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33163/262144 : ℝ)) (248035001503/250000000000 : ℝ) (198428001203/200000000000 : ℝ) (500598427971/1000000000000 : ℝ) (500598427981/1000000000000 : ℝ) (990709687/1250000000 : ℝ) (792567749619/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0382_exp_lower
  have heNumeric : (2054904967233/1000000000000 : ℝ)/4 ≤ Real.exp (-21314072284683/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904967233/1000000000000 : ℝ)/4 ≤ Real.exp ((16581/131072 : ℝ)-(792567749619/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16581/131072 : ℝ) (33163/262144 : ℝ) (792567749619/1000000000000 : ℝ) (2054904967233/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0383; no trusted numerical premise.
theorem cover8_leaf0383_exp_radius : (499012612000818311/500000000000000000 : ℝ) ≤ Real.exp ((-8291/524288 : ℝ)/8) ∧ Real.exp ((-8291/524288 : ℝ)/8) ≤ (998025224001636623/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8291/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0383_exp_lower : (920113637252510973/1000000000000000000 : ℝ) ≤ Real.exp ((-42628146080837/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628146080837/64000000000000 : ℝ)/8) ≤ (460056818626255487/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628146080837/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0383_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904918703/1000000000000 : ℝ) ≤ 4*Real.exp (33163/262144 : ℝ)*Real.exp (-mu (radius 8 (8291/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904918703/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8291/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0383_exp_radius
  have hrNumeric : (49215527727/50000000000 : ℝ) ≤ Real.exp (-8291/524288 : ℝ) ∧ Real.exp (-8291/524288 : ℝ) ≤ (984310554541/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49215527727/50000000000 : ℝ) ≤ (radius 8 (8291/65536 : ℝ)) ∧ (radius 8 (8291/65536 : ℝ)) ≤ (984310554541/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8291/65536 : ℝ)) (49215527727/50000000000 : ℝ) (984310554541/1000000000000 : ℝ) (176444700173/1000000000000 : ℝ) (176444700179/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8291/65536 : ℝ)) (49215527727/50000000000 : ℝ) (984310554541/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8291/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49215527727/50000000000 : ℝ) (984310554541/1000000000000 : ℝ) (99215527727/100000000000 : ℝ) (992155277271/1000000000000 : ℝ) (496062131829/500000000000 : ℝ) (49606213183/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8291/65536 : ℝ)) 1 (99215527727/100000000000 : ℝ) (992155277271/1000000000000 : ℝ) (496062131829/500000000000 : ℝ) (49606213183/50000000000 : ℝ) (31004367827/31250000000 : ℝ) (496069885233/500000000000 : ℝ) (496069885171/500000000000 : ℝ) (198427954069/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8291/65536 : ℝ)) 2 (31004367827/31250000000 : ℝ) (496069885233/500000000000 : ℝ) (496069885171/500000000000 : ℝ) (198427954069/200000000000 : ℝ) (992139770403/1000000000000 : ℝ) (496069885203/500000000000 : ℝ) (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8291/65536 : ℝ)) 3 (992139770403/1000000000000 : ℝ) (496069885203/500000000000 : ℝ) (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ) (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ) (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8291/65536 : ℝ)) 4 (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ) (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ) (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ) (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8291/65536 : ℝ)) 5 (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ) (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ) (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ) (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8291/65536 : ℝ)) 6 (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ) (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ) (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ) (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8291/65536 : ℝ)) 7 (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ) (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ) (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ) (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8291/65536 : ℝ))) (176444700173/1000000000000 : ℝ) (176444700179/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8291/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176444700173/1000000000000 : ℝ) (176444700179/1000000000000 : ℝ) (294111175043/500000000000 : ℝ) (58822235009/100000000000 : ℝ) (5250665139/12500000000 : ℝ) (420053211129/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8291/65536 : ℝ))) 1 (294111175043/500000000000 : ℝ) (58822235009/100000000000 : ℝ) (5250665139/12500000000 : ℝ) (420053211129/1000000000000 : ℝ) (504137780603/1000000000000 : ℝ) (50413778061/100000000000 : ℝ) (497076138037/1000000000000 : ℝ) (99415227609/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8291/65536 : ℝ))) 2 (504137780603/1000000000000 : ℝ) (50413778061/100000000000 : ℝ) (497076138037/1000000000000 : ℝ) (99415227609/200000000000 : ℝ) (12515173983/25000000000 : ℝ) (15643967479/31250000000 : ℝ) (500594507581/1000000000000 : ℝ) (500594507589/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8291/65536 : ℝ))) 3 (12515173983/25000000000 : ℝ) (15643967479/31250000000 : ℝ) (500594507581/1000000000000 : ℝ) (500594507589/1000000000000 : ℝ) (10012014669/20000000000 : ℝ) (500600733459/1000000000000 : ℝ) (500600733411/1000000000000 : ℝ) (25030036671/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8291/65536 : ℝ))) 4 (10012014669/20000000000 : ℝ) (500600733459/1000000000000 : ℝ) (500600733411/1000000000000 : ℝ) (25030036671/50000000000 : ℝ) (50060073343/100000000000 : ℝ) (391094323/781250000 : ℝ) (50060073343/100000000000 : ℝ) (391094323/781250000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8291/65536 : ℝ))) 5 (50060073343/100000000000 : ℝ) (391094323/781250000 : ℝ) (50060073343/100000000000 : ℝ) (391094323/781250000 : ℝ) (50060073343/100000000000 : ℝ) (391094323/781250000 : ℝ) (50060073343/100000000000 : ℝ) (391094323/781250000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8291/65536 : ℝ))) 6 (50060073343/100000000000 : ℝ) (391094323/781250000 : ℝ) (50060073343/100000000000 : ℝ) (391094323/781250000 : ℝ) (50060073343/100000000000 : ℝ) (391094323/781250000 : ℝ) (50060073343/100000000000 : ℝ) (391094323/781250000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8291/65536 : ℝ))) 7 (50060073343/100000000000 : ℝ) (391094323/781250000 : ℝ) (50060073343/100000000000 : ℝ) (391094323/781250000 : ℝ) (50060073343/100000000000 : ℝ) (391094323/781250000 : ℝ) (50060073343/100000000000 : ℝ) (391094323/781250000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8291/65536 : ℝ)) hmem 8 (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ) (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8291/65536 : ℝ))) hcmem 8 (50060073343/100000000000 : ℝ) (391094323/781250000 : ℝ) (50060073343/100000000000 : ℝ) (391094323/781250000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8291/65536 : ℝ)) (496069885201/500000000000 : ℝ) (496069885203/500000000000 : ℝ) (50060073343/100000000000 : ℝ) (391094323/781250000 : ℝ) (792571587913/1000000000000 : ℝ) (792571587933/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0383_exp_lower
  have heNumeric : (2054904918703/1000000000000 : ℝ)/4 ≤ Real.exp (-42628146080837/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904918703/1000000000000 : ℝ)/4 ≤ Real.exp ((33163/262144 : ℝ)-(792571587933/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33163/262144 : ℝ) (8291/65536 : ℝ) (792571587933/1000000000000 : ℝ) (2054904918703/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0384; no trusted numerical premise.
theorem cover8_leaf0384_exp_radius : (998025164514699441/1000000000000000000 : ℝ) ≤ Real.exp ((-33165/2097152 : ℝ)/8) ∧ Real.exp ((-33165/2097152 : ℝ)/8) ≤ (499012582257349721/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33165/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0384_exp_lower : (28753551079545381/31250000000000000 : ℝ) ≤ Real.exp ((-10657036896797/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657036896797/16000000000000 : ℝ)/8) ≤ (920113634545452193/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657036896797/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0384_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904870337/1000000000000 : ℝ) ≤ 4*Real.exp (8291/65536 : ℝ)*Real.exp (-mu (radius 8 (33165/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904870337/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33165/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0384_exp_radius
  have hrNumeric : (15379845081/15625000000 : ℝ) ≤ Real.exp (-33165/2097152 : ℝ) ∧ Real.exp (-33165/2097152 : ℝ) ≤ (196862017037/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (15379845081/15625000000 : ℝ) ≤ (radius 8 (33165/262144 : ℝ)) ∧ (radius 8 (33165/262144 : ℝ)) ≤ (196862017037/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33165/262144 : ℝ)) (15379845081/15625000000 : ℝ) (196862017037/200000000000 : ℝ) (44111829623/250000000000 : ℝ) (88223659249/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33165/262144 : ℝ)) (15379845081/15625000000 : ℝ) (196862017037/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33165/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (15379845081/15625000000 : ℝ) (196862017037/200000000000 : ℝ) (31004845081/31250000000 : ℝ) (992155042593/1000000000000 : ℝ) (992124027117/1000000000000 : ℝ) (992124027119/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33165/262144 : ℝ)) 1 (31004845081/31250000000 : ℝ) (992155042593/1000000000000 : ℝ) (992124027117/1000000000000 : ℝ) (992124027119/1000000000000 : ℝ) (496069767427/500000000000 : ℝ) (124017441857/125000000000 : ℝ) (992139534733/1000000000000 : ℝ) (198427906947/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33165/262144 : ℝ)) 2 (496069767427/500000000000 : ℝ) (124017441857/125000000000 : ℝ) (992139534733/1000000000000 : ℝ) (198427906947/200000000000 : ℝ) (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ) (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33165/262144 : ℝ)) 3 (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ) (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ) (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ) (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33165/262144 : ℝ)) 4 (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ) (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ) (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ) (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33165/262144 : ℝ)) 5 (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ) (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ) (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ) (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33165/262144 : ℝ)) 6 (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ) (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ) (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ) (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33165/262144 : ℝ)) 7 (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ) (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ) (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ) (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33165/262144 : ℝ))) (44111829623/250000000000 : ℝ) (88223659249/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33165/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44111829623/250000000000 : ℝ) (88223659249/500000000000 : ℝ) (294111829623/500000000000 : ℝ) (588223659249/1000000000000 : ℝ) (5250704097/12500000000 : ℝ) (420056327769/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33165/262144 : ℝ))) 1 (294111829623/500000000000 : ℝ) (588223659249/1000000000000 : ℝ) (5250704097/12500000000 : ℝ) (420056327769/1000000000000 : ℝ) (504139993503/1000000000000 : ℝ) (504139993509/1000000000000 : ℝ) (31067408453/62500000000 : ℝ) (99415707051/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33165/262144 : ℝ))) 2 (504139993503/1000000000000 : ℝ) (504139993509/1000000000000 : ℝ) (31067408453/62500000000 : ℝ) (99415707051/200000000000 : ℝ) (800974823/1600000000 : ℝ) (250304632191/500000000000 : ℝ) (15643650417/31250000000 : ℝ) (500596813351/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33165/262144 : ℝ))) 3 (800974823/1600000000 : ℝ) (250304632191/500000000000 : ℝ) (15643650417/31250000000 : ℝ) (500596813351/1000000000000 : ℝ) (500603038859/1000000000000 : ℝ) (500603038867/1000000000000 : ℝ) (25030151941/50000000000 : ℝ) (125150759707/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33165/262144 : ℝ))) 4 (500603038859/1000000000000 : ℝ) (500603038867/1000000000000 : ℝ) (25030151941/50000000000 : ℝ) (125150759707/250000000000 : ℝ) (500603038839/1000000000000 : ℝ) (3910961241/7812500000 : ℝ) (500603038839/1000000000000 : ℝ) (3910961241/7812500000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33165/262144 : ℝ))) 5 (500603038839/1000000000000 : ℝ) (3910961241/7812500000 : ℝ) (500603038839/1000000000000 : ℝ) (3910961241/7812500000 : ℝ) (500603038839/1000000000000 : ℝ) (3910961241/7812500000 : ℝ) (500603038839/1000000000000 : ℝ) (3910961241/7812500000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33165/262144 : ℝ))) 6 (500603038839/1000000000000 : ℝ) (3910961241/7812500000 : ℝ) (500603038839/1000000000000 : ℝ) (3910961241/7812500000 : ℝ) (500603038839/1000000000000 : ℝ) (3910961241/7812500000 : ℝ) (500603038839/1000000000000 : ℝ) (3910961241/7812500000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33165/262144 : ℝ))) 7 (500603038839/1000000000000 : ℝ) (3910961241/7812500000 : ℝ) (500603038839/1000000000000 : ℝ) (3910961241/7812500000 : ℝ) (500603038839/1000000000000 : ℝ) (3910961241/7812500000 : ℝ) (500603038839/1000000000000 : ℝ) (3910961241/7812500000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33165/262144 : ℝ)) hmem 8 (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ) (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33165/262144 : ℝ))) hcmem 8 (500603038839/1000000000000 : ℝ) (3910961241/7812500000 : ℝ) (500603038839/1000000000000 : ℝ) (3910961241/7812500000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33165/262144 : ℝ)) (992139534793/1000000000000 : ℝ) (248034883699/250000000000 : ℝ) (500603038839/1000000000000 : ℝ) (3910961241/7812500000 : ℝ) (792575426149/1000000000000 : ℝ) (792575426167/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0384_exp_lower
  have heNumeric : (2054904870337/1000000000000 : ℝ)/4 ≤ Real.exp (-10657036896797/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904870337/1000000000000 : ℝ)/4 ≤ Real.exp ((8291/65536 : ℝ)-(792575426167/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8291/65536 : ℝ) (33165/262144 : ℝ) (792575426167/1000000000000 : ℝ) (2054904870337/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0385; no trusted numerical premise.
theorem cover8_leaf0385_exp_radius : (499012552513882903/500000000000000000 : ℝ) ≤ Real.exp ((-16583/1048576 : ℝ)/8) ∧ Real.exp ((-16583/1048576 : ℝ)/8) ≤ (998025105027765807/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16583/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0385_exp_lower : (920113631847939599/1000000000000000000 : ℝ) ≤ Real.exp ((-42628149088227/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628149088227/64000000000000 : ℝ)/8) ≤ (2300284079619849/2500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628149088227/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0385_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452411071/500000000000 : ℝ) ≤ 4*Real.exp (33165/262144 : ℝ)*Real.exp (-mu (radius 8 (16583/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452411071/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16583/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0385_exp_radius
  have hrNumeric : (984309615829/1000000000000 : ℝ) ≤ Real.exp (-16583/1048576 : ℝ) ∧ Real.exp (-16583/1048576 : ℝ) ≤ (98430961583/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984309615829/1000000000000 : ℝ) ≤ (radius 8 (16583/131072 : ℝ)) ∧ (radius 8 (16583/131072 : ℝ)) ≤ (98430961583/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16583/131072 : ℝ)) (984309615829/1000000000000 : ℝ) (98430961583/100000000000 : ℝ) (35289987353/200000000000 : ℝ) (44112484193/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16583/131072 : ℝ)) (984309615829/1000000000000 : ℝ) (98430961583/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16583/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984309615829/1000000000000 : ℝ) (98430961583/100000000000 : ℝ) (496077403957/500000000000 : ℝ) (198430961583/200000000000 : ℝ) (992123790577/1000000000000 : ℝ) (496061895289/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16583/131072 : ℝ)) 1 (496077403957/500000000000 : ℝ) (198430961583/200000000000 : ℝ) (992123790577/1000000000000 : ℝ) (496061895289/500000000000 : ℝ) (198427859849/200000000000 : ℝ) (992139299247/1000000000000 : ℝ) (248034824781/250000000000 : ℝ) (496069649563/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16583/131072 : ℝ)) 2 (198427859849/200000000000 : ℝ) (992139299247/1000000000000 : ℝ) (248034824781/250000000000 : ℝ) (496069649563/500000000000 : ℝ) (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ) (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16583/131072 : ℝ)) 3 (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ) (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ) (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ) (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16583/131072 : ℝ)) 4 (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ) (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ) (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ) (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16583/131072 : ℝ)) 5 (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ) (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ) (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ) (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16583/131072 : ℝ)) 6 (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ) (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ) (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ) (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16583/131072 : ℝ)) 7 (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ) (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ) (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ) (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16583/131072 : ℝ))) (35289987353/200000000000 : ℝ) (44112484193/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16583/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35289987353/200000000000 : ℝ) (44112484193/250000000000 : ℝ) (294112484191/500000000000 : ℝ) (294112484193/500000000000 : ℝ) (420059444323/1000000000000 : ℝ) (105014861083/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16583/131072 : ℝ))) 1 (294112484191/500000000000 : ℝ) (294112484193/500000000000 : ℝ) (420059444323/1000000000000 : ℝ) (105014861083/250000000000 : ℝ) (31508887897/62500000000 : ℝ) (504142206359/1000000000000 : ℝ) (497080932399/1000000000000 : ℝ) (497080932407/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16583/131072 : ℝ))) 2 (31508887897/62500000000 : ℝ) (504142206359/1000000000000 : ℝ) (497080932399/1000000000000 : ℝ) (497080932407/1000000000000 : ℝ) (800978511/1600000000 : ℝ) (500611569383/1000000000000 : ℝ) (500599119051/1000000000000 : ℝ) (25029955953/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16583/131072 : ℝ))) 3 (800978511/1600000000 : ℝ) (500611569383/1000000000000 : ℝ) (500599119051/1000000000000 : ℝ) (25029955953/50000000000 : ℝ) (500605344213/1000000000000 : ℝ) (250302672111/500000000000 : ℝ) (250302672087/500000000000 : ℝ) (500605344183/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16583/131072 : ℝ))) 4 (500605344213/1000000000000 : ℝ) (250302672111/500000000000 : ℝ) (250302672087/500000000000 : ℝ) (500605344183/1000000000000 : ℝ) (500605344193/1000000000000 : ℝ) (500605344203/1000000000000 : ℝ) (500605344193/1000000000000 : ℝ) (500605344203/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16583/131072 : ℝ))) 5 (500605344193/1000000000000 : ℝ) (500605344203/1000000000000 : ℝ) (500605344193/1000000000000 : ℝ) (500605344203/1000000000000 : ℝ) (500605344193/1000000000000 : ℝ) (500605344203/1000000000000 : ℝ) (500605344193/1000000000000 : ℝ) (500605344203/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16583/131072 : ℝ))) 6 (500605344193/1000000000000 : ℝ) (500605344203/1000000000000 : ℝ) (500605344193/1000000000000 : ℝ) (500605344203/1000000000000 : ℝ) (500605344193/1000000000000 : ℝ) (500605344203/1000000000000 : ℝ) (500605344193/1000000000000 : ℝ) (500605344203/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16583/131072 : ℝ))) 7 (500605344193/1000000000000 : ℝ) (500605344203/1000000000000 : ℝ) (500605344193/1000000000000 : ℝ) (500605344203/1000000000000 : ℝ) (500605344193/1000000000000 : ℝ) (500605344203/1000000000000 : ℝ) (500605344193/1000000000000 : ℝ) (500605344203/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16583/131072 : ℝ)) hmem 8 (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ) (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16583/131072 : ℝ))) hcmem 8 (500605344193/1000000000000 : ℝ) (500605344203/1000000000000 : ℝ) (500605344193/1000000000000 : ℝ) (500605344203/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16583/131072 : ℝ)) (62008706199/62500000000 : ℝ) (992139299187/1000000000000 : ℝ) (500605344193/1000000000000 : ℝ) (500605344203/1000000000000 : ℝ) (792579264299/1000000000000 : ℝ) (396289632159/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0385_exp_lower
  have heNumeric : (1027452411071/500000000000 : ℝ)/4 ≤ Real.exp (-42628149088227/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452411071/500000000000 : ℝ)/4 ≤ Real.exp ((33165/262144 : ℝ)-(396289632159/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33165/262144 : ℝ) (16583/131072 : ℝ) (396289632159/500000000000 : ℝ) (1027452411071/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0386; no trusted numerical premise.
theorem cover8_leaf0386_exp_radius : (998025045540835717/1000000000000000000 : ℝ) ≤ Real.exp ((-33167/2097152 : ℝ)/8) ∧ Real.exp ((-33167/2097152 : ℝ)/8) ≤ (499012522770417859/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33167/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0386_exp_lower : (920113629158362993/1000000000000000000 : ℝ) ≤ Real.exp ((-852563011697/1280000000000 : ℝ)/8) ∧ Real.exp ((-852563011697/1280000000000 : ℝ)/8) ≤ (460056814579181497/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-852563011697/1280000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0386_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256863096761/125000000000 : ℝ) ≤ 4*Real.exp (16583/131072 : ℝ)*Real.exp (-mu (radius 8 (33167/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256863096761/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33167/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0386_exp_radius
  have hrNumeric : (984309146473/1000000000000 : ℝ) ≤ Real.exp (-33167/2097152 : ℝ) ∧ Real.exp (-33167/2097152 : ℝ) ≤ (492154573237/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984309146473/1000000000000 : ℝ) ≤ (radius 8 (33167/262144 : ℝ)) ∧ (radius 8 (33167/262144 : ℝ)) ≤ (492154573237/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33167/262144 : ℝ)) (984309146473/1000000000000 : ℝ) (492154573237/500000000000 : ℝ) (44113138751/250000000000 : ℝ) (176452555011/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33167/262144 : ℝ)) (984309146473/1000000000000 : ℝ) (492154573237/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33167/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984309146473/1000000000000 : ℝ) (492154573237/500000000000 : ℝ) (248038643309/250000000000 : ℝ) (992154573237/1000000000000 : ℝ) (198424710807/200000000000 : ℝ) (992123554037/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33167/262144 : ℝ)) 1 (248038643309/250000000000 : ℝ) (992154573237/1000000000000 : ℝ) (198424710807/200000000000 : ℝ) (992123554037/1000000000000 : ℝ) (198427812727/200000000000 : ℝ) (992139063637/1000000000000 : ℝ) (496069531757/500000000000 : ℝ) (248034765879/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33167/262144 : ℝ)) 2 (198427812727/200000000000 : ℝ) (992139063637/1000000000000 : ℝ) (496069531757/500000000000 : ℝ) (248034765879/250000000000 : ℝ) (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ) (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33167/262144 : ℝ)) 3 (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ) (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ) (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ) (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33167/262144 : ℝ)) 4 (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ) (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ) (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ) (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33167/262144 : ℝ)) 5 (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ) (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ) (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ) (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33167/262144 : ℝ)) 6 (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ) (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ) (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ) (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33167/262144 : ℝ)) 7 (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ) (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ) (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ) (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33167/262144 : ℝ))) (44113138751/250000000000 : ℝ) (176452555011/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33167/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44113138751/250000000000 : ℝ) (176452555011/1000000000000 : ℝ) (294113138751/500000000000 : ℝ) (294113138753/500000000000 : ℝ) (420062560821/1000000000000 : ℝ) (42006256083/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33167/262144 : ℝ))) 1 (294113138751/500000000000 : ℝ) (294113138753/500000000000 : ℝ) (420062560821/1000000000000 : ℝ) (42006256083/100000000000 : ℝ) (504144419161/1000000000000 : ℝ) (15754513099/31250000000 : ℝ) (248541664751/500000000000 : ℝ) (49708332951/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33167/262144 : ℝ))) 2 (504144419161/1000000000000 : ℝ) (15754513099/31250000000 : ℝ) (248541664751/500000000000 : ℝ) (49708332951/100000000000 : ℝ) (500613874331/1000000000000 : ℝ) (500613874339/1000000000000 : ℝ) (250300712357/500000000000 : ℝ) (500601424723/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33167/262144 : ℝ))) 3 (500613874331/1000000000000 : ℝ) (500613874339/1000000000000 : ℝ) (250300712357/500000000000 : ℝ) (500601424723/1000000000000 : ℝ) (250303824761/500000000000 : ℝ) (500607649531/1000000000000 : ℝ) (500607649483/1000000000000 : ℝ) (500607649493/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33167/262144 : ℝ))) 4 (250303824761/500000000000 : ℝ) (500607649531/1000000000000 : ℝ) (500607649483/1000000000000 : ℝ) (500607649493/1000000000000 : ℝ) (250303824751/500000000000 : ℝ) (62575956189/125000000000 : ℝ) (250303824751/500000000000 : ℝ) (62575956189/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33167/262144 : ℝ))) 5 (250303824751/500000000000 : ℝ) (62575956189/125000000000 : ℝ) (250303824751/500000000000 : ℝ) (62575956189/125000000000 : ℝ) (250303824751/500000000000 : ℝ) (62575956189/125000000000 : ℝ) (250303824751/500000000000 : ℝ) (62575956189/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33167/262144 : ℝ))) 6 (250303824751/500000000000 : ℝ) (62575956189/125000000000 : ℝ) (250303824751/500000000000 : ℝ) (62575956189/125000000000 : ℝ) (250303824751/500000000000 : ℝ) (62575956189/125000000000 : ℝ) (250303824751/500000000000 : ℝ) (62575956189/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33167/262144 : ℝ))) 7 (250303824751/500000000000 : ℝ) (62575956189/125000000000 : ℝ) (250303824751/500000000000 : ℝ) (62575956189/125000000000 : ℝ) (250303824751/500000000000 : ℝ) (62575956189/125000000000 : ℝ) (250303824751/500000000000 : ℝ) (62575956189/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33167/262144 : ℝ)) hmem 8 (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ) (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33167/262144 : ℝ))) hcmem 8 (250303824751/500000000000 : ℝ) (62575956189/125000000000 : ℝ) (250303824751/500000000000 : ℝ) (62575956189/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33167/262144 : ℝ)) (496069531787/500000000000 : ℝ) (992139063577/1000000000000 : ℝ) (250303824751/500000000000 : ℝ) (62575956189/125000000000 : ℝ) (39629155119/50000000000 : ℝ) (495364439/625000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0386_exp_lower
  have heNumeric : (256863096761/125000000000 : ℝ)/4 ≤ Real.exp (-852563011697/1280000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256863096761/125000000000 : ℝ)/4 ≤ Real.exp ((16583/131072 : ℝ)-(495364439/625000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16583/131072 : ℝ) (33167/262144 : ℝ) (495364439/625000000 : ℝ) (256863096761/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0387; no trusted numerical premise.
theorem cover8_leaf0387_exp_radius : (998024986053909173/1000000000000000000 : ℝ) ≤ Real.exp ((-2073/131072 : ℝ)/8) ∧ Real.exp ((-2073/131072 : ℝ)/8) ≤ (499012493026954587/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2073/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0387_exp_lower : (920113626478562603/1000000000000000000 : ℝ) ≤ Real.exp ((-42628152076033/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628152076033/64000000000000 : ℝ)/8) ≤ (230028406619640651/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628152076033/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0387_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490472621/100000000000 : ℝ) ≤ 4*Real.exp (33167/262144 : ℝ)*Real.exp (-mu (radius 8 (2073/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (205490472621/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2073/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0387_exp_radius
  have hrNumeric : (492154338559/500000000000 : ℝ) ≤ Real.exp (-2073/131072 : ℝ) ∧ Real.exp (-2073/131072 : ℝ) ≤ (984308677119/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492154338559/500000000000 : ℝ) ≤ (radius 8 (2073/16384 : ℝ)) ∧ (radius 8 (2073/16384 : ℝ)) ≤ (984308677119/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2073/16384 : ℝ)) (492154338559/500000000000 : ℝ) (984308677119/1000000000000 : ℝ) (176455173197/1000000000000 : ℝ) (44113793301/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2073/16384 : ℝ)) (492154338559/500000000000 : ℝ) (984308677119/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2073/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492154338559/500000000000 : ℝ) (984308677119/1000000000000 : ℝ) (992154338559/1000000000000 : ℝ) (775120577/781250000 : ℝ) (198424663499/200000000000 : ℝ) (124015414687/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2073/16384 : ℝ)) 1 (992154338559/1000000000000 : ℝ) (775120577/781250000 : ℝ) (198424663499/200000000000 : ℝ) (124015414687/125000000000 : ℝ) (992138828027/1000000000000 : ℝ) (248034707007/250000000000 : ℝ) (198427765581/200000000000 : ℝ) (992138827907/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2073/16384 : ℝ)) 2 (992138828027/1000000000000 : ℝ) (248034707007/250000000000 : ℝ) (198427765581/200000000000 : ℝ) (992138827907/1000000000000 : ℝ) (496069413983/500000000000 : ℝ) (15502169187/15625000000 : ℝ) (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2073/16384 : ℝ)) 3 (496069413983/500000000000 : ℝ) (15502169187/15625000000 : ℝ) (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ) (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ) (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2073/16384 : ℝ)) 4 (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ) (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ) (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ) (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2073/16384 : ℝ)) 5 (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ) (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ) (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ) (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2073/16384 : ℝ)) 6 (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ) (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ) (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ) (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2073/16384 : ℝ)) 7 (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ) (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ) (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ) (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2073/16384 : ℝ))) (176455173197/1000000000000 : ℝ) (44113793301/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2073/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176455173197/1000000000000 : ℝ) (44113793301/250000000000 : ℝ) (294113793299/500000000000 : ℝ) (294113793301/500000000000 : ℝ) (210032838621/500000000000 : ℝ) (420065677251/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2073/16384 : ℝ))) 1 (294113793299/500000000000 : ℝ) (294113793301/500000000000 : ℝ) (210032838621/500000000000 : ℝ) (420065677251/1000000000000 : ℝ) (6301832899/12500000000 : ℝ) (504146631927/1000000000000 : ℝ) (248542863273/500000000000 : ℝ) (248542863277/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2073/16384 : ℝ))) 2 (6301832899/12500000000 : ℝ) (504146631927/1000000000000 : ℝ) (248542863273/500000000000 : ℝ) (248542863277/500000000000 : ℝ) (500616179233/1000000000000 : ℝ) (500616179241/1000000000000 : ℝ) (500603730323/1000000000000 : ℝ) (500603730331/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2073/16384 : ℝ))) 3 (500616179233/1000000000000 : ℝ) (500616179241/1000000000000 : ℝ) (500603730323/1000000000000 : ℝ) (500603730331/1000000000000 : ℝ) (250304977389/500000000000 : ℝ) (250304977393/500000000000 : ℝ) (500609954739/1000000000000 : ℝ) (125152488687/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2073/16384 : ℝ))) 4 (250304977389/500000000000 : ℝ) (250304977393/500000000000 : ℝ) (500609954739/1000000000000 : ℝ) (125152488687/250000000000 : ℝ) (250304977379/500000000000 : ℝ) (500609954767/1000000000000 : ℝ) (250304977379/500000000000 : ℝ) (500609954767/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2073/16384 : ℝ))) 5 (250304977379/500000000000 : ℝ) (500609954767/1000000000000 : ℝ) (250304977379/500000000000 : ℝ) (500609954767/1000000000000 : ℝ) (250304977379/500000000000 : ℝ) (500609954767/1000000000000 : ℝ) (250304977379/500000000000 : ℝ) (500609954767/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2073/16384 : ℝ))) 6 (250304977379/500000000000 : ℝ) (500609954767/1000000000000 : ℝ) (250304977379/500000000000 : ℝ) (500609954767/1000000000000 : ℝ) (250304977379/500000000000 : ℝ) (500609954767/1000000000000 : ℝ) (250304977379/500000000000 : ℝ) (500609954767/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2073/16384 : ℝ))) 7 (250304977379/500000000000 : ℝ) (500609954767/1000000000000 : ℝ) (250304977379/500000000000 : ℝ) (500609954767/1000000000000 : ℝ) (250304977379/500000000000 : ℝ) (500609954767/1000000000000 : ℝ) (250304977379/500000000000 : ℝ) (500609954767/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2073/16384 : ℝ)) hmem 8 (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ) (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2073/16384 : ℝ))) hcmem 8 (250304977379/500000000000 : ℝ) (500609954767/1000000000000 : ℝ) (250304977379/500000000000 : ℝ) (500609954767/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2073/16384 : ℝ)) (198427765593/200000000000 : ℝ) (15502169187/15625000000 : ℝ) (250304977379/500000000000 : ℝ) (500609954767/1000000000000 : ℝ) (792586940379/1000000000000 : ℝ) (792586940397/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0387_exp_lower
  have heNumeric : (205490472621/100000000000 : ℝ)/4 ≤ Real.exp (-42628152076033/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490472621/100000000000 : ℝ)/4 ≤ Real.exp ((33167/262144 : ℝ)-(792586940397/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33167/262144 : ℝ) (2073/16384 : ℝ) (792586940397/1000000000000 : ℝ) (205490472621/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0388; no trusted numerical premise.
theorem cover8_leaf0388_exp_radius : (39920997062679447/40000000000000000 : ℝ) ≤ Real.exp ((-33169/2097152 : ℝ)/8) ∧ Real.exp ((-33169/2097152 : ℝ)/8) ≤ (15594139477609159/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33169/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0388_exp_lower : (920113623808538427/1000000000000000000 : ℝ) ≤ Real.exp ((-2664259597611/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664259597611/4000000000000 : ℝ)/8) ≤ (230028405952134607/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664259597611/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0388_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980935701/200000000000 : ℝ) ≤ 4*Real.exp (2073/16384 : ℝ)*Real.exp (-mu (radius 8 (33169/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980935701/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33169/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0388_exp_radius
  have hrNumeric : (246077051941/250000000000 : ℝ) ≤ Real.exp (-33169/2097152 : ℝ) ∧ Real.exp (-33169/2097152 : ℝ) ≤ (196861641553/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246077051941/250000000000 : ℝ) ≤ (radius 8 (33169/262144 : ℝ)) ∧ (radius 8 (33169/262144 : ℝ)) ≤ (196861641553/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33169/262144 : ℝ)) (246077051941/250000000000 : ℝ) (196861641553/200000000000 : ℝ) (35291558269/200000000000 : ℝ) (176457791351/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33169/262144 : ℝ)) (246077051941/250000000000 : ℝ) (196861641553/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33169/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246077051941/250000000000 : ℝ) (196861641553/200000000000 : ℝ) (496077051941/500000000000 : ℝ) (992154103883/1000000000000 : ℝ) (198424616191/200000000000 : ℝ) (248030770239/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33169/262144 : ℝ)) 1 (496077051941/500000000000 : ℝ) (992154103883/1000000000000 : ℝ) (198424616191/200000000000 : ℝ) (248030770239/250000000000 : ℝ) (496069296209/500000000000 : ℝ) (49606929621/50000000000 : ℝ) (992138592297/1000000000000 : ℝ) (992138592299/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33169/262144 : ℝ)) 2 (496069296209/500000000000 : ℝ) (49606929621/50000000000 : ℝ) (992138592297/1000000000000 : ℝ) (992138592299/1000000000000 : ℝ) (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ) (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33169/262144 : ℝ)) 3 (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ) (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ) (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ) (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33169/262144 : ℝ)) 4 (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ) (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ) (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ) (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33169/262144 : ℝ)) 5 (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ) (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ) (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ) (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33169/262144 : ℝ)) 6 (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ) (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ) (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ) (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33169/262144 : ℝ)) 7 (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ) (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ) (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ) (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33169/262144 : ℝ))) (35291558269/200000000000 : ℝ) (176457791351/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33169/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35291558269/200000000000 : ℝ) (176457791351/1000000000000 : ℝ) (73528611959/125000000000 : ℝ) (147057223919/250000000000 : ℝ) (210034396793/500000000000 : ℝ) (210034396797/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33169/262144 : ℝ))) 1 (73528611959/125000000000 : ℝ) (147057223919/250000000000 : ℝ) (210034396793/500000000000 : ℝ) (210034396797/500000000000 : ℝ) (504148844629/1000000000000 : ℝ) (100829768927/200000000000 : ℝ) (124272030883/250000000000 : ℝ) (24854406177/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33169/262144 : ℝ))) 2 (504148844629/1000000000000 : ℝ) (100829768927/200000000000 : ℝ) (124272030883/250000000000 : ℝ) (24854406177/50000000000 : ℝ) (6257731051/12500000000 : ℝ) (62577310511/125000000000 : ℝ) (500606035877/1000000000000 : ℝ) (100121207177/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33169/262144 : ℝ))) 3 (6257731051/12500000000 : ℝ) (62577310511/125000000000 : ℝ) (500606035877/1000000000000 : ℝ) (100121207177/200000000000 : ℝ) (250306129989/500000000000 : ℝ) (500612259987/1000000000000 : ℝ) (500612259939/1000000000000 : ℝ) (125153064987/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33169/262144 : ℝ))) 4 (250306129989/500000000000 : ℝ) (500612259987/1000000000000 : ℝ) (500612259939/1000000000000 : ℝ) (125153064987/250000000000 : ℝ) (250306129979/500000000000 : ℝ) (3911033281/7812500000 : ℝ) (250306129979/500000000000 : ℝ) (3911033281/7812500000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33169/262144 : ℝ))) 5 (250306129979/500000000000 : ℝ) (3911033281/7812500000 : ℝ) (250306129979/500000000000 : ℝ) (3911033281/7812500000 : ℝ) (250306129979/500000000000 : ℝ) (3911033281/7812500000 : ℝ) (250306129979/500000000000 : ℝ) (3911033281/7812500000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33169/262144 : ℝ))) 6 (250306129979/500000000000 : ℝ) (3911033281/7812500000 : ℝ) (250306129979/500000000000 : ℝ) (3911033281/7812500000 : ℝ) (250306129979/500000000000 : ℝ) (3911033281/7812500000 : ℝ) (250306129979/500000000000 : ℝ) (3911033281/7812500000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33169/262144 : ℝ))) 7 (250306129979/500000000000 : ℝ) (3911033281/7812500000 : ℝ) (250306129979/500000000000 : ℝ) (3911033281/7812500000 : ℝ) (250306129979/500000000000 : ℝ) (3911033281/7812500000 : ℝ) (250306129979/500000000000 : ℝ) (3911033281/7812500000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33169/262144 : ℝ)) hmem 8 (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ) (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33169/262144 : ℝ))) hcmem 8 (250306129979/500000000000 : ℝ) (3911033281/7812500000 : ℝ) (250306129979/500000000000 : ℝ) (3911033281/7812500000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33169/262144 : ℝ)) (992138592357/1000000000000 : ℝ) (24803464809/25000000000 : ℝ) (250306129979/500000000000 : ℝ) (3911033281/7812500000 : ℝ) (79259077829/100000000000 : ℝ) (792590778309/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0388_exp_lower
  have heNumeric : (410980935701/200000000000 : ℝ)/4 ≤ Real.exp (-2664259597611/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980935701/200000000000 : ℝ)/4 ≤ Real.exp ((2073/16384 : ℝ)-(792590778309/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2073/16384 : ℝ) (33169/262144 : ℝ) (792590778309/1000000000000 : ℝ) (410980935701/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0389; no trusted numerical premise.
theorem cover8_leaf0389_exp_radius : (998024867080066723/1000000000000000000 : ℝ) ≤ Real.exp ((-16585/1048576 : ℝ)/8) ∧ Real.exp ((-16585/1048576 : ℝ)/8) ≤ (249506216770016681/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16585/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0389_exp_lower : (920113621146220211/1000000000000000000 : ℝ) ≤ Real.exp ((-42628155043231/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628155043231/64000000000000 : ℝ)/8) ≤ (230028405286555053/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628155043231/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0389_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904630939/1000000000000 : ℝ) ≤ 4*Real.exp (33169/262144 : ℝ)*Real.exp (-mu (radius 8 (16585/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904630939/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16585/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0389_exp_radius
  have hrNumeric : (984307738409/1000000000000 : ℝ) ≤ Real.exp (-16585/1048576 : ℝ) ∧ Real.exp (-16585/1048576 : ℝ) ≤ (98430773841/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984307738409/1000000000000 : ℝ) ≤ (radius 8 (16585/131072 : ℝ)) ∧ (radius 8 (16585/131072 : ℝ)) ≤ (98430773841/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16585/131072 : ℝ)) (984307738409/1000000000000 : ℝ) (98430773841/100000000000 : ℝ) (88230204729/500000000000 : ℝ) (22057551183/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16585/131072 : ℝ)) (984307738409/1000000000000 : ℝ) (98430773841/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16585/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984307738409/1000000000000 : ℝ) (98430773841/100000000000 : ℝ) (248038467301/250000000000 : ℝ) (198430773841/200000000000 : ℝ) (496061422207/500000000000 : ℝ) (198424568883/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16585/131072 : ℝ)) 1 (248038467301/250000000000 : ℝ) (198430773841/200000000000 : ℝ) (496061422207/500000000000 : ℝ) (198424568883/200000000000 : ℝ) (992138356809/1000000000000 : ℝ) (99213835681/100000000000 : ℝ) (992138356687/1000000000000 : ℝ) (992138356689/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16585/131072 : ℝ)) 2 (992138356809/1000000000000 : ℝ) (99213835681/100000000000 : ℝ) (992138356687/1000000000000 : ℝ) (992138356689/1000000000000 : ℝ) (248034589187/250000000000 : ℝ) (3968553427/4000000000 : ℝ) (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16585/131072 : ℝ)) 3 (248034589187/250000000000 : ℝ) (3968553427/4000000000 : ℝ) (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ) (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ) (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16585/131072 : ℝ)) 4 (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ) (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ) (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ) (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16585/131072 : ℝ)) 5 (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ) (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ) (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ) (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16585/131072 : ℝ)) 6 (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ) (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ) (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ) (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16585/131072 : ℝ)) 7 (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ) (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ) (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ) (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16585/131072 : ℝ))) (88230204729/500000000000 : ℝ) (22057551183/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16585/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88230204729/500000000000 : ℝ) (22057551183/125000000000 : ℝ) (588230204729/1000000000000 : ℝ) (147057551183/250000000000 : ℝ) (84014381973/200000000000 : ℝ) (420071909873/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16585/131072 : ℝ))) 1 (588230204729/1000000000000 : ℝ) (147057551183/250000000000 : ℝ) (84014381973/200000000000 : ℝ) (420071909873/1000000000000 : ℝ) (504151057297/1000000000000 : ℝ) (504151057303/1000000000000 : ℝ) (497090520469/1000000000000 : ℝ) (124272630119/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16585/131072 : ℝ))) 2 (504151057297/1000000000000 : ℝ) (504151057303/1000000000000 : ℝ) (497090520469/1000000000000 : ℝ) (124272630119/250000000000 : ℝ) (500620788883/1000000000000 : ℝ) (50062078889/100000000000 : ℝ) (500608341387/1000000000000 : ℝ) (100121668279/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16585/131072 : ℝ))) 3 (500620788883/1000000000000 : ℝ) (50062078889/100000000000 : ℝ) (500608341387/1000000000000 : ℝ) (100121668279/200000000000 : ℝ) (100122913027/200000000000 : ℝ) (500614565143/1000000000000 : ℝ) (62576820637/125000000000 : ℝ) (31288410319/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16585/131072 : ℝ))) 4 (100122913027/200000000000 : ℝ) (500614565143/1000000000000 : ℝ) (62576820637/125000000000 : ℝ) (31288410319/62500000000 : ℝ) (100122913023/200000000000 : ℝ) (125153641281/250000000000 : ℝ) (100122913023/200000000000 : ℝ) (125153641281/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16585/131072 : ℝ))) 5 (100122913023/200000000000 : ℝ) (125153641281/250000000000 : ℝ) (100122913023/200000000000 : ℝ) (125153641281/250000000000 : ℝ) (100122913023/200000000000 : ℝ) (125153641281/250000000000 : ℝ) (100122913023/200000000000 : ℝ) (125153641281/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16585/131072 : ℝ))) 6 (100122913023/200000000000 : ℝ) (125153641281/250000000000 : ℝ) (100122913023/200000000000 : ℝ) (125153641281/250000000000 : ℝ) (100122913023/200000000000 : ℝ) (125153641281/250000000000 : ℝ) (100122913023/200000000000 : ℝ) (125153641281/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16585/131072 : ℝ))) 7 (100122913023/200000000000 : ℝ) (125153641281/250000000000 : ℝ) (100122913023/200000000000 : ℝ) (125153641281/250000000000 : ℝ) (100122913023/200000000000 : ℝ) (125153641281/250000000000 : ℝ) (100122913023/200000000000 : ℝ) (125153641281/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16585/131072 : ℝ)) hmem 8 (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ) (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16585/131072 : ℝ))) hcmem 8 (100122913023/200000000000 : ℝ) (125153641281/250000000000 : ℝ) (100122913023/200000000000 : ℝ) (125153641281/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16585/131072 : ℝ)) (992138356747/1000000000000 : ℝ) (3968553427/4000000000 : ℝ) (100122913023/200000000000 : ℝ) (125153641281/250000000000 : ℝ) (99074327017/125000000000 : ℝ) (396297308077/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0389_exp_lower
  have heNumeric : (2054904630939/1000000000000 : ℝ)/4 ≤ Real.exp (-42628155043231/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904630939/1000000000000 : ℝ)/4 ≤ Real.exp ((33169/262144 : ℝ)-(396297308077/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33169/262144 : ℝ) (16585/131072 : ℝ) (396297308077/500000000000 : ℝ) (2054904630939/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0390; no trusted numerical premise.
theorem cover8_leaf0390_exp_radius : (998024807593150817/1000000000000000000 : ℝ) ≤ Real.exp ((-33171/2097152 : ℝ)/8) ∧ Real.exp ((-33171/2097152 : ℝ)/8) ≤ (499012403796575409/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33171/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0390_exp_lower : (1472181789588781/1600000000000000 : ℝ) ≤ Real.exp ((-4262815651963/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262815651963/6400000000000 : ℝ)/8) ≤ (460056809246494063/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262815651963/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0390_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980916707/200000000000 : ℝ) ≤ 4*Real.exp (16585/131072 : ℝ)*Real.exp (-mu (radius 8 (33171/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980916707/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33171/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0390_exp_radius
  have hrNumeric : (492153634527/500000000000 : ℝ) ≤ Real.exp (-33171/2097152 : ℝ) ∧ Real.exp (-33171/2097152 : ℝ) ≤ (196861453811/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492153634527/500000000000 : ℝ) ≤ (radius 8 (33171/262144 : ℝ)) ∧ (radius 8 (33171/262144 : ℝ)) ≤ (196861453811/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33171/262144 : ℝ)) (492153634527/500000000000 : ℝ) (196861453811/200000000000 : ℝ) (176463027531/1000000000000 : ℝ) (176463027537/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33171/262144 : ℝ)) (492153634527/500000000000 : ℝ) (196861453811/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33171/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492153634527/500000000000 : ℝ) (196861453811/200000000000 : ℝ) (992153634527/1000000000000 : ℝ) (31004801079/31250000000 : ℝ) (992122607873/1000000000000 : ℝ) (7936980863/8000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33171/262144 : ℝ)) 1 (992153634527/1000000000000 : ℝ) (31004801079/31250000000 : ℝ) (992122607873/1000000000000 : ℝ) (7936980863/8000000000 : ℝ) (2480345303/2500000000 : ℝ) (496069060601/500000000000 : ℝ) (496069060539/500000000000 : ℝ) (992138121081/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33171/262144 : ℝ)) 2 (2480345303/2500000000 : ℝ) (496069060601/500000000000 : ℝ) (496069060539/500000000000 : ℝ) (992138121081/1000000000000 : ℝ) (992138121139/1000000000000 : ℝ) (496069060571/500000000000 : ℝ) (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33171/262144 : ℝ)) 3 (992138121139/1000000000000 : ℝ) (496069060571/500000000000 : ℝ) (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ) (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ) (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33171/262144 : ℝ)) 4 (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ) (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ) (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ) (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33171/262144 : ℝ)) 5 (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ) (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ) (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ) (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33171/262144 : ℝ)) 6 (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ) (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ) (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ) (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33171/262144 : ℝ)) 7 (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ) (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ) (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ) (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33171/262144 : ℝ))) (176463027531/1000000000000 : ℝ) (176463027537/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33171/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176463027531/1000000000000 : ℝ) (176463027537/1000000000000 : ℝ) (117646302753/200000000000 : ℝ) (588231513769/1000000000000 : ℝ) (420075026073/1000000000000 : ℝ) (210037513041/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33171/262144 : ℝ))) 1 (117646302753/200000000000 : ℝ) (588231513769/1000000000000 : ℝ) (420075026073/1000000000000 : ℝ) (210037513041/500000000000 : ℝ) (504153269919/1000000000000 : ℝ) (252076634963/500000000000 : ℝ) (62136614669/125000000000 : ℝ) (6213661467/12500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33171/262144 : ℝ))) 2 (504153269919/1000000000000 : ℝ) (252076634963/500000000000 : ℝ) (62136614669/125000000000 : ℝ) (6213661467/12500000000 : ℝ) (100124618727/200000000000 : ℝ) (500623093643/1000000000000 : ℝ) (500610646847/1000000000000 : ℝ) (100122129371/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33171/262144 : ℝ))) 3 (100124618727/200000000000 : ℝ) (500623093643/1000000000000 : ℝ) (500610646847/1000000000000 : ℝ) (100122129371/200000000000 : ℝ) (500616870241/1000000000000 : ℝ) (500616870249/1000000000000 : ℝ) (250308435101/500000000000 : ℝ) (500616870211/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33171/262144 : ℝ))) 4 (500616870241/1000000000000 : ℝ) (500616870249/1000000000000 : ℝ) (250308435101/500000000000 : ℝ) (500616870211/1000000000000 : ℝ) (500616870221/1000000000000 : ℝ) (50061687023/100000000000 : ℝ) (500616870221/1000000000000 : ℝ) (50061687023/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33171/262144 : ℝ))) 5 (500616870221/1000000000000 : ℝ) (50061687023/100000000000 : ℝ) (500616870221/1000000000000 : ℝ) (50061687023/100000000000 : ℝ) (500616870221/1000000000000 : ℝ) (50061687023/100000000000 : ℝ) (500616870221/1000000000000 : ℝ) (50061687023/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33171/262144 : ℝ))) 6 (500616870221/1000000000000 : ℝ) (50061687023/100000000000 : ℝ) (500616870221/1000000000000 : ℝ) (50061687023/100000000000 : ℝ) (500616870221/1000000000000 : ℝ) (50061687023/100000000000 : ℝ) (500616870221/1000000000000 : ℝ) (50061687023/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33171/262144 : ℝ))) 7 (500616870221/1000000000000 : ℝ) (50061687023/100000000000 : ℝ) (500616870221/1000000000000 : ℝ) (50061687023/100000000000 : ℝ) (500616870221/1000000000000 : ℝ) (50061687023/100000000000 : ℝ) (500616870221/1000000000000 : ℝ) (50061687023/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33171/262144 : ℝ)) hmem 8 (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ) (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33171/262144 : ℝ))) hcmem 8 (500616870221/1000000000000 : ℝ) (50061687023/100000000000 : ℝ) (500616870221/1000000000000 : ℝ) (50061687023/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33171/262144 : ℝ)) (496069060569/500000000000 : ℝ) (496069060571/500000000000 : ℝ) (500616870221/1000000000000 : ℝ) (50061687023/100000000000 : ℝ) (396299226951/500000000000 : ℝ) (4953740337/6250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0390_exp_lower
  have heNumeric : (410980916707/200000000000 : ℝ)/4 ≤ Real.exp (-4262815651963/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980916707/200000000000 : ℝ)/4 ≤ Real.exp ((16585/131072 : ℝ)-(4953740337/6250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16585/131072 : ℝ) (33171/262144 : ℝ) (4953740337/6250000000 : ℝ) (410980916707/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0391; no trusted numerical premise.
theorem cover8_leaf0391_exp_radius : (124753093513279807/125000000000000000 : ℝ) ≤ Real.exp ((-8293/524288 : ℝ)/8) ∧ Real.exp ((-8293/524288 : ℝ)/8) ≤ (998024748106238457/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8293/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0391_exp_lower : (920113615849417239/1000000000000000000 : ℝ) ≤ Real.exp ((-42628157990653/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628157990653/64000000000000 : ℝ)/8) ≤ (23002840396235431/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628157990653/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0391_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431533519/62500000000 : ℝ) ≤ 4*Real.exp (33171/262144 : ℝ)*Real.exp (-mu (radius 8 (8293/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (128431533519/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8293/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0391_exp_radius
  have hrNumeric : (9843067997/10000000000 : ℝ) ≤ Real.exp (-8293/524288 : ℝ) ∧ Real.exp (-8293/524288 : ℝ) ≤ (984306799701/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (9843067997/10000000000 : ℝ) ≤ (radius 8 (8293/65536 : ℝ)) ∧ (radius 8 (8293/65536 : ℝ)) ≤ (984306799701/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8293/65536 : ℝ)) (9843067997/10000000000 : ℝ) (984306799701/1000000000000 : ℝ) (88232822779/500000000000 : ℝ) (35293129113/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8293/65536 : ℝ)) (9843067997/10000000000 : ℝ) (984306799701/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8293/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (9843067997/10000000000 : ℝ) (984306799701/1000000000000 : ℝ) (19843067997/20000000000 : ℝ) (992153399851/1000000000000 : ℝ) (992122371333/1000000000000 : ℝ) (496061185667/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8293/65536 : ℝ)) 1 (19843067997/20000000000 : ℝ) (992153399851/1000000000000 : ℝ) (992122371333/1000000000000 : ℝ) (496061185667/500000000000 : ℝ) (992137885591/1000000000000 : ℝ) (992137885593/1000000000000 : ℝ) (99213788547/100000000000 : ℝ) (31004308921/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8293/65536 : ℝ)) 2 (992137885591/1000000000000 : ℝ) (992137885593/1000000000000 : ℝ) (99213788547/100000000000 : ℝ) (31004308921/31250000000 : ℝ) (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ) (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8293/65536 : ℝ)) 3 (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ) (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ) (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ) (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8293/65536 : ℝ)) 4 (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ) (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ) (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ) (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8293/65536 : ℝ)) 5 (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ) (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ) (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ) (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8293/65536 : ℝ)) 6 (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ) (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ) (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ) (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8293/65536 : ℝ)) 7 (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ) (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ) (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ) (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8293/65536 : ℝ))) (88232822779/500000000000 : ℝ) (35293129113/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8293/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88232822779/500000000000 : ℝ) (35293129113/200000000000 : ℝ) (588232822779/1000000000000 : ℝ) (588232822783/1000000000000 : ℝ) (105019535551/250000000000 : ℝ) (420078142213/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8293/65536 : ℝ))) 1 (588232822779/1000000000000 : ℝ) (588232822783/1000000000000 : ℝ) (105019535551/250000000000 : ℝ) (420078142213/1000000000000 : ℝ) (504155482491/1000000000000 : ℝ) (252077741249/500000000000 : ℝ) (1941778571/3906250000 : ℝ) (62136914273/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8293/65536 : ℝ))) 2 (504155482491/1000000000000 : ℝ) (252077741249/500000000000 : ℝ) (1941778571/3906250000 : ℝ) (62136914273/125000000000 : ℝ) (500625398333/1000000000000 : ℝ) (500625398341/1000000000000 : ℝ) (500612952251/1000000000000 : ℝ) (25030647613/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8293/65536 : ℝ))) 3 (500625398333/1000000000000 : ℝ) (500625398341/1000000000000 : ℝ) (500612952251/1000000000000 : ℝ) (25030647613/50000000000 : ℝ) (125154793823/250000000000 : ℝ) (500619175301/1000000000000 : ℝ) (500619175253/1000000000000 : ℝ) (250309587631/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8293/65536 : ℝ))) 4 (125154793823/250000000000 : ℝ) (500619175301/1000000000000 : ℝ) (500619175253/1000000000000 : ℝ) (250309587631/500000000000 : ℝ) (62577396909/125000000000 : ℝ) (250309587641/500000000000 : ℝ) (62577396909/125000000000 : ℝ) (250309587641/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8293/65536 : ℝ))) 5 (62577396909/125000000000 : ℝ) (250309587641/500000000000 : ℝ) (62577396909/125000000000 : ℝ) (250309587641/500000000000 : ℝ) (62577396909/125000000000 : ℝ) (250309587641/500000000000 : ℝ) (62577396909/125000000000 : ℝ) (250309587641/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8293/65536 : ℝ))) 6 (62577396909/125000000000 : ℝ) (250309587641/500000000000 : ℝ) (62577396909/125000000000 : ℝ) (250309587641/500000000000 : ℝ) (62577396909/125000000000 : ℝ) (250309587641/500000000000 : ℝ) (62577396909/125000000000 : ℝ) (250309587641/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8293/65536 : ℝ))) 7 (62577396909/125000000000 : ℝ) (250309587641/500000000000 : ℝ) (62577396909/125000000000 : ℝ) (250309587641/500000000000 : ℝ) (62577396909/125000000000 : ℝ) (250309587641/500000000000 : ℝ) (62577396909/125000000000 : ℝ) (250309587641/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8293/65536 : ℝ)) hmem 8 (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ) (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8293/65536 : ℝ))) hcmem 8 (62577396909/125000000000 : ℝ) (250309587641/500000000000 : ℝ) (62577396909/125000000000 : ℝ) (250309587641/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8293/65536 : ℝ)) (99213788553/100000000000 : ℝ) (992137885533/1000000000000 : ℝ) (62577396909/125000000000 : ℝ) (250309587641/500000000000 : ℝ) (792602291583/1000000000000 : ℝ) (396301145801/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0391_exp_lower
  have heNumeric : (128431533519/62500000000 : ℝ)/4 ≤ Real.exp (-42628157990653/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431533519/62500000000 : ℝ)/4 ≤ Real.exp ((33171/262144 : ℝ)-(396301145801/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33171/262144 : ℝ) (8293/65536 : ℝ) (396301145801/500000000000 : ℝ) (128431533519/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0392; no trusted numerical premise.
theorem cover8_leaf0392_exp_radius : (998024688619329641/1000000000000000000 : ℝ) ≤ Real.exp ((-33173/2097152 : ℝ)/8) ∧ Real.exp ((-33173/2097152 : ℝ)/8) ≤ (499012344309664821/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33173/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0392_exp_lower : (920113613214587441/1000000000000000000 : ℝ) ≤ Real.exp ((-10657039864203/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657039864203/16000000000000 : ℝ)/8) ≤ (460056806607293721/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657039864203/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0392_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726122307/250000000000 : ℝ) ≤ 4*Real.exp (8293/65536 : ℝ)*Real.exp (-mu (radius 8 (33173/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513726122307/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33173/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0392_exp_radius
  have hrNumeric : (492153165173/500000000000 : ℝ) ≤ Real.exp (-33173/2097152 : ℝ) ∧ Real.exp (-33173/2097152 : ℝ) ≤ (984306330347/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492153165173/500000000000 : ℝ) ≤ (radius 8 (33173/262144 : ℝ)) ∧ (radius 8 (33173/262144 : ℝ)) ≤ (984306330347/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33173/262144 : ℝ)) (492153165173/500000000000 : ℝ) (984306330347/1000000000000 : ℝ) (35293652709/200000000000 : ℝ) (1378658309/7812500000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33173/262144 : ℝ)) (492153165173/500000000000 : ℝ) (984306330347/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33173/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492153165173/500000000000 : ℝ) (984306330347/1000000000000 : ℝ) (992153165173/1000000000000 : ℝ) (496076582587/500000000000 : ℝ) (124015266849/125000000000 : ℝ) (496061067397/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33173/262144 : ℝ)) 1 (992153165173/1000000000000 : ℝ) (496076582587/500000000000 : ℝ) (124015266849/125000000000 : ℝ) (496061067397/500000000000 : ℝ) (496068824991/500000000000 : ℝ) (15502150781/15625000000 : ℝ) (992137649861/1000000000000 : ℝ) (992137649863/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33173/262144 : ℝ)) 2 (496068824991/500000000000 : ℝ) (15502150781/15625000000 : ℝ) (992137649861/1000000000000 : ℝ) (992137649863/1000000000000 : ℝ) (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ) (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33173/262144 : ℝ)) 3 (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ) (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ) (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ) (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33173/262144 : ℝ)) 4 (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ) (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ) (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ) (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33173/262144 : ℝ)) 5 (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ) (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ) (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ) (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33173/262144 : ℝ)) 6 (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ) (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ) (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ) (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33173/262144 : ℝ)) 7 (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ) (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ) (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ) (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33173/262144 : ℝ))) (35293652709/200000000000 : ℝ) (1378658309/7812500000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33173/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35293652709/200000000000 : ℝ) (1378658309/7812500000 : ℝ) (147058532943/250000000000 : ℝ) (9191158309/15625000000 : ℝ) (52510157283/125000000000 : ℝ) (420081258273/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33173/262144 : ℝ))) 1 (147058532943/250000000000 : ℝ) (9191158309/15625000000 : ℝ) (52510157283/125000000000 : ℝ) (420081258273/1000000000000 : ℝ) (252078847509/500000000000 : ℝ) (20166307801/40000000000 : ℝ) (248548855473/500000000000 : ℝ) (248548855477/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33173/262144 : ℝ))) 2 (252078847509/500000000000 : ℝ) (20166307801/40000000000 : ℝ) (248548855473/500000000000 : ℝ) (248548855477/500000000000 : ℝ) (250313851491/500000000000 : ℝ) (50062770299/100000000000 : ℝ) (500615257607/1000000000000 : ℝ) (100123051523/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33173/262144 : ℝ))) 3 (250313851491/500000000000 : ℝ) (50062770299/100000000000 : ℝ) (500615257607/1000000000000 : ℝ) (100123051523/200000000000 : ℝ) (250310740147/500000000000 : ℝ) (500621480303/1000000000000 : ℝ) (100124296051/200000000000 : ℝ) (62577685033/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33173/262144 : ℝ))) 4 (250310740147/500000000000 : ℝ) (500621480303/1000000000000 : ℝ) (100124296051/200000000000 : ℝ) (62577685033/125000000000 : ℝ) (250310740137/500000000000 : ℝ) (125155370071/250000000000 : ℝ) (250310740137/500000000000 : ℝ) (125155370071/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33173/262144 : ℝ))) 5 (250310740137/500000000000 : ℝ) (125155370071/250000000000 : ℝ) (250310740137/500000000000 : ℝ) (125155370071/250000000000 : ℝ) (250310740137/500000000000 : ℝ) (125155370071/250000000000 : ℝ) (250310740137/500000000000 : ℝ) (125155370071/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33173/262144 : ℝ))) 6 (250310740137/500000000000 : ℝ) (125155370071/250000000000 : ℝ) (250310740137/500000000000 : ℝ) (125155370071/250000000000 : ℝ) (250310740137/500000000000 : ℝ) (125155370071/250000000000 : ℝ) (250310740137/500000000000 : ℝ) (125155370071/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33173/262144 : ℝ))) 7 (250310740137/500000000000 : ℝ) (125155370071/250000000000 : ℝ) (250310740137/500000000000 : ℝ) (125155370071/250000000000 : ℝ) (250310740137/500000000000 : ℝ) (125155370071/250000000000 : ℝ) (250310740137/500000000000 : ℝ) (125155370071/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33173/262144 : ℝ)) hmem 8 (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ) (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33173/262144 : ℝ))) hcmem 8 (250310740137/500000000000 : ℝ) (125155370071/250000000000 : ℝ) (250310740137/500000000000 : ℝ) (125155370071/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33173/262144 : ℝ)) (992137649921/1000000000000 : ℝ) (248034412481/250000000000 : ℝ) (250310740137/500000000000 : ℝ) (125155370071/250000000000 : ℝ) (792606129189/1000000000000 : ℝ) (99075766151/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0392_exp_lower
  have heNumeric : (513726122307/250000000000 : ℝ)/4 ≤ Real.exp (-10657039864203/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726122307/250000000000 : ℝ)/4 ≤ Real.exp ((8293/65536 : ℝ)-(99075766151/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8293/65536 : ℝ) (33173/262144 : ℝ) (99075766151/125000000000 : ℝ) (513726122307/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0393; no trusted numerical premise.
theorem cover8_leaf0393_exp_radius : (249506157283106093/250000000000000000 : ℝ) ≤ Real.exp ((-16587/1048576 : ℝ)/8) ∧ Real.exp ((-16587/1048576 : ℝ)/8) ≤ (998024629132424373/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16587/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0393_exp_lower : (920113610589648871/1000000000000000000 : ℝ) ≤ Real.exp ((-42628160917467/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628160917467/64000000000000 : ℝ)/8) ≤ (115014201323706109/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628160917467/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0393_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490444233/100000000000 : ℝ) ≤ 4*Real.exp (33173/262144 : ℝ)*Real.exp (-mu (radius 8 (16587/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (205490444233/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16587/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0393_exp_radius
  have hrNumeric : (984305860993/1000000000000 : ℝ) ≤ Real.exp (-16587/1048576 : ℝ) ∧ Real.exp (-16587/1048576 : ℝ) ≤ (492152930497/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984305860993/1000000000000 : ℝ) ≤ (radius 8 (16587/131072 : ℝ)) ∧ (radius 8 (16587/131072 : ℝ)) ≤ (492152930497/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16587/131072 : ℝ)) (984305860993/1000000000000 : ℝ) (492152930497/500000000000 : ℝ) (176470881487/1000000000000 : ℝ) (176470881493/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16587/131072 : ℝ)) (984305860993/1000000000000 : ℝ) (492152930497/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16587/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984305860993/1000000000000 : ℝ) (492152930497/500000000000 : ℝ) (15502389539/15625000000 : ℝ) (992152930497/1000000000000 : ℝ) (248030474563/250000000000 : ℝ) (496060949127/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16587/131072 : ℝ)) 1 (15502389539/15625000000 : ℝ) (992152930497/1000000000000 : ℝ) (248030474563/250000000000 : ℝ) (496060949127/500000000000 : ℝ) (496068707187/500000000000 : ℝ) (124017176797/125000000000 : ℝ) (248034353563/250000000000 : ℝ) (198427482851/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16587/131072 : ℝ)) 2 (496068707187/500000000000 : ℝ) (124017176797/125000000000 : ℝ) (248034353563/250000000000 : ℝ) (198427482851/200000000000 : ℝ) (992137414313/1000000000000 : ℝ) (248034353579/250000000000 : ℝ) (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16587/131072 : ℝ)) 3 (992137414313/1000000000000 : ℝ) (248034353579/250000000000 : ℝ) (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ) (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ) (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16587/131072 : ℝ)) 4 (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ) (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ) (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ) (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16587/131072 : ℝ)) 5 (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ) (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ) (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ) (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16587/131072 : ℝ)) 6 (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ) (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ) (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ) (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16587/131072 : ℝ)) 7 (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ) (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ) (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ) (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16587/131072 : ℝ))) (176470881487/1000000000000 : ℝ) (176470881493/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16587/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176470881487/1000000000000 : ℝ) (176470881493/1000000000000 : ℝ) (588235440743/1000000000000 : ℝ) (588235440747/1000000000000 : ℝ) (420084374247/1000000000000 : ℝ) (84016874851/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16587/131072 : ℝ))) 1 (588235440743/1000000000000 : ℝ) (588235440747/1000000000000 : ℝ) (420084374247/1000000000000 : ℝ) (84016874851/200000000000 : ℝ) (100831981499/200000000000 : ℝ) (504159907501/1000000000000 : ℝ) (248550053829/500000000000 : ℝ) (248550053833/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16587/131072 : ℝ))) 2 (100831981499/200000000000 : ℝ) (504159907501/1000000000000 : ℝ) (248550053829/500000000000 : ℝ) (248550053833/500000000000 : ℝ) (62578750947/125000000000 : ℝ) (15644687737/31250000000 : ℝ) (125154390727/250000000000 : ℝ) (125154390729/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16587/131072 : ℝ))) 3 (62578750947/125000000000 : ℝ) (15644687737/31250000000 : ℝ) (125154390727/250000000000 : ℝ) (125154390729/250000000000 : ℝ) (250311892621/500000000000 : ℝ) (2002495141/4000000000 : ℝ) (500623785203/1000000000000 : ℝ) (125155946303/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16587/131072 : ℝ))) 4 (250311892621/500000000000 : ℝ) (2002495141/4000000000 : ℝ) (500623785203/1000000000000 : ℝ) (125155946303/250000000000 : ℝ) (250311892611/500000000000 : ℝ) (500623785231/1000000000000 : ℝ) (250311892611/500000000000 : ℝ) (500623785231/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16587/131072 : ℝ))) 5 (250311892611/500000000000 : ℝ) (500623785231/1000000000000 : ℝ) (250311892611/500000000000 : ℝ) (500623785231/1000000000000 : ℝ) (250311892611/500000000000 : ℝ) (500623785231/1000000000000 : ℝ) (250311892611/500000000000 : ℝ) (500623785231/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16587/131072 : ℝ))) 6 (250311892611/500000000000 : ℝ) (500623785231/1000000000000 : ℝ) (250311892611/500000000000 : ℝ) (500623785231/1000000000000 : ℝ) (250311892611/500000000000 : ℝ) (500623785231/1000000000000 : ℝ) (250311892611/500000000000 : ℝ) (500623785231/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16587/131072 : ℝ))) 7 (250311892611/500000000000 : ℝ) (500623785231/1000000000000 : ℝ) (250311892611/500000000000 : ℝ) (500623785231/1000000000000 : ℝ) (250311892611/500000000000 : ℝ) (500623785231/1000000000000 : ℝ) (250311892611/500000000000 : ℝ) (500623785231/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16587/131072 : ℝ)) hmem 8 (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ) (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16587/131072 : ℝ))) hcmem 8 (250311892611/500000000000 : ℝ) (500623785231/1000000000000 : ℝ) (250311892611/500000000000 : ℝ) (500623785231/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16587/131072 : ℝ)) (124017176789/125000000000 : ℝ) (248034353579/250000000000 : ℝ) (250311892611/500000000000 : ℝ) (500623785231/1000000000000 : ℝ) (79260996671/100000000000 : ℝ) (99076245841/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0393_exp_lower
  have heNumeric : (205490444233/100000000000 : ℝ)/4 ≤ Real.exp (-42628160917467/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490444233/100000000000 : ℝ)/4 ≤ Real.exp ((33173/262144 : ℝ)-(99076245841/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33173/262144 : ℝ) (16587/131072 : ℝ) (99076245841/125000000000 : ℝ) (205490444233/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0394; no trusted numerical premise.
theorem cover8_leaf0394_exp_radius : (124753071205690331/125000000000000000 : ℝ) ≤ Real.exp ((-33175/2097152 : ℝ)/8) ∧ Real.exp ((-33175/2097152 : ℝ)/8) ≤ (998024569645522649/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33175/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0394_exp_lower : (460056803986265637/500000000000000000 : ℝ) ≤ Real.exp ((-4262816237377/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262816237377/6400000000000 : ℝ)/8) ≤ (36804544318901251/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262816237377/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0394_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904395571/1000000000000 : ℝ) ≤ 4*Real.exp (16587/131072 : ℝ)*Real.exp (-mu (radius 8 (33175/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904395571/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33175/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0394_exp_radius
  have hrNumeric : (984305391639/1000000000000 : ℝ) ≤ Real.exp (-33175/2097152 : ℝ) ∧ Real.exp (-33175/2097152 : ℝ) ≤ (24607634791/25000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984305391639/1000000000000 : ℝ) ≤ (radius 8 (33175/262144 : ℝ)) ∧ (radius 8 (33175/262144 : ℝ)) ≤ (24607634791/25000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33175/262144 : ℝ)) (984305391639/1000000000000 : ℝ) (24607634791/25000000000 : ℝ) (88236749697/500000000000 : ℝ) (882367497/5000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33175/262144 : ℝ)) (984305391639/1000000000000 : ℝ) (24607634791/25000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33175/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984305391639/1000000000000 : ℝ) (24607634791/25000000000 : ℝ) (992152695819/1000000000000 : ℝ) (49607634791/50000000000 : ℝ) (62007603857/62500000000 : ℝ) (992121661713/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33175/262144 : ℝ)) 1 (992152695819/1000000000000 : ℝ) (49607634791/50000000000 : ℝ) (62007603857/62500000000 : ℝ) (992121661713/1000000000000 : ℝ) (198427435753/200000000000 : ℝ) (992137178767/1000000000000 : ℝ) (248034294661/250000000000 : ℝ) (496068589323/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33175/262144 : ℝ)) 2 (198427435753/200000000000 : ℝ) (992137178767/1000000000000 : ℝ) (248034294661/250000000000 : ℝ) (496068589323/500000000000 : ℝ) (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ) (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33175/262144 : ℝ)) 3 (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ) (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ) (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ) (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33175/262144 : ℝ)) 4 (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ) (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ) (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ) (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33175/262144 : ℝ)) 5 (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ) (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ) (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ) (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33175/262144 : ℝ)) 6 (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ) (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ) (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ) (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33175/262144 : ℝ)) 7 (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ) (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ) (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ) (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33175/262144 : ℝ))) (88236749697/500000000000 : ℝ) (882367497/5000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33175/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88236749697/500000000000 : ℝ) (882367497/5000000000 : ℝ) (588236749697/1000000000000 : ℝ) (5882367497/10000000000 : ℝ) (210043745083/500000000000 : ℝ) (210043745087/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33175/262144 : ℝ))) 1 (588236749697/1000000000000 : ℝ) (5882367497/10000000000 : ℝ) (210043745083/500000000000 : ℝ) (210043745087/500000000000 : ℝ) (504162119931/1000000000000 : ℝ) (504162119937/1000000000000 : ℝ) (248551252161/500000000000 : ℝ) (497102504329/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33175/262144 : ℝ))) 2 (504162119931/1000000000000 : ℝ) (504162119937/1000000000000 : ℝ) (248551252161/500000000000 : ℝ) (497102504329/1000000000000 : ℝ) (250316156063/500000000000 : ℝ) (500632312133/1000000000000 : ℝ) (100123973633/200000000000 : ℝ) (125154967043/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33175/262144 : ℝ))) 3 (250316156063/500000000000 : ℝ) (500632312133/1000000000000 : ℝ) (100123973633/200000000000 : ℝ) (125154967043/250000000000 : ℝ) (100125218029/200000000000 : ℝ) (500626090153/1000000000000 : ℝ) (250313045053/500000000000 : ℝ) (250313045057/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33175/262144 : ℝ))) 4 (100125218029/200000000000 : ℝ) (500626090153/1000000000000 : ℝ) (250313045053/500000000000 : ℝ) (250313045057/500000000000 : ℝ) (4005008721/8000000000 : ℝ) (250313045067/500000000000 : ℝ) (4005008721/8000000000 : ℝ) (250313045067/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33175/262144 : ℝ))) 5 (4005008721/8000000000 : ℝ) (250313045067/500000000000 : ℝ) (4005008721/8000000000 : ℝ) (250313045067/500000000000 : ℝ) (4005008721/8000000000 : ℝ) (250313045067/500000000000 : ℝ) (4005008721/8000000000 : ℝ) (250313045067/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33175/262144 : ℝ))) 6 (4005008721/8000000000 : ℝ) (250313045067/500000000000 : ℝ) (4005008721/8000000000 : ℝ) (250313045067/500000000000 : ℝ) (4005008721/8000000000 : ℝ) (250313045067/500000000000 : ℝ) (4005008721/8000000000 : ℝ) (250313045067/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33175/262144 : ℝ))) 7 (4005008721/8000000000 : ℝ) (250313045067/500000000000 : ℝ) (4005008721/8000000000 : ℝ) (250313045067/500000000000 : ℝ) (4005008721/8000000000 : ℝ) (250313045067/500000000000 : ℝ) (4005008721/8000000000 : ℝ) (250313045067/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33175/262144 : ℝ)) hmem 8 (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ) (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33175/262144 : ℝ))) hcmem 8 (4005008721/8000000000 : ℝ) (250313045067/500000000000 : ℝ) (4005008721/8000000000 : ℝ) (250313045067/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33175/262144 : ℝ)) (62008573669/62500000000 : ℝ) (992137178707/1000000000000 : ℝ) (4005008721/8000000000 : ℝ) (250313045067/500000000000 : ℝ) (396306902081/500000000000 : ℝ) (39630690209/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0394_exp_lower
  have heNumeric : (2054904395571/1000000000000 : ℝ)/4 ≤ Real.exp (-4262816237377/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904395571/1000000000000 : ℝ)/4 ≤ Real.exp ((16587/131072 : ℝ)-(39630690209/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16587/131072 : ℝ) (33175/262144 : ℝ) (39630690209/50000000000 : ℝ) (2054904395571/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0395; no trusted numerical premise.
theorem cover8_leaf0395_exp_radius : (99802451015862447/100000000000000000 : ℝ) ≤ Real.exp ((-4147/262144 : ℝ)/8) ∧ Real.exp ((-4147/262144 : ℝ)/8) ≤ (998024510158624471/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4147/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0395_exp_lower : (460056802682652453/500000000000000000 : ℝ) ≤ Real.exp ((-42628163824569/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628163824569/64000000000000 : ℝ)/8) ≤ (920113605365304907/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628163824569/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0395_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904348989/1000000000000 : ℝ) ≤ 4*Real.exp (33175/262144 : ℝ)*Real.exp (-mu (radius 8 (4147/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904348989/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4147/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0395_exp_radius
  have hrNumeric : (492152461143/500000000000 : ℝ) ≤ Real.exp (-4147/262144 : ℝ) ∧ Real.exp (-4147/262144 : ℝ) ≤ (984304922287/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492152461143/500000000000 : ℝ) ≤ (radius 8 (4147/32768 : ℝ)) ∧ (radius 8 (4147/32768 : ℝ)) ≤ (984304922287/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4147/32768 : ℝ)) (492152461143/500000000000 : ℝ) (984304922287/1000000000000 : ℝ) (35295223451/200000000000 : ℝ) (88238058631/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4147/32768 : ℝ)) (492152461143/500000000000 : ℝ) (984304922287/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4147/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492152461143/500000000000 : ℝ) (984304922287/1000000000000 : ℝ) (992152461143/1000000000000 : ℝ) (124019057643/125000000000 : ℝ) (248030356293/250000000000 : ℝ) (992121425173/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4147/32768 : ℝ)) 1 (992152461143/1000000000000 : ℝ) (124019057643/125000000000 : ℝ) (248030356293/250000000000 : ℝ) (992121425173/1000000000000 : ℝ) (992136943157/1000000000000 : ℝ) (992136943159/1000000000000 : ℝ) (248034235759/250000000000 : ℝ) (496068471519/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4147/32768 : ℝ)) 2 (992136943157/1000000000000 : ℝ) (992136943159/1000000000000 : ℝ) (248034235759/250000000000 : ℝ) (496068471519/500000000000 : ℝ) (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ) (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4147/32768 : ℝ)) 3 (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ) (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ) (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ) (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4147/32768 : ℝ)) 4 (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ) (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ) (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ) (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4147/32768 : ℝ)) 5 (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ) (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ) (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ) (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4147/32768 : ℝ)) 6 (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ) (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ) (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ) (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4147/32768 : ℝ)) 7 (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ) (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ) (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ) (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4147/32768 : ℝ))) (35295223451/200000000000 : ℝ) (88238058631/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4147/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35295223451/200000000000 : ℝ) (88238058631/500000000000 : ℝ) (588238058627/1000000000000 : ℝ) (588238058631/1000000000000 : ℝ) (210045303003/500000000000 : ℝ) (84018121203/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4147/32768 : ℝ))) 1 (588238058627/1000000000000 : ℝ) (588238058631/1000000000000 : ℝ) (210045303003/500000000000 : ℝ) (84018121203/200000000000 : ℝ) (126041083079/250000000000 : ℝ) (504164332323/1000000000000 : ℝ) (19884196037/40000000000 : ℝ) (497104900933/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4147/32768 : ℝ))) 2 (126041083079/250000000000 : ℝ) (504164332323/1000000000000 : ℝ) (19884196037/40000000000 : ℝ) (497104900933/1000000000000 : ℝ) (25031730831/50000000000 : ℝ) (125158654157/250000000000 : ℝ) (250311086683/500000000000 : ℝ) (250311086687/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4147/32768 : ℝ))) 3 (25031730831/50000000000 : ℝ) (125158654157/250000000000 : ℝ) (250311086683/500000000000 : ℝ) (250311086687/500000000000 : ℝ) (500628394993/1000000000000 : ℝ) (500628395001/1000000000000 : ℝ) (250314197477/500000000000 : ℝ) (500628394963/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4147/32768 : ℝ))) 4 (500628394993/1000000000000 : ℝ) (500628395001/1000000000000 : ℝ) (250314197477/500000000000 : ℝ) (500628394963/1000000000000 : ℝ) (500628394973/1000000000000 : ℝ) (250314197491/500000000000 : ℝ) (500628394973/1000000000000 : ℝ) (250314197491/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4147/32768 : ℝ))) 5 (500628394973/1000000000000 : ℝ) (250314197491/500000000000 : ℝ) (500628394973/1000000000000 : ℝ) (250314197491/500000000000 : ℝ) (500628394973/1000000000000 : ℝ) (250314197491/500000000000 : ℝ) (500628394973/1000000000000 : ℝ) (250314197491/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4147/32768 : ℝ))) 6 (500628394973/1000000000000 : ℝ) (250314197491/500000000000 : ℝ) (500628394973/1000000000000 : ℝ) (250314197491/500000000000 : ℝ) (500628394973/1000000000000 : ℝ) (250314197491/500000000000 : ℝ) (500628394973/1000000000000 : ℝ) (250314197491/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4147/32768 : ℝ))) 7 (500628394973/1000000000000 : ℝ) (250314197491/500000000000 : ℝ) (500628394973/1000000000000 : ℝ) (250314197491/500000000000 : ℝ) (500628394973/1000000000000 : ℝ) (250314197491/500000000000 : ℝ) (500628394973/1000000000000 : ℝ) (250314197491/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4147/32768 : ℝ)) hmem 8 (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ) (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4147/32768 : ℝ))) hcmem 8 (500628394973/1000000000000 : ℝ) (250314197491/500000000000 : ℝ) (500628394973/1000000000000 : ℝ) (250314197491/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4147/32768 : ℝ)) (124017117887/125000000000 : ℝ) (992136943099/1000000000000 : ℝ) (500628394973/1000000000000 : ℝ) (250314197491/500000000000 : ℝ) (99077205191/125000000000 : ℝ) (396308820773/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0395_exp_lower
  have heNumeric : (2054904348989/1000000000000 : ℝ)/4 ≤ Real.exp (-42628163824569/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904348989/1000000000000 : ℝ)/4 ≤ Real.exp ((33175/262144 : ℝ)-(396308820773/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33175/262144 : ℝ) (4147/32768 : ℝ) (396308820773/500000000000 : ℝ) (2054904348989/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0396; no trusted numerical premise.
theorem cover8_leaf0396_exp_radius : (499012225335864919/500000000000000000 : ℝ) ≤ Real.exp ((-33177/2097152 : ℝ)/8) ∧ Real.exp ((-33177/2097152 : ℝ)/8) ≤ (998024450671729839/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33177/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0396_exp_lower : (460056801383237291/500000000000000000 : ℝ) ≤ Real.exp ((-5328520658837/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328520658837/8000000000000 : ℝ)/8) ≤ (920113602766474583/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328520658837/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0396_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904302557/1000000000000 : ℝ) ≤ 4*Real.exp (4147/32768 : ℝ)*Real.exp (-mu (radius 8 (33177/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904302557/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33177/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0396_exp_radius
  have hrNumeric : (984304452933/1000000000000 : ℝ) ≤ Real.exp (-33177/2097152 : ℝ) ∧ Real.exp (-33177/2097152 : ℝ) ≤ (492152226467/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984304452933/1000000000000 : ℝ) ≤ (radius 8 (33177/262144 : ℝ)) ∧ (radius 8 (33177/262144 : ℝ)) ≤ (492152226467/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33177/262144 : ℝ)) (984304452933/1000000000000 : ℝ) (492152226467/500000000000 : ℝ) (44119683769/250000000000 : ℝ) (176478735083/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33177/262144 : ℝ)) (984304452933/1000000000000 : ℝ) (492152226467/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33177/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984304452933/1000000000000 : ℝ) (492152226467/500000000000 : ℝ) (496076113233/500000000000 : ℝ) (992152226467/1000000000000 : ℝ) (124015148579/125000000000 : ℝ) (992121188633/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33177/262144 : ℝ)) 1 (496076113233/500000000000 : ℝ) (992152226467/1000000000000 : ℝ) (124015148579/125000000000 : ℝ) (992121188633/1000000000000 : ℝ) (992136707549/1000000000000 : ℝ) (19842734151/20000000000 : ℝ) (992136707427/1000000000000 : ℝ) (992136707429/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33177/262144 : ℝ)) 2 (992136707549/1000000000000 : ℝ) (19842734151/20000000000 : ℝ) (992136707427/1000000000000 : ℝ) (992136707429/1000000000000 : ℝ) (31004272109/31250000000 : ℝ) (99213670749/100000000000 : ℝ) (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33177/262144 : ℝ)) 3 (31004272109/31250000000 : ℝ) (99213670749/100000000000 : ℝ) (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ) (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ) (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33177/262144 : ℝ)) 4 (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ) (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ) (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ) (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33177/262144 : ℝ)) 5 (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ) (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ) (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ) (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33177/262144 : ℝ)) 6 (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ) (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ) (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ) (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33177/262144 : ℝ)) 7 (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ) (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ) (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ) (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33177/262144 : ℝ))) (44119683769/250000000000 : ℝ) (176478735083/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33177/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44119683769/250000000000 : ℝ) (176478735083/1000000000000 : ℝ) (294119683769/500000000000 : ℝ) (294119683771/500000000000 : ℝ) (26255857611/62500000000 : ℝ) (84018744357/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33177/262144 : ℝ))) 1 (294119683769/500000000000 : ℝ) (294119683771/500000000000 : ℝ) (26255857611/62500000000 : ℝ) (84018744357/200000000000 : ℝ) (504166544657/1000000000000 : ℝ) (63020818083/125000000000 : ℝ) (124276824369/250000000000 : ℝ) (124276824371/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33177/262144 : ℝ))) 2 (504166544657/1000000000000 : ℝ) (63020818083/125000000000 : ℝ) (124276824369/250000000000 : ℝ) (124276824371/250000000000 : ℝ) (250318460533/500000000000 : ℝ) (250318460537/500000000000 : ℝ) (250312239259/500000000000 : ℝ) (500624478527/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33177/262144 : ℝ))) 3 (250318460533/500000000000 : ℝ) (250318460537/500000000000 : ℝ) (250312239259/500000000000 : ℝ) (500624478527/1000000000000 : ℝ) (31289418737/62500000000 : ℝ) (500630699801/1000000000000 : ℝ) (500630699753/1000000000000 : ℝ) (250315349881/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33177/262144 : ℝ))) 4 (31289418737/62500000000 : ℝ) (500630699801/1000000000000 : ℝ) (500630699753/1000000000000 : ℝ) (250315349881/500000000000 : ℝ) (125157674943/250000000000 : ℝ) (250315349891/500000000000 : ℝ) (125157674943/250000000000 : ℝ) (250315349891/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33177/262144 : ℝ))) 5 (125157674943/250000000000 : ℝ) (250315349891/500000000000 : ℝ) (125157674943/250000000000 : ℝ) (250315349891/500000000000 : ℝ) (125157674943/250000000000 : ℝ) (250315349891/500000000000 : ℝ) (125157674943/250000000000 : ℝ) (250315349891/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33177/262144 : ℝ))) 6 (125157674943/250000000000 : ℝ) (250315349891/500000000000 : ℝ) (125157674943/250000000000 : ℝ) (250315349891/500000000000 : ℝ) (125157674943/250000000000 : ℝ) (250315349891/500000000000 : ℝ) (125157674943/250000000000 : ℝ) (250315349891/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33177/262144 : ℝ))) 7 (125157674943/250000000000 : ℝ) (250315349891/500000000000 : ℝ) (125157674943/250000000000 : ℝ) (250315349891/500000000000 : ℝ) (125157674943/250000000000 : ℝ) (250315349891/500000000000 : ℝ) (125157674943/250000000000 : ℝ) (250315349891/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33177/262144 : ℝ)) hmem 8 (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ) (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33177/262144 : ℝ))) hcmem 8 (125157674943/250000000000 : ℝ) (250315349891/500000000000 : ℝ) (125157674943/250000000000 : ℝ) (250315349891/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33177/262144 : ℝ)) (992136707487/1000000000000 : ℝ) (99213670749/100000000000 : ℝ) (125157674943/250000000000 : ℝ) (250315349891/500000000000 : ℝ) (39631073941/50000000000 : ℝ) (792621478839/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0396_exp_lower
  have heNumeric : (2054904302557/1000000000000 : ℝ)/4 ≤ Real.exp (-5328520658837/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904302557/1000000000000 : ℝ)/4 ≤ Real.exp ((4147/32768 : ℝ)-(792621478839/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4147/32768 : ℝ) (33177/262144 : ℝ) (792621478839/1000000000000 : ℝ) (2054904302557/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0397; no trusted numerical premise.
theorem cover8_leaf0397_exp_radius : (998024391184838751/1000000000000000000 : ℝ) ≤ Real.exp ((-16589/1048576 : ℝ)/8) ∧ Real.exp ((-16589/1048576 : ℝ)/8) ≤ (31188262224526211/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16589/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0397_exp_lower : (184022720035392083/200000000000000000 : ℝ) ≤ Real.exp ((-42628166711639/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628166711639/64000000000000 : ℝ)/8) ≤ (28753550005530013/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628166711639/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0397_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904256291/1000000000000 : ℝ) ≤ 4*Real.exp (33177/262144 : ℝ)*Real.exp (-mu (radius 8 (16589/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904256291/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16589/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0397_exp_radius
  have hrNumeric : (49215199179/50000000000 : ℝ) ≤ Real.exp (-16589/1048576 : ℝ) ∧ Real.exp (-16589/1048576 : ℝ) ≤ (984303983581/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49215199179/50000000000 : ℝ) ≤ (radius 8 (16589/131072 : ℝ)) ∧ (radius 8 (16589/131072 : ℝ)) ≤ (984303983581/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16589/131072 : ℝ)) (49215199179/50000000000 : ℝ) (984303983581/1000000000000 : ℝ) (176481352857/1000000000000 : ℝ) (5515042277/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16589/131072 : ℝ)) (49215199179/50000000000 : ℝ) (984303983581/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16589/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49215199179/50000000000 : ℝ) (984303983581/1000000000000 : ℝ) (99215199179/100000000000 : ℝ) (992151991791/1000000000000 : ℝ) (248030238023/250000000000 : ℝ) (992120952093/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16589/131072 : ℝ)) 1 (99215199179/100000000000 : ℝ) (992151991791/1000000000000 : ℝ) (248030238023/250000000000 : ℝ) (992120952093/1000000000000 : ℝ) (992136471941/1000000000000 : ℝ) (496068235971/500000000000 : ℝ) (992136471819/1000000000000 : ℝ) (992136471821/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16589/131072 : ℝ)) 2 (992136471941/1000000000000 : ℝ) (496068235971/500000000000 : ℝ) (992136471819/1000000000000 : ℝ) (992136471821/1000000000000 : ℝ) (24803411797/25000000000 : ℝ) (496068235941/500000000000 : ℝ) (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16589/131072 : ℝ)) 3 (24803411797/25000000000 : ℝ) (496068235941/500000000000 : ℝ) (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ) (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ) (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16589/131072 : ℝ)) 4 (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ) (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ) (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ) (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16589/131072 : ℝ)) 5 (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ) (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ) (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ) (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16589/131072 : ℝ)) 6 (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ) (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ) (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ) (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16589/131072 : ℝ)) 7 (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ) (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ) (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ) (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16589/131072 : ℝ))) (176481352857/1000000000000 : ℝ) (5515042277/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16589/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176481352857/1000000000000 : ℝ) (5515042277/31250000000 : ℝ) (147060169107/250000000000 : ℝ) (36765042277/62500000000 : ℝ) (16803873499/40000000000 : ℝ) (105024209371/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16589/131072 : ℝ))) 1 (147060169107/250000000000 : ℝ) (36765042277/62500000000 : ℝ) (16803873499/40000000000 : ℝ) (105024209371/250000000000 : ℝ) (504168756951/1000000000000 : ℝ) (252084378479/500000000000 : ℝ) (124277423493/250000000000 : ℝ) (24855484699/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16589/131072 : ℝ))) 2 (504168756951/1000000000000 : ℝ) (252084378479/500000000000 : ℝ) (124277423493/250000000000 : ℝ) (24855484699/50000000000 : ℝ) (500639225461/1000000000000 : ℝ) (500639225469/1000000000000 : ℝ) (25031339181/50000000000 : ℝ) (125156695907/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16589/131072 : ℝ))) 3 (500639225461/1000000000000 : ℝ) (500639225469/1000000000000 : ℝ) (25031339181/50000000000 : ℝ) (125156695907/250000000000 : ℝ) (25031650227/50000000000 : ℝ) (500633004549/1000000000000 : ℝ) (500633004501/1000000000000 : ℝ) (50063300451/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16589/131072 : ℝ))) 4 (25031650227/50000000000 : ℝ) (500633004549/1000000000000 : ℝ) (500633004501/1000000000000 : ℝ) (50063300451/100000000000 : ℝ) (12515825113/25000000000 : ℝ) (50063300453/100000000000 : ℝ) (12515825113/25000000000 : ℝ) (50063300453/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16589/131072 : ℝ))) 5 (12515825113/25000000000 : ℝ) (50063300453/100000000000 : ℝ) (12515825113/25000000000 : ℝ) (50063300453/100000000000 : ℝ) (12515825113/25000000000 : ℝ) (50063300453/100000000000 : ℝ) (12515825113/25000000000 : ℝ) (50063300453/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16589/131072 : ℝ))) 6 (12515825113/25000000000 : ℝ) (50063300453/100000000000 : ℝ) (12515825113/25000000000 : ℝ) (50063300453/100000000000 : ℝ) (12515825113/25000000000 : ℝ) (50063300453/100000000000 : ℝ) (12515825113/25000000000 : ℝ) (50063300453/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16589/131072 : ℝ))) 7 (12515825113/25000000000 : ℝ) (50063300453/100000000000 : ℝ) (12515825113/25000000000 : ℝ) (50063300453/100000000000 : ℝ) (12515825113/25000000000 : ℝ) (50063300453/100000000000 : ℝ) (12515825113/25000000000 : ℝ) (50063300453/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16589/131072 : ℝ)) hmem 8 (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ) (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16589/131072 : ℝ))) hcmem 8 (12515825113/25000000000 : ℝ) (50063300453/100000000000 : ℝ) (12515825113/25000000000 : ℝ) (50063300453/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16589/131072 : ℝ)) (992136471879/1000000000000 : ℝ) (496068235941/500000000000 : ℝ) (12515825113/25000000000 : ℝ) (50063300453/100000000000 : ℝ) (792625316031/1000000000000 : ℝ) (792625316051/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0397_exp_lower
  have heNumeric : (2054904256291/1000000000000 : ℝ)/4 ≤ Real.exp (-42628166711639/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904256291/1000000000000 : ℝ)/4 ≤ Real.exp ((33177/262144 : ℝ)-(792625316051/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33177/262144 : ℝ) (16589/131072 : ℝ) (792625316051/1000000000000 : ℝ) (2054904256291/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0398; no trusted numerical premise.
theorem cover8_leaf0398_exp_radius : (99802433169795121/100000000000000000 : ℝ) ≤ Real.exp ((-33179/2097152 : ℝ)/8) ∧ Real.exp ((-33179/2097152 : ℝ)/8) ≤ (998024331697951211/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33179/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0398_exp_lower : (920113597595957307/1000000000000000000 : ℝ) ≤ Real.exp ((-21314084073923/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314084073923/32000000000000 : ℝ)/8) ≤ (230028399398989327/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314084073923/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0398_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452105089/500000000000 : ℝ) ≤ 4*Real.exp (16589/131072 : ℝ)*Real.exp (-mu (radius 8 (33179/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452105089/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33179/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0398_exp_radius
  have hrNumeric : (984303514227/1000000000000 : ℝ) ≤ Real.exp (-33179/2097152 : ℝ) ∧ Real.exp (-33179/2097152 : ℝ) ≤ (246075878557/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984303514227/1000000000000 : ℝ) ≤ (radius 8 (33179/262144 : ℝ)) ∧ (radius 8 (33179/262144 : ℝ)) ≤ (246075878557/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33179/262144 : ℝ)) (984303514227/1000000000000 : ℝ) (246075878557/250000000000 : ℝ) (176483970599/1000000000000 : ℝ) (35296794121/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33179/262144 : ℝ)) (984303514227/1000000000000 : ℝ) (246075878557/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33179/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984303514227/1000000000000 : ℝ) (246075878557/250000000000 : ℝ) (992151757113/1000000000000 : ℝ) (496075878557/500000000000 : ℝ) (992120715551/1000000000000 : ℝ) (992120715553/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33179/262144 : ℝ)) 1 (992151757113/1000000000000 : ℝ) (496075878557/500000000000 : ℝ) (992120715551/1000000000000 : ℝ) (992120715553/1000000000000 : ℝ) (248034059083/250000000000 : ℝ) (496068118167/500000000000 : ℝ) (99213623621/100000000000 : ℝ) (992136236213/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33179/262144 : ℝ)) 2 (248034059083/250000000000 : ℝ) (496068118167/500000000000 : ℝ) (99213623621/100000000000 : ℝ) (992136236213/1000000000000 : ℝ) (992136236271/1000000000000 : ℝ) (496068118137/500000000000 : ℝ) (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33179/262144 : ℝ)) 3 (992136236271/1000000000000 : ℝ) (496068118137/500000000000 : ℝ) (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ) (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ) (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33179/262144 : ℝ)) 4 (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ) (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ) (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ) (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33179/262144 : ℝ)) 5 (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ) (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ) (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ) (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33179/262144 : ℝ)) 6 (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ) (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ) (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ) (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33179/262144 : ℝ)) 7 (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ) (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ) (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ) (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33179/262144 : ℝ))) (176483970599/1000000000000 : ℝ) (35296794121/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33179/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176483970599/1000000000000 : ℝ) (35296794121/200000000000 : ℝ) (588241985299/1000000000000 : ℝ) (588241985303/1000000000000 : ℝ) (84019990621/200000000000 : ℝ) (420099953113/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33179/262144 : ℝ))) 1 (588241985299/1000000000000 : ℝ) (588241985303/1000000000000 : ℝ) (84019990621/200000000000 : ℝ) (420099953113/1000000000000 : ℝ) (252085484601/500000000000 : ℝ) (63021371151/125000000000 : ℝ) (31069505651/62500000000 : ℝ) (62139011303/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33179/262144 : ℝ))) 2 (252085484601/500000000000 : ℝ) (63021371151/125000000000 : ℝ) (31069505651/62500000000 : ℝ) (62139011303/125000000000 : ℝ) (500641529809/1000000000000 : ℝ) (62580191227/125000000000 : ℝ) (250314544337/500000000000 : ℝ) (250314544341/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33179/262144 : ℝ))) 3 (500641529809/1000000000000 : ℝ) (62580191227/125000000000 : ℝ) (250314544337/500000000000 : ℝ) (250314544341/500000000000 : ℝ) (500635309241/1000000000000 : ℝ) (500635309249/1000000000000 : ℝ) (250317654601/500000000000 : ℝ) (500635309211/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33179/262144 : ℝ))) 4 (500635309241/1000000000000 : ℝ) (500635309249/1000000000000 : ℝ) (250317654601/500000000000 : ℝ) (500635309211/1000000000000 : ℝ) (500635309221/1000000000000 : ℝ) (50063530923/100000000000 : ℝ) (500635309221/1000000000000 : ℝ) (50063530923/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33179/262144 : ℝ))) 5 (500635309221/1000000000000 : ℝ) (50063530923/100000000000 : ℝ) (500635309221/1000000000000 : ℝ) (50063530923/100000000000 : ℝ) (500635309221/1000000000000 : ℝ) (50063530923/100000000000 : ℝ) (500635309221/1000000000000 : ℝ) (50063530923/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33179/262144 : ℝ))) 6 (500635309221/1000000000000 : ℝ) (50063530923/100000000000 : ℝ) (500635309221/1000000000000 : ℝ) (50063530923/100000000000 : ℝ) (500635309221/1000000000000 : ℝ) (50063530923/100000000000 : ℝ) (500635309221/1000000000000 : ℝ) (50063530923/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33179/262144 : ℝ))) 7 (500635309221/1000000000000 : ℝ) (50063530923/100000000000 : ℝ) (500635309221/1000000000000 : ℝ) (50063530923/100000000000 : ℝ) (500635309221/1000000000000 : ℝ) (50063530923/100000000000 : ℝ) (500635309221/1000000000000 : ℝ) (50063530923/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33179/262144 : ℝ)) hmem 8 (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ) (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33179/262144 : ℝ))) hcmem 8 (500635309221/1000000000000 : ℝ) (50063530923/100000000000 : ℝ) (500635309221/1000000000000 : ℝ) (50063530923/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33179/262144 : ℝ)) (99213623627/100000000000 : ℝ) (496068118137/500000000000 : ℝ) (500635309221/1000000000000 : ℝ) (50063530923/100000000000 : ℝ) (792629153171/1000000000000 : ℝ) (792629153189/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0398_exp_lower
  have heNumeric : (1027452105089/500000000000 : ℝ)/4 ≤ Real.exp (-21314084073923/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452105089/500000000000 : ℝ)/4 ≤ Real.exp ((16589/131072 : ℝ)-(792629153189/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16589/131072 : ℝ) (33179/262144 : ℝ) (792629153189/1000000000000 : ℝ) (1027452105089/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0399; no trusted numerical premise.
theorem cover8_leaf0399_exp_radius : (199604854442213443/200000000000000000 : ℝ) ≤ Real.exp ((-8295/524288 : ℝ)/8) ∧ Real.exp ((-8295/524288 : ℝ)/8) ≤ (62376517013191701/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8295/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0399_exp_lower : (920113595024615399/1000000000000000000 : ℝ) ≤ Real.exp ((-42628169578677/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628169578677/64000000000000 : ℝ)/8) ≤ (4600567975123077/5000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628169578677/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0399_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904164237/1000000000000 : ℝ) ≤ 4*Real.exp (33179/262144 : ℝ)*Real.exp (-mu (radius 8 (8295/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904164237/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8295/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0399_exp_radius
  have hrNumeric : (7874424359/8000000000 : ℝ) ≤ Real.exp (-8295/524288 : ℝ) ∧ Real.exp (-8295/524288 : ℝ) ≤ (246075761219/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (7874424359/8000000000 : ℝ) ≤ (radius 8 (8295/65536 : ℝ)) ∧ (radius 8 (8295/65536 : ℝ)) ≤ (246075761219/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8295/65536 : ℝ)) (7874424359/8000000000 : ℝ) (246075761219/250000000000 : ℝ) (88243294147/500000000000 : ℝ) (176486588301/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8295/65536 : ℝ)) (7874424359/8000000000 : ℝ) (246075761219/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8295/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (7874424359/8000000000 : ℝ) (246075761219/250000000000 : ℝ) (992151522437/1000000000000 : ℝ) (496075761219/500000000000 : ℝ) (992120479011/1000000000000 : ℝ) (992120479013/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8295/65536 : ℝ)) 1 (992151522437/1000000000000 : ℝ) (496075761219/500000000000 : ℝ) (992120479011/1000000000000 : ℝ) (992120479013/1000000000000 : ℝ) (248034000181/250000000000 : ℝ) (496068000363/500000000000 : ℝ) (496068000301/500000000000 : ℝ) (198427200121/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8295/65536 : ℝ)) 2 (248034000181/250000000000 : ℝ) (496068000363/500000000000 : ℝ) (496068000301/500000000000 : ℝ) (198427200121/200000000000 : ℝ) (992136000663/1000000000000 : ℝ) (496068000333/500000000000 : ℝ) (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8295/65536 : ℝ)) 3 (992136000663/1000000000000 : ℝ) (496068000333/500000000000 : ℝ) (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ) (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ) (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8295/65536 : ℝ)) 4 (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ) (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ) (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ) (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8295/65536 : ℝ)) 5 (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ) (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ) (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ) (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8295/65536 : ℝ)) 6 (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ) (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ) (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ) (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8295/65536 : ℝ)) 7 (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ) (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ) (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ) (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8295/65536 : ℝ))) (88243294147/500000000000 : ℝ) (176486588301/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8295/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88243294147/500000000000 : ℝ) (176486588301/1000000000000 : ℝ) (588243294147/1000000000000 : ℝ) (588243294151/1000000000000 : ℝ) (84020613731/200000000000 : ℝ) (84020613733/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8295/65536 : ℝ))) 1 (588243294147/1000000000000 : ℝ) (588243294151/1000000000000 : ℝ) (84020613731/200000000000 : ℝ) (84020613733/200000000000 : ℝ) (504173181401/1000000000000 : ℝ) (15755411919/31250000000 : ℝ) (1242786217/2500000000 : ℝ) (497114486809/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8295/65536 : ℝ))) 2 (504173181401/1000000000000 : ℝ) (15755411919/31250000000 : ℝ) (1242786217/2500000000 : ℝ) (497114486809/1000000000000 : ℝ) (5006438341/10000000000 : ℝ) (500643834109/1000000000000 : ℝ) (62578924209/125000000000 : ℝ) (500631393681/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8295/65536 : ℝ))) 3 (5006438341/10000000000 : ℝ) (500643834109/1000000000000 : ℝ) (62578924209/125000000000 : ℝ) (500631393681/1000000000000 : ℝ) (250318806943/500000000000 : ℝ) (100127522779/200000000000 : ℝ) (500637613847/1000000000000 : ℝ) (500637613857/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8295/65536 : ℝ))) 4 (250318806943/500000000000 : ℝ) (100127522779/200000000000 : ℝ) (500637613847/1000000000000 : ℝ) (500637613857/1000000000000 : ℝ) (250318806933/500000000000 : ℝ) (125159403469/250000000000 : ℝ) (250318806933/500000000000 : ℝ) (125159403469/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8295/65536 : ℝ))) 5 (250318806933/500000000000 : ℝ) (125159403469/250000000000 : ℝ) (250318806933/500000000000 : ℝ) (125159403469/250000000000 : ℝ) (250318806933/500000000000 : ℝ) (125159403469/250000000000 : ℝ) (250318806933/500000000000 : ℝ) (125159403469/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8295/65536 : ℝ))) 6 (250318806933/500000000000 : ℝ) (125159403469/250000000000 : ℝ) (250318806933/500000000000 : ℝ) (125159403469/250000000000 : ℝ) (250318806933/500000000000 : ℝ) (125159403469/250000000000 : ℝ) (250318806933/500000000000 : ℝ) (125159403469/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8295/65536 : ℝ))) 7 (250318806933/500000000000 : ℝ) (125159403469/250000000000 : ℝ) (250318806933/500000000000 : ℝ) (125159403469/250000000000 : ℝ) (250318806933/500000000000 : ℝ) (125159403469/250000000000 : ℝ) (250318806933/500000000000 : ℝ) (125159403469/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8295/65536 : ℝ)) hmem 8 (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ) (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8295/65536 : ℝ))) hcmem 8 (250318806933/500000000000 : ℝ) (125159403469/250000000000 : ℝ) (250318806933/500000000000 : ℝ) (125159403469/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8295/65536 : ℝ)) (496068000331/500000000000 : ℝ) (496068000333/500000000000 : ℝ) (250318806933/500000000000 : ℝ) (125159403469/250000000000 : ℝ) (792632990223/1000000000000 : ℝ) (792632990243/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0399_exp_lower
  have heNumeric : (2054904164237/1000000000000 : ℝ)/4 ≤ Real.exp (-42628169578677/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904164237/1000000000000 : ℝ)/4 ≤ Real.exp ((33179/262144 : ℝ)-(792632990243/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33179/262144 : ℝ) (8295/65536 : ℝ) (792632990243/1000000000000 : ℝ) (2054904164237/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0375_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0375_certificate
#check SmaleRate.Proofs.cover8_leaf0376_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0376_certificate
#check SmaleRate.Proofs.cover8_leaf0377_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0377_certificate
#check SmaleRate.Proofs.cover8_leaf0378_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0378_certificate
#check SmaleRate.Proofs.cover8_leaf0379_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0379_certificate
#check SmaleRate.Proofs.cover8_leaf0380_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0380_certificate
#check SmaleRate.Proofs.cover8_leaf0381_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0381_certificate
#check SmaleRate.Proofs.cover8_leaf0382_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0382_certificate
#check SmaleRate.Proofs.cover8_leaf0383_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0383_certificate
#check SmaleRate.Proofs.cover8_leaf0384_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0384_certificate
#check SmaleRate.Proofs.cover8_leaf0385_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0385_certificate
#check SmaleRate.Proofs.cover8_leaf0386_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0386_certificate
#check SmaleRate.Proofs.cover8_leaf0387_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0387_certificate
#check SmaleRate.Proofs.cover8_leaf0388_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0388_certificate
#check SmaleRate.Proofs.cover8_leaf0389_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0389_certificate
#check SmaleRate.Proofs.cover8_leaf0390_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0390_certificate
#check SmaleRate.Proofs.cover8_leaf0391_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0391_certificate
#check SmaleRate.Proofs.cover8_leaf0392_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0392_certificate
#check SmaleRate.Proofs.cover8_leaf0393_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0393_certificate
#check SmaleRate.Proofs.cover8_leaf0394_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0394_certificate
#check SmaleRate.Proofs.cover8_leaf0395_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0395_certificate
#check SmaleRate.Proofs.cover8_leaf0396_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0396_certificate
#check SmaleRate.Proofs.cover8_leaf0397_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0397_certificate
#check SmaleRate.Proofs.cover8_leaf0398_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0398_certificate
#check SmaleRate.Proofs.cover8_leaf0399_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0399_certificate
