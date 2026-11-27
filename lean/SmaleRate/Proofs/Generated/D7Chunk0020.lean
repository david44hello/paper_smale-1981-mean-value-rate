/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0500; no trusted numerical premise.
theorem cover7_leaf0500_exp_radius : (997507210248221939/1000000000000000000 : ℝ) ≤ Real.exp ((-1145/57344 : ℝ)/8) ∧ Real.exp ((-1145/57344 : ℝ)/8) ≤ (49875360512411097/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1145/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0500_exp_lower : (183618153947055093/200000000000000000 : ℝ) ≤ Real.exp ((-5469376994717/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469376994717/8000000000000 : ℝ)/8) ≤ (459045384867637733/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469376994717/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0500_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (40380803467/20000000000 : ℝ) ≤ 4*Real.exp (4579/32768 : ℝ)*Real.exp (-mu (radius 7 (1145/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (40380803467/20000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1145/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0500_exp_radius
  have hrNumeric : (980230809253/1000000000000 : ℝ) ≤ Real.exp (-1145/57344 : ℝ) ∧ Real.exp (-1145/57344 : ℝ) ≤ (490115404627/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980230809253/1000000000000 : ℝ) ≤ (radius 7 (1145/8192 : ℝ)) ∧ (radius 7 (1145/8192 : ℝ)) ≤ (490115404627/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1145/8192 : ℝ)) (980230809253/1000000000000 : ℝ) (490115404627/500000000000 : ℝ) (197857424903/1000000000000 : ℝ) (49464356227/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1145/8192 : ℝ)) (980230809253/1000000000000 : ℝ) (490115404627/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1145/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980230809253/1000000000000 : ℝ) (490115404627/500000000000 : ℝ) (495057702313/500000000000 : ℝ) (990115404627/1000000000000 : ℝ) (39602642523/40000000000 : ℝ) (247516515769/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1145/8192 : ℝ)) 1 (495057702313/500000000000 : ℝ) (990115404627/1000000000000 : ℝ) (39602642523/40000000000 : ℝ) (247516515769/250000000000 : ℝ) (19801814677/20000000000 : ℝ) (247522683463/250000000000 : ℝ) (990090733543/1000000000000 : ℝ) (198018146709/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1145/8192 : ℝ)) 2 (19801814677/20000000000 : ℝ) (247522683463/250000000000 : ℝ) (990090733543/1000000000000 : ℝ) (198018146709/200000000000 : ℝ) (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ) (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1145/8192 : ℝ)) 3 (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ) (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ) (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ) (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1145/8192 : ℝ)) 4 (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ) (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ) (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ) (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1145/8192 : ℝ)) 5 (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ) (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ) (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ) (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1145/8192 : ℝ)) 6 (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ) (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ) (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ) (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1145/8192 : ℝ)) 7 (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ) (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ) (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ) (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1145/8192 : ℝ))) (197857424903/1000000000000 : ℝ) (49464356227/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1145/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (197857424903/1000000000000 : ℝ) (49464356227/250000000000 : ℝ) (598928712451/1000000000000 : ℝ) (299464356227/500000000000 : ℝ) (444811673523/1000000000000 : ℝ) (44481167353/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1145/8192 : ℝ))) 1 (598928712451/1000000000000 : ℝ) (299464356227/500000000000 : ℝ) (444811673523/1000000000000 : ℝ) (44481167353/100000000000 : ℝ) (521870192987/1000000000000 : ℝ) (16308443531/31250000000 : ℝ) (516149671031/1000000000000 : ℝ) (258074835519/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1145/8192 : ℝ))) 2 (521870192987/1000000000000 : ℝ) (16308443531/31250000000 : ℝ) (516149671031/1000000000000 : ℝ) (258074835519/500000000000 : ℝ) (519009932009/1000000000000 : ℝ) (103801986403/200000000000 : ℝ) (519002050507/1000000000000 : ℝ) (259501025257/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1145/8192 : ℝ))) 3 (519009932009/1000000000000 : ℝ) (103801986403/200000000000 : ℝ) (519002050507/1000000000000 : ℝ) (259501025257/500000000000 : ℝ) (259502995629/500000000000 : ℝ) (103801198253/200000000000 : ℝ) (519005991243/1000000000000 : ℝ) (415204793/800000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1145/8192 : ℝ))) 4 (259502995629/500000000000 : ℝ) (103801198253/200000000000 : ℝ) (519005991243/1000000000000 : ℝ) (415204793/800000000 : ℝ) (415204793/800000000 : ℝ) (259502995629/500000000000 : ℝ) (415204793/800000000 : ℝ) (259502995629/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1145/8192 : ℝ))) 5 (415204793/800000000 : ℝ) (259502995629/500000000000 : ℝ) (415204793/800000000 : ℝ) (259502995629/500000000000 : ℝ) (415204793/800000000 : ℝ) (259502995629/500000000000 : ℝ) (415204793/800000000 : ℝ) (259502995629/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1145/8192 : ℝ))) 6 (415204793/800000000 : ℝ) (259502995629/500000000000 : ℝ) (415204793/800000000 : ℝ) (259502995629/500000000000 : ℝ) (415204793/800000000 : ℝ) (259502995629/500000000000 : ℝ) (415204793/800000000 : ℝ) (259502995629/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1145/8192 : ℝ))) 7 (415204793/800000000 : ℝ) (259502995629/500000000000 : ℝ) (415204793/800000000 : ℝ) (259502995629/500000000000 : ℝ) (415204793/800000000 : ℝ) (259502995629/500000000000 : ℝ) (415204793/800000000 : ℝ) (259502995629/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1145/8192 : ℝ)) hmem 8 (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ) (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1145/8192 : ℝ))) hcmem 8 (415204793/800000000 : ℝ) (259502995629/500000000000 : ℝ) (415204793/800000000 : ℝ) (259502995629/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1145/8192 : ℝ)) (7735083857/7812500000 : ℝ) (990090733699/1000000000000 : ℝ) (415204793/800000000 : ℝ) (259502995629/500000000000 : ℝ) (411706057279/500000000000 : ℝ) (411706057287/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0500_exp_lower
  have heNumeric : (40380803467/20000000000 : ℝ)/4 ≤ Real.exp (-5469376994717/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (40380803467/20000000000 : ℝ)/4 ≤ Real.exp ((4579/32768 : ℝ)-(411706057287/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4579/32768 : ℝ) (1145/8192 : ℝ) (411706057287/500000000000 : ℝ) (40380803467/20000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0501; no trusted numerical premise.
theorem cover7_leaf0501_exp_radius : (997506666650080433/1000000000000000000 : ℝ) ≤ Real.exp ((-4581/229376 : ℝ)/8) ∧ Real.exp ((-4581/229376 : ℝ)/8) ≤ (498753333325040217/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4581/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0501_exp_lower : (459045414807331831/500000000000000000 : ℝ) ≤ Real.exp ((-1367343205133/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367343205133/2000000000000 : ℝ)/8) ≤ (918090829614663663/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367343205133/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0501_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019041226831/1000000000000 : ℝ) ≤ 4*Real.exp (1145/8192 : ℝ)*Real.exp (-mu (radius 7 (4581/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019041226831/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4581/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0501_exp_radius
  have hrNumeric : (196045307159/200000000000 : ℝ) ≤ Real.exp (-4581/229376 : ℝ) ∧ Real.exp (-4581/229376 : ℝ) ≤ (245056633949/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196045307159/200000000000 : ℝ) ≤ (radius 7 (4581/32768 : ℝ)) ∧ (radius 7 (4581/32768 : ℝ)) ≤ (245056633949/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4581/32768 : ℝ)) (196045307159/200000000000 : ℝ) (245056633949/250000000000 : ℝ) (197878595409/1000000000000 : ℝ) (39575719083/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4581/32768 : ℝ)) (196045307159/200000000000 : ℝ) (245056633949/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4581/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196045307159/200000000000 : ℝ) (245056633949/250000000000 : ℝ) (990113267897/1000000000000 : ℝ) (495056633949/500000000000 : ℝ) (123757988113/125000000000 : ℝ) (495031952453/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4581/32768 : ℝ)) 1 (990113267897/1000000000000 : ℝ) (495056633949/500000000000 : ℝ) (123757988113/125000000000 : ℝ) (495031952453/500000000000 : ℝ) (1237610733/1250000000 : ℝ) (495044293201/500000000000 : ℝ) (247522146523/250000000000 : ℝ) (198017717219/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4581/32768 : ℝ)) 2 (1237610733/1250000000 : ℝ) (495044293201/500000000000 : ℝ) (247522146523/250000000000 : ℝ) (198017717219/200000000000 : ℝ) (495044293123/500000000000 : ℝ) (990088586249/1000000000000 : ℝ) (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4581/32768 : ℝ)) 3 (495044293123/500000000000 : ℝ) (990088586249/1000000000000 : ℝ) (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ) (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ) (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4581/32768 : ℝ)) 4 (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ) (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ) (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ) (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4581/32768 : ℝ)) 5 (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ) (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ) (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ) (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4581/32768 : ℝ)) 6 (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ) (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ) (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ) (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4581/32768 : ℝ)) 7 (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ) (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ) (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ) (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4581/32768 : ℝ))) (197878595409/1000000000000 : ℝ) (39575719083/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4581/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (197878595409/1000000000000 : ℝ) (39575719083/200000000000 : ℝ) (74867412213/125000000000 : ℝ) (149734824427/250000000000 : ℝ) (444835470043/1000000000000 : ℝ) (444835470051/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4581/32768 : ℝ))) 1 (74867412213/125000000000 : ℝ) (149734824427/250000000000 : ℝ) (444835470043/1000000000000 : ℝ) (444835470051/1000000000000 : ℝ) (521887383873/1000000000000 : ℝ) (13047184597/25000000000 : ℝ) (10323360771/20000000000 : ℝ) (258084019279/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4581/32768 : ℝ))) 2 (521887383873/1000000000000 : ℝ) (13047184597/25000000000 : ℝ) (10323360771/20000000000 : ℝ) (258084019279/500000000000 : ℝ) (519027711211/1000000000000 : ℝ) (519027711219/1000000000000 : ℝ) (519019833221/1000000000000 : ℝ) (51901983323/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4581/32768 : ℝ))) 3 (519027711211/1000000000000 : ℝ) (519027711219/1000000000000 : ℝ) (519019833221/1000000000000 : ℝ) (51901983323/100000000000 : ℝ) (64877971527/125000000000 : ℝ) (20760950889/40000000000 : ℝ) (519023772201/1000000000000 : ℝ) (51902377221/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4581/32768 : ℝ))) 4 (64877971527/125000000000 : ℝ) (20760950889/40000000000 : ℝ) (519023772201/1000000000000 : ℝ) (51902377221/100000000000 : ℝ) (32438985763/62500000000 : ℝ) (259511886109/500000000000 : ℝ) (32438985763/62500000000 : ℝ) (259511886109/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4581/32768 : ℝ))) 5 (32438985763/62500000000 : ℝ) (259511886109/500000000000 : ℝ) (32438985763/62500000000 : ℝ) (259511886109/500000000000 : ℝ) (32438985763/62500000000 : ℝ) (259511886109/500000000000 : ℝ) (32438985763/62500000000 : ℝ) (259511886109/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4581/32768 : ℝ))) 6 (32438985763/62500000000 : ℝ) (259511886109/500000000000 : ℝ) (32438985763/62500000000 : ℝ) (259511886109/500000000000 : ℝ) (32438985763/62500000000 : ℝ) (259511886109/500000000000 : ℝ) (32438985763/62500000000 : ℝ) (259511886109/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4581/32768 : ℝ))) 7 (32438985763/62500000000 : ℝ) (259511886109/500000000000 : ℝ) (32438985763/62500000000 : ℝ) (259511886109/500000000000 : ℝ) (32438985763/62500000000 : ℝ) (259511886109/500000000000 : ℝ) (32438985763/62500000000 : ℝ) (259511886109/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4581/32768 : ℝ)) hmem 8 (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ) (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4581/32768 : ℝ))) hcmem 8 (32438985763/62500000000 : ℝ) (259511886109/500000000000 : ℝ) (32438985763/62500000000 : ℝ) (259511886109/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4581/32768 : ℝ)) (198017717249/200000000000 : ℝ) (990088586249/1000000000000 : ℝ) (32438985763/62500000000 : ℝ) (259511886109/500000000000 : ℝ) (823442110359/1000000000000 : ℝ) (823442110379/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0501_exp_lower
  have heNumeric : (2019041226831/1000000000000 : ℝ)/4 ≤ Real.exp (-1367343205133/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019041226831/1000000000000 : ℝ)/4 ≤ Real.exp ((1145/8192 : ℝ)-(823442110379/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1145/8192 : ℝ) (4581/32768 : ℝ) (823442110379/1000000000000 : ℝ) (2019041226831/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0502; no trusted numerical premise.
theorem cover7_leaf0502_exp_radius : (249376530763058791/250000000000000000 : ℝ) ≤ Real.exp ((-2291/114688 : ℝ)/8) ∧ Real.exp ((-2291/114688 : ℝ)/8) ≤ (199501224610447033/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2291/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0502_exp_lower : (918090889995448153/1000000000000000000 : ℝ) ≤ Real.exp ((-1093873722279/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093873722279/1600000000000 : ℝ)/8) ≤ (459045444997724077/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093873722279/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0502_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009521144567/500000000000 : ℝ) ≤ 4*Real.exp (4581/32768 : ℝ)*Real.exp (-mu (radius 7 (2291/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (1009521144567/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2291/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0502_exp_radius
  have hrNumeric : (245055565589/250000000000 : ℝ) ≤ Real.exp (-2291/114688 : ℝ) ∧ Real.exp (-2291/114688 : ℝ) ≤ (980222262357/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245055565589/250000000000 : ℝ) ≤ (radius 7 (2291/16384 : ℝ)) ∧ (radius 7 (2291/16384 : ℝ)) ≤ (980222262357/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2291/16384 : ℝ)) (245055565589/250000000000 : ℝ) (980222262357/1000000000000 : ℝ) (39579952693/200000000000 : ℝ) (197899763471/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2291/16384 : ℝ)) (245055565589/250000000000 : ℝ) (980222262357/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2291/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245055565589/250000000000 : ℝ) (980222262357/1000000000000 : ℝ) (495055565589/500000000000 : ℝ) (990111131179/1000000000000 : ℝ) (990061746739/1000000000000 : ℝ) (49503087337/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2291/16384 : ℝ)) 1 (495055565589/500000000000 : ℝ) (990111131179/1000000000000 : ℝ) (990061746739/1000000000000 : ℝ) (49503087337/50000000000 : ℝ) (495043219479/500000000000 : ℝ) (12376080487/12500000000 : ℝ) (19801728773/20000000000 : ℝ) (247521609663/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2291/16384 : ℝ)) 2 (495043219479/500000000000 : ℝ) (12376080487/12500000000 : ℝ) (19801728773/20000000000 : ℝ) (247521609663/250000000000 : ℝ) (247521609701/250000000000 : ℝ) (495043219403/500000000000 : ℝ) (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2291/16384 : ℝ)) 3 (247521609701/250000000000 : ℝ) (495043219403/500000000000 : ℝ) (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ) (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ) (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2291/16384 : ℝ)) 4 (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ) (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ) (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ) (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2291/16384 : ℝ)) 5 (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ) (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ) (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ) (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2291/16384 : ℝ)) 6 (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ) (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ) (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ) (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2291/16384 : ℝ)) 7 (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ) (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ) (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ) (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2291/16384 : ℝ))) (39579952693/200000000000 : ℝ) (197899763471/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2291/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39579952693/200000000000 : ℝ) (197899763471/1000000000000 : ℝ) (149737470433/250000000000 : ℝ) (74868735217/125000000000 : ℝ) (444859262537/1000000000000 : ℝ) (27803703909/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2291/16384 : ℝ))) 1 (149737470433/250000000000 : ℝ) (74868735217/125000000000 : ℝ) (444859262537/1000000000000 : ℝ) (27803703909/62500000000 : ℝ) (260952286067/500000000000 : ℝ) (26095228607/50000000000 : ℝ) (3226165019/6250000000 : ℝ) (516186403047/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2291/16384 : ℝ))) 2 (260952286067/500000000000 : ℝ) (26095228607/50000000000 : ℝ) (3226165019/6250000000 : ℝ) (516186403047/1000000000000 : ℝ) (519045487587/1000000000000 : ℝ) (259522743797/500000000000 : ℝ) (519037613107/1000000000000 : ℝ) (259518806557/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2291/16384 : ℝ))) 3 (519045487587/1000000000000 : ℝ) (259522743797/500000000000 : ℝ) (519037613107/1000000000000 : ℝ) (259518806557/500000000000 : ℝ) (519041550347/1000000000000 : ℝ) (259520775177/500000000000 : ℝ) (129760387583/250000000000 : ℝ) (25952077517/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2291/16384 : ℝ))) 4 (519041550347/1000000000000 : ℝ) (259520775177/500000000000 : ℝ) (129760387583/250000000000 : ℝ) (25952077517/50000000000 : ℝ) (519041550339/1000000000000 : ℝ) (519041550347/1000000000000 : ℝ) (519041550339/1000000000000 : ℝ) (519041550347/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2291/16384 : ℝ))) 5 (519041550339/1000000000000 : ℝ) (519041550347/1000000000000 : ℝ) (519041550339/1000000000000 : ℝ) (519041550347/1000000000000 : ℝ) (519041550339/1000000000000 : ℝ) (519041550347/1000000000000 : ℝ) (519041550339/1000000000000 : ℝ) (519041550347/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2291/16384 : ℝ))) 6 (519041550339/1000000000000 : ℝ) (519041550347/1000000000000 : ℝ) (519041550339/1000000000000 : ℝ) (519041550347/1000000000000 : ℝ) (519041550339/1000000000000 : ℝ) (519041550347/1000000000000 : ℝ) (519041550339/1000000000000 : ℝ) (519041550347/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2291/16384 : ℝ))) 7 (519041550339/1000000000000 : ℝ) (519041550347/1000000000000 : ℝ) (519041550339/1000000000000 : ℝ) (519041550347/1000000000000 : ℝ) (519041550339/1000000000000 : ℝ) (519041550347/1000000000000 : ℝ) (519041550339/1000000000000 : ℝ) (519041550347/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2291/16384 : ℝ)) hmem 8 (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ) (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2291/16384 : ℝ))) hcmem 8 (519041550339/1000000000000 : ℝ) (519041550347/1000000000000 : ℝ) (519041550339/1000000000000 : ℝ) (519041550347/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2291/16384 : ℝ)) (990086438803/1000000000000 : ℝ) (495043219403/500000000000 : ℝ) (519041550339/1000000000000 : ℝ) (519041550347/1000000000000 : ℝ) (823472101799/1000000000000 : ℝ) (164694420363/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0502_exp_lower
  have heNumeric : (1009521144567/500000000000 : ℝ)/4 ≤ Real.exp (-1093873722279/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009521144567/500000000000 : ℝ)/4 ≤ Real.exp ((4581/32768 : ℝ)-(164694420363/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4581/32768 : ℝ) (2291/16384 : ℝ) (164694420363/200000000000 : ℝ) (1009521144567/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0503; no trusted numerical premise.
theorem cover7_leaf0503_exp_radius : (249376394863671533/250000000000000000 : ℝ) ≤ Real.exp ((-4583/229376 : ℝ)/8) ∧ Real.exp ((-4583/229376 : ℝ)/8) ≤ (997505579454686133/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4583/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0503_exp_lower : (57380684429758571/62500000000000000 : ℝ) ≤ Real.exp ((-546936436741/800000000000 : ℝ)/8) ∧ Real.exp ((-546936436741/800000000000 : ℝ)/8) ≤ (918090950876137137/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-546936436741/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0503_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252380420029/125000000000 : ℝ) ≤ 4*Real.exp (2291/16384 : ℝ)*Real.exp (-mu (radius 7 (4583/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (252380420029/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4583/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0503_exp_radius
  have hrNumeric : (196043597787/200000000000 : ℝ) ≤ Real.exp (-4583/229376 : ℝ) ∧ Real.exp (-4583/229376 : ℝ) ≤ (122527248617/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196043597787/200000000000 : ℝ) ≤ (radius 7 (4583/32768 : ℝ)) ∧ (radius 7 (4583/32768 : ℝ)) ≤ (122527248617/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4583/32768 : ℝ)) (196043597787/200000000000 : ℝ) (122527248617/125000000000 : ℝ) (7916837163/40000000000 : ℝ) (197920929081/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4583/32768 : ℝ)) (196043597787/200000000000 : ℝ) (122527248617/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4583/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196043597787/200000000000 : ℝ) (122527248617/125000000000 : ℝ) (990108994467/1000000000000 : ℝ) (247527248617/250000000000 : ℝ) (990059588577/1000000000000 : ℝ) (990059588579/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4583/32768 : ℝ)) 1 (990108994467/1000000000000 : ℝ) (247527248617/250000000000 : ℝ) (990059588577/1000000000000 : ℝ) (990059588579/1000000000000 : ℝ) (495042145761/500000000000 : ℝ) (247521072881/250000000000 : ℝ) (990084291213/1000000000000 : ℝ) (61880268201/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4583/32768 : ℝ)) 2 (495042145761/500000000000 : ℝ) (247521072881/250000000000 : ℝ) (990084291213/1000000000000 : ℝ) (61880268201/62500000000 : ℝ) (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ) (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4583/32768 : ℝ)) 3 (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ) (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ) (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ) (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4583/32768 : ℝ)) 4 (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ) (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ) (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ) (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4583/32768 : ℝ)) 5 (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ) (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ) (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ) (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4583/32768 : ℝ)) 6 (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ) (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ) (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ) (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4583/32768 : ℝ)) 7 (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ) (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ) (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ) (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4583/32768 : ℝ))) (7916837163/40000000000 : ℝ) (197920929081/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4583/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7916837163/40000000000 : ℝ) (197920929081/1000000000000 : ℝ) (598960464537/1000000000000 : ℝ) (598960464541/1000000000000 : ℝ) (868912209/1953125000 : ℝ) (55610381377/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4583/32768 : ℝ))) 1 (598960464537/1000000000000 : ℝ) (598960464541/1000000000000 : ℝ) (868912209/1953125000 : ℝ) (55610381377/125000000000 : ℝ) (130480439443/250000000000 : ℝ) (521921757779/1000000000000 : ℝ) (516204764503/1000000000000 : ℝ) (516204764511/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4583/32768 : ℝ))) 2 (130480439443/250000000000 : ℝ) (521921757779/1000000000000 : ℝ) (516204764503/1000000000000 : ℝ) (516204764511/1000000000000 : ℝ) (519063261137/1000000000000 : ℝ) (103812652229/200000000000 : ℝ) (103811078033/200000000000 : ℝ) (519055390173/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4583/32768 : ℝ))) 3 (519063261137/1000000000000 : ℝ) (103812652229/200000000000 : ℝ) (103811078033/200000000000 : ℝ) (519055390173/1000000000000 : ℝ) (519059325651/1000000000000 : ℝ) (519059325659/1000000000000 : ℝ) (129764831409/250000000000 : ℝ) (103811865129/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4583/32768 : ℝ))) 4 (519059325651/1000000000000 : ℝ) (519059325659/1000000000000 : ℝ) (129764831409/250000000000 : ℝ) (103811865129/200000000000 : ℝ) (519059325643/1000000000000 : ℝ) (129764831413/250000000000 : ℝ) (519059325643/1000000000000 : ℝ) (129764831413/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4583/32768 : ℝ))) 5 (519059325643/1000000000000 : ℝ) (129764831413/250000000000 : ℝ) (519059325643/1000000000000 : ℝ) (129764831413/250000000000 : ℝ) (519059325643/1000000000000 : ℝ) (129764831413/250000000000 : ℝ) (519059325643/1000000000000 : ℝ) (129764831413/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4583/32768 : ℝ))) 6 (519059325643/1000000000000 : ℝ) (129764831413/250000000000 : ℝ) (519059325643/1000000000000 : ℝ) (129764831413/250000000000 : ℝ) (519059325643/1000000000000 : ℝ) (129764831413/250000000000 : ℝ) (519059325643/1000000000000 : ℝ) (129764831413/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4583/32768 : ℝ))) 7 (519059325643/1000000000000 : ℝ) (129764831413/250000000000 : ℝ) (519059325643/1000000000000 : ℝ) (129764831413/250000000000 : ℝ) (519059325643/1000000000000 : ℝ) (129764831413/250000000000 : ℝ) (519059325643/1000000000000 : ℝ) (129764831413/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4583/32768 : ℝ)) hmem 8 (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ) (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4583/32768 : ℝ))) hcmem 8 (519059325643/1000000000000 : ℝ) (129764831413/250000000000 : ℝ) (519059325643/1000000000000 : ℝ) (129764831413/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4583/32768 : ℝ)) (990084291367/1000000000000 : ℝ) (99008429137/100000000000 : ℝ) (519059325643/1000000000000 : ℝ) (129764831413/250000000000 : ℝ) (411751044439/500000000000 : ℝ) (164700417779/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0503_exp_lower
  have heNumeric : (252380420029/125000000000 : ℝ)/4 ≤ Real.exp (-546936436741/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252380420029/125000000000 : ℝ)/4 ≤ Real.exp ((2291/16384 : ℝ)-(164700417779/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2291/16384 : ℝ) (4583/32768 : ℝ) (164700417779/200000000000 : ℝ) (252380420029/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0504; no trusted numerical premise.
theorem cover7_leaf0504_exp_radius : (498752517928716669/500000000000000000 : ℝ) ≤ Real.exp ((-573/28672 : ℝ)/8) ∧ Real.exp ((-573/28672 : ℝ)/8) ≤ (997505035857433339/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-573/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0504_exp_lower : (918091012257189759/1000000000000000000 : ℝ) ≤ Real.exp ((-1093872017709/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093872017709/1600000000000 : ℝ)/8) ≤ (1434517206651859/1562500000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093872017709/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0504_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009522220067/500000000000 : ℝ) ≤ 4*Real.exp (4583/32768 : ℝ)*Real.exp (-mu (radius 7 (573/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (1009522220067/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (573/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0504_exp_radius
  have hrNumeric : (980213715533/1000000000000 : ℝ) ≤ Real.exp (-573/28672 : ℝ) ∧ Real.exp (-573/28672 : ℝ) ≤ (490106857767/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980213715533/1000000000000 : ℝ) ≤ (radius 7 (573/4096 : ℝ)) ∧ (radius 7 (573/4096 : ℝ)) ≤ (490106857767/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (573/4096 : ℝ)) (980213715533/1000000000000 : ℝ) (490106857767/500000000000 : ℝ) (49485523059/250000000000 : ℝ) (98971046121/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (573/4096 : ℝ)) (980213715533/1000000000000 : ℝ) (490106857767/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (573/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980213715533/1000000000000 : ℝ) (490106857767/500000000000 : ℝ) (495053428883/500000000000 : ℝ) (990106857767/1000000000000 : ℝ) (990057430421/1000000000000 : ℝ) (990057430423/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (573/4096 : ℝ)) 1 (495053428883/500000000000 : ℝ) (990106857767/1000000000000 : ℝ) (990057430421/1000000000000 : ℝ) (990057430423/1000000000000 : ℝ) (990082144093/1000000000000 : ℝ) (198016428819/200000000000 : ℝ) (198016428757/200000000000 : ℝ) (990082143787/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (573/4096 : ℝ)) 2 (990082144093/1000000000000 : ℝ) (198016428819/200000000000 : ℝ) (198016428757/200000000000 : ℝ) (990082143787/1000000000000 : ℝ) (990082143939/1000000000000 : ℝ) (990082143941/1000000000000 : ℝ) (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (573/4096 : ℝ)) 3 (990082143939/1000000000000 : ℝ) (990082143941/1000000000000 : ℝ) (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ) (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ) (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (573/4096 : ℝ)) 4 (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ) (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ) (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ) (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (573/4096 : ℝ)) 5 (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ) (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ) (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ) (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (573/4096 : ℝ)) 6 (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ) (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ) (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ) (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (573/4096 : ℝ)) 7 (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ) (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ) (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ) (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (573/4096 : ℝ))) (49485523059/250000000000 : ℝ) (98971046121/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (573/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49485523059/250000000000 : ℝ) (98971046121/500000000000 : ℝ) (299485523059/500000000000 : ℝ) (598971046121/1000000000000 : ℝ) (868958663/1953125000 : ℝ) (55613354433/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (573/4096 : ℝ))) 1 (299485523059/500000000000 : ℝ) (598971046121/1000000000000 : ℝ) (868958663/1953125000 : ℝ) (55613354433/125000000000 : ℝ) (521938940787/1000000000000 : ℝ) (521938940793/1000000000000 : ℝ) (25811156147/50000000000 : ℝ) (516223122947/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (573/4096 : ℝ))) 2 (521938940787/1000000000000 : ℝ) (521938940793/1000000000000 : ℝ) (25811156147/50000000000 : ℝ) (516223122947/1000000000000 : ℝ) (519081031863/1000000000000 : ℝ) (51908103187/100000000000 : ℝ) (129768291099/250000000000 : ℝ) (129768291101/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (573/4096 : ℝ))) 3 (519081031863/1000000000000 : ℝ) (51908103187/100000000000 : ℝ) (129768291099/250000000000 : ℝ) (129768291101/250000000000 : ℝ) (519077098129/1000000000000 : ℝ) (519077098137/1000000000000 : ℝ) (259538549057/500000000000 : ℝ) (519077098123/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (573/4096 : ℝ))) 4 (519077098129/1000000000000 : ℝ) (519077098137/1000000000000 : ℝ) (259538549057/500000000000 : ℝ) (519077098123/1000000000000 : ℝ) (519077098121/1000000000000 : ℝ) (51907709813/100000000000 : ℝ) (519077098121/1000000000000 : ℝ) (51907709813/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (573/4096 : ℝ))) 5 (519077098121/1000000000000 : ℝ) (51907709813/100000000000 : ℝ) (519077098121/1000000000000 : ℝ) (51907709813/100000000000 : ℝ) (519077098121/1000000000000 : ℝ) (51907709813/100000000000 : ℝ) (519077098121/1000000000000 : ℝ) (51907709813/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (573/4096 : ℝ))) 6 (519077098121/1000000000000 : ℝ) (51907709813/100000000000 : ℝ) (519077098121/1000000000000 : ℝ) (51907709813/100000000000 : ℝ) (519077098121/1000000000000 : ℝ) (51907709813/100000000000 : ℝ) (519077098121/1000000000000 : ℝ) (51907709813/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (573/4096 : ℝ))) 7 (519077098121/1000000000000 : ℝ) (51907709813/100000000000 : ℝ) (519077098121/1000000000000 : ℝ) (51907709813/100000000000 : ℝ) (519077098121/1000000000000 : ℝ) (51907709813/100000000000 : ℝ) (519077098121/1000000000000 : ℝ) (51907709813/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (573/4096 : ℝ)) hmem 8 (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ) (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (573/4096 : ℝ))) hcmem 8 (519077098121/1000000000000 : ℝ) (51907709813/100000000000 : ℝ) (519077098121/1000000000000 : ℝ) (51907709813/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (573/4096 : ℝ)) (495041071969/500000000000 : ℝ) (990082143941/1000000000000 : ℝ) (519077098121/1000000000000 : ℝ) (51907709813/100000000000 : ℝ) (823532071597/1000000000000 : ℝ) (164706414323/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0504_exp_lower
  have heNumeric : (1009522220067/500000000000 : ℝ)/4 ≤ Real.exp (-1093872017709/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009522220067/500000000000 : ℝ)/4 ≤ Real.exp ((4583/32768 : ℝ)-(164706414323/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4583/32768 : ℝ) (573/4096 : ℝ) (164706414323/200000000000 : ℝ) (1009522220067/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0505; no trusted numerical premise.
theorem cover7_leaf0505_exp_radius : (49875224613023839/50000000000000000 : ℝ) ≤ Real.exp ((-655/32768 : ℝ)/8) ∧ Real.exp ((-655/32768 : ℝ)/8) ≤ (997504492260476781/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-655/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0505_exp_lower : (918091074138835643/1000000000000000000 : ℝ) ≤ Real.exp ((-85458683981/125000000000 : ℝ)/8) ∧ Real.exp ((-85458683981/125000000000 : ℝ)/8) ≤ (229522768534708911/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85458683981/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0505_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504761382211/250000000000 : ℝ) ≤ 4*Real.exp (573/4096 : ℝ)*Real.exp (-mu (radius 7 (4585/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (504761382211/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4585/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0505_exp_radius
  have hrNumeric : (19604188843/20000000000 : ℝ) ≤ Real.exp (-655/32768 : ℝ) ∧ Real.exp (-655/32768 : ℝ) ≤ (980209442151/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (19604188843/20000000000 : ℝ) ≤ (radius 7 (4585/32768 : ℝ)) ∧ (radius 7 (4585/32768 : ℝ)) ≤ (980209442151/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4585/32768 : ℝ)) (19604188843/20000000000 : ℝ) (980209442151/1000000000000 : ℝ) (49490813237/250000000000 : ℝ) (98981626477/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4585/32768 : ℝ)) (19604188843/20000000000 : ℝ) (980209442151/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4585/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (19604188843/20000000000 : ℝ) (980209442151/1000000000000 : ℝ) (39604188843/40000000000 : ℝ) (247526180269/250000000000 : ℝ) (99005527227/100000000000 : ℝ) (990055272271/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4585/32768 : ℝ)) 1 (39604188843/40000000000 : ℝ) (247526180269/250000000000 : ℝ) (99005527227/100000000000 : ℝ) (990055272271/1000000000000 : ℝ) (3867499987/3906250000 : ℝ) (495039998337/500000000000 : ℝ) (990079996363/1000000000000 : ℝ) (198015999273/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4585/32768 : ℝ)) 2 (3867499987/3906250000 : ℝ) (495039998337/500000000000 : ℝ) (990079996363/1000000000000 : ℝ) (198015999273/200000000000 : ℝ) (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ) (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4585/32768 : ℝ)) 3 (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ) (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ) (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ) (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4585/32768 : ℝ)) 4 (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ) (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ) (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ) (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4585/32768 : ℝ)) 5 (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ) (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ) (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ) (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4585/32768 : ℝ)) 6 (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ) (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ) (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ) (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4585/32768 : ℝ)) 7 (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ) (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ) (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ) (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4585/32768 : ℝ))) (49490813237/250000000000 : ℝ) (98981626477/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4585/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49490813237/250000000000 : ℝ) (98981626477/500000000000 : ℝ) (299490813237/500000000000 : ℝ) (598981626477/1000000000000 : ℝ) (11123265397/25000000000 : ℝ) (27808163493/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4585/32768 : ℝ))) 1 (299490813237/500000000000 : ℝ) (598981626477/1000000000000 : ℝ) (11123265397/25000000000 : ℝ) (27808163493/62500000000 : ℝ) (521956121177/1000000000000 : ℝ) (521956121183/1000000000000 : ℝ) (129060369587/250000000000 : ℝ) (103248295671/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4585/32768 : ℝ))) 2 (521956121177/1000000000000 : ℝ) (521956121183/1000000000000 : ℝ) (129060369587/250000000000 : ℝ) (103248295671/200000000000 : ℝ) (259549399881/500000000000 : ℝ) (519098799769/1000000000000 : ℝ) (519090935799/1000000000000 : ℝ) (519090935807/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4585/32768 : ℝ))) 3 (259549399881/500000000000 : ℝ) (519098799769/1000000000000 : ℝ) (519090935799/1000000000000 : ℝ) (519090935807/1000000000000 : ℝ) (25954743389/50000000000 : ℝ) (129773716947/250000000000 : ℝ) (103818973553/200000000000 : ℝ) (259547433887/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4585/32768 : ℝ))) 4 (25954743389/50000000000 : ℝ) (129773716947/250000000000 : ℝ) (103818973553/200000000000 : ℝ) (259547433887/500000000000 : ℝ) (129773716943/250000000000 : ℝ) (519094867781/1000000000000 : ℝ) (129773716943/250000000000 : ℝ) (519094867781/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4585/32768 : ℝ))) 5 (129773716943/250000000000 : ℝ) (519094867781/1000000000000 : ℝ) (129773716943/250000000000 : ℝ) (519094867781/1000000000000 : ℝ) (129773716943/250000000000 : ℝ) (519094867781/1000000000000 : ℝ) (129773716943/250000000000 : ℝ) (519094867781/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4585/32768 : ℝ))) 6 (129773716943/250000000000 : ℝ) (519094867781/1000000000000 : ℝ) (129773716943/250000000000 : ℝ) (519094867781/1000000000000 : ℝ) (129773716943/250000000000 : ℝ) (519094867781/1000000000000 : ℝ) (129773716943/250000000000 : ℝ) (519094867781/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4585/32768 : ℝ))) 7 (129773716943/250000000000 : ℝ) (519094867781/1000000000000 : ℝ) (129773716943/250000000000 : ℝ) (519094867781/1000000000000 : ℝ) (129773716943/250000000000 : ℝ) (519094867781/1000000000000 : ℝ) (129773716943/250000000000 : ℝ) (519094867781/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4585/32768 : ℝ)) hmem 8 (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ) (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4585/32768 : ℝ))) hcmem 8 (129773716943/250000000000 : ℝ) (519094867781/1000000000000 : ℝ) (129773716943/250000000000 : ℝ) (519094867781/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4585/32768 : ℝ)) (990079996517/1000000000000 : ℝ) (24751999913/25000000000 : ℝ) (129773716943/250000000000 : ℝ) (519094867781/1000000000000 : ℝ) (164712409991/200000000000 : ℝ) (823562049973/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0505_exp_lower
  have heNumeric : (504761382211/250000000000 : ℝ)/4 ≤ Real.exp (-85458683981/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504761382211/250000000000 : ℝ)/4 ≤ Real.exp ((573/4096 : ℝ)-(823562049973/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (573/4096 : ℝ) (4585/32768 : ℝ) (823562049973/1000000000000 : ℝ) (504761382211/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0506; no trusted numerical premise.
theorem cover7_leaf0506_exp_radius : (997503948663816459/1000000000000000000 : ℝ) ≤ Real.exp ((-2293/114688 : ℝ)/8) ∧ Real.exp ((-2293/114688 : ℝ)/8) ≤ (49875197433190823/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2293/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0506_exp_lower : (918091136519582993/1000000000000000000 : ℝ) ≤ Real.exp ((-5469351426231/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469351426231/8000000000000 : ℝ)/8) ≤ (459045568259791497/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469351426231/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0506_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403809325267/200000000000 : ℝ) ≤ 4*Real.exp (4585/32768 : ℝ)*Real.exp (-mu (radius 7 (2293/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (403809325267/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2293/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0506_exp_radius
  have hrNumeric : (196041033757/200000000000 : ℝ) ≤ Real.exp (-2293/114688 : ℝ) ∧ Real.exp (-2293/114688 : ℝ) ≤ (490102584393/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196041033757/200000000000 : ℝ) ≤ (radius 7 (2293/16384 : ℝ)) ∧ (radius 7 (2293/16384 : ℝ)) ≤ (490102584393/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2293/16384 : ℝ)) (196041033757/200000000000 : ℝ) (490102584393/500000000000 : ℝ) (197984411217/1000000000000 : ℝ) (197984411223/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2293/16384 : ℝ)) (196041033757/200000000000 : ℝ) (490102584393/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2293/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196041033757/200000000000 : ℝ) (490102584393/500000000000 : ℝ) (123762823049/125000000000 : ℝ) (990102584393/1000000000000 : ℝ) (990053114123/1000000000000 : ℝ) (247513278531/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2293/16384 : ℝ)) 1 (123762823049/125000000000 : ℝ) (990102584393/1000000000000 : ℝ) (990053114123/1000000000000 : ℝ) (247513278531/250000000000 : ℝ) (990077849257/1000000000000 : ℝ) (990077849259/1000000000000 : ℝ) (247519462237/250000000000 : ℝ) (19801556979/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2293/16384 : ℝ)) 2 (990077849257/1000000000000 : ℝ) (990077849259/1000000000000 : ℝ) (247519462237/250000000000 : ℝ) (19801556979/20000000000 : ℝ) (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ) (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2293/16384 : ℝ)) 3 (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ) (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ) (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ) (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2293/16384 : ℝ)) 4 (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ) (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ) (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ) (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2293/16384 : ℝ)) 5 (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ) (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ) (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ) (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2293/16384 : ℝ)) 6 (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ) (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ) (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ) (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2293/16384 : ℝ)) 7 (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ) (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ) (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ) (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2293/16384 : ℝ))) (197984411217/1000000000000 : ℝ) (197984411223/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2293/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (197984411217/1000000000000 : ℝ) (197984411223/1000000000000 : ℝ) (74874025701/125000000000 : ℝ) (149748051403/250000000000 : ℝ) (13904824759/31250000000 : ℝ) (55619299037/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2293/16384 : ℝ))) 1 (74874025701/125000000000 : ℝ) (149748051403/250000000000 : ℝ) (13904824759/31250000000 : ℝ) (55619299037/125000000000 : ℝ) (130493324737/250000000000 : ℝ) (260986649477/500000000000 : ℝ) (103251966147/200000000000 : ℝ) (516259830743/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2293/16384 : ℝ))) 2 (130493324737/250000000000 : ℝ) (260986649477/500000000000 : ℝ) (103251966147/200000000000 : ℝ) (516259830743/1000000000000 : ℝ) (519116564841/1000000000000 : ℝ) (519116564849/1000000000000 : ℝ) (25955435219/50000000000 : ℝ) (129777176097/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2293/16384 : ℝ))) 3 (519116564841/1000000000000 : ℝ) (519116564849/1000000000000 : ℝ) (25955435219/50000000000 : ℝ) (129777176097/250000000000 : ℝ) (51911263461/100000000000 : ℝ) (519112634619/1000000000000 : ℝ) (103822526919/200000000000 : ℝ) (129778158651/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2293/16384 : ℝ))) 4 (51911263461/100000000000 : ℝ) (519112634619/1000000000000 : ℝ) (103822526919/200000000000 : ℝ) (129778158651/250000000000 : ℝ) (259556317301/500000000000 : ℝ) (129778158653/250000000000 : ℝ) (259556317301/500000000000 : ℝ) (129778158653/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2293/16384 : ℝ))) 5 (259556317301/500000000000 : ℝ) (129778158653/250000000000 : ℝ) (259556317301/500000000000 : ℝ) (129778158653/250000000000 : ℝ) (259556317301/500000000000 : ℝ) (129778158653/250000000000 : ℝ) (259556317301/500000000000 : ℝ) (129778158653/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2293/16384 : ℝ))) 6 (259556317301/500000000000 : ℝ) (129778158653/250000000000 : ℝ) (259556317301/500000000000 : ℝ) (129778158653/250000000000 : ℝ) (259556317301/500000000000 : ℝ) (129778158653/250000000000 : ℝ) (259556317301/500000000000 : ℝ) (129778158653/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2293/16384 : ℝ))) 7 (259556317301/500000000000 : ℝ) (129778158653/250000000000 : ℝ) (259556317301/500000000000 : ℝ) (129778158653/250000000000 : ℝ) (259556317301/500000000000 : ℝ) (129778158653/250000000000 : ℝ) (259556317301/500000000000 : ℝ) (129778158653/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2293/16384 : ℝ)) hmem 8 (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ) (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2293/16384 : ℝ))) hcmem 8 (259556317301/500000000000 : ℝ) (129778158653/250000000000 : ℝ) (259556317301/500000000000 : ℝ) (129778158653/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2293/16384 : ℝ)) (495038924551/500000000000 : ℝ) (198015569821/200000000000 : ℝ) (259556317301/500000000000 : ℝ) (129778158653/250000000000 : ℝ) (823592023963/1000000000000 : ℝ) (411796011991/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0506_exp_lower
  have heNumeric : (403809325267/200000000000 : ℝ)/4 ≤ Real.exp (-5469351426231/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403809325267/200000000000 : ℝ)/4 ≤ Real.exp ((4585/32768 : ℝ)-(411796011991/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4585/32768 : ℝ) (2293/16384 : ℝ) (411796011991/500000000000 : ℝ) (403809325267/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0507; no trusted numerical premise.
theorem cover7_leaf0507_exp_radius : (7980027240539619/8000000000000000 : ℝ) ≤ Real.exp ((-4587/229376 : ℝ)/8) ∧ Real.exp ((-4587/229376 : ℝ)/8) ≤ (124687925633431547/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4587/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0507_exp_lower : (459045599700289761/500000000000000000 : ℝ) ≤ Real.exp ((-2734673521403/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734673521403/4000000000000 : ℝ)/8) ≤ (918091199400579523/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734673521403/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0507_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504761933157/250000000000 : ℝ) ≤ 4*Real.exp (2293/16384 : ℝ)*Real.exp (-mu (radius 7 (4587/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (504761933157/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4587/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0507_exp_radius
  have hrNumeric : (980200895439/1000000000000 : ℝ) ≤ Real.exp (-4587/229376 : ℝ) ∧ Real.exp (-4587/229376 : ℝ) ≤ (12252511193/12500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980200895439/1000000000000 : ℝ) ≤ (radius 7 (4587/32768 : ℝ)) ∧ (radius 7 (4587/32768 : ℝ)) ≤ (12252511193/12500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4587/32768 : ℝ)) (980200895439/1000000000000 : ℝ) (12252511193/12500000000 : ℝ) (198005567039/1000000000000 : ℝ) (39601113409/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4587/32768 : ℝ)) (980200895439/1000000000000 : ℝ) (12252511193/12500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4587/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980200895439/1000000000000 : ℝ) (12252511193/12500000000 : ℝ) (990100447719/1000000000000 : ℝ) (24752511193/25000000000 : ℝ) (990050955981/1000000000000 : ℝ) (495025477991/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4587/32768 : ℝ)) 1 (990100447719/1000000000000 : ℝ) (24752511193/25000000000 : ℝ) (990050955981/1000000000000 : ℝ) (495025477991/500000000000 : ℝ) (19801514037/20000000000 : ℝ) (990075701851/1000000000000 : ℝ) (49503785077/50000000000 : ℝ) (495037850771/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4587/32768 : ℝ)) 2 (19801514037/20000000000 : ℝ) (990075701851/1000000000000 : ℝ) (49503785077/50000000000 : ℝ) (495037850771/500000000000 : ℝ) (198015140339/200000000000 : ℝ) (990075701697/1000000000000 : ℝ) (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4587/32768 : ℝ)) 3 (198015140339/200000000000 : ℝ) (990075701697/1000000000000 : ℝ) (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ) (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ) (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4587/32768 : ℝ)) 4 (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ) (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ) (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ) (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4587/32768 : ℝ)) 5 (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ) (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ) (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ) (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4587/32768 : ℝ)) 6 (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ) (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ) (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ) (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4587/32768 : ℝ)) 7 (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ) (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ) (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ) (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4587/32768 : ℝ))) (198005567039/1000000000000 : ℝ) (39601113409/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4587/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (198005567039/1000000000000 : ℝ) (39601113409/200000000000 : ℝ) (599002783519/1000000000000 : ℝ) (599002783523/1000000000000 : ℝ) (111244541169/250000000000 : ℝ) (111244541171/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4587/32768 : ℝ))) 1 (599002783519/1000000000000 : ℝ) (599002783523/1000000000000 : ℝ) (111244541169/250000000000 : ℝ) (111244541171/250000000000 : ℝ) (521990474097/1000000000000 : ℝ) (65248809263/125000000000 : ℝ) (258139090049/500000000000 : ℝ) (258139090053/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4587/32768 : ℝ))) 2 (521990474097/1000000000000 : ℝ) (65248809263/125000000000 : ℝ) (258139090049/500000000000 : ℝ) (258139090053/500000000000 : ℝ) (519134327097/1000000000000 : ℝ) (103826865421/200000000000 : ℝ) (103825294027/200000000000 : ℝ) (519126470143/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4587/32768 : ℝ))) 3 (519134327097/1000000000000 : ℝ) (103826865421/200000000000 : ℝ) (103825294027/200000000000 : ℝ) (519126470143/1000000000000 : ℝ) (64891299827/125000000000 : ℝ) (16222824957/31250000000 : ℝ) (519130398601/1000000000000 : ℝ) (51913039861/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4587/32768 : ℝ))) 4 (64891299827/125000000000 : ℝ) (16222824957/31250000000 : ℝ) (519130398601/1000000000000 : ℝ) (51913039861/100000000000 : ℝ) (32445649913/62500000000 : ℝ) (519130398617/1000000000000 : ℝ) (32445649913/62500000000 : ℝ) (519130398617/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4587/32768 : ℝ))) 5 (32445649913/62500000000 : ℝ) (519130398617/1000000000000 : ℝ) (32445649913/62500000000 : ℝ) (519130398617/1000000000000 : ℝ) (32445649913/62500000000 : ℝ) (519130398617/1000000000000 : ℝ) (32445649913/62500000000 : ℝ) (519130398617/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4587/32768 : ℝ))) 6 (32445649913/62500000000 : ℝ) (519130398617/1000000000000 : ℝ) (32445649913/62500000000 : ℝ) (519130398617/1000000000000 : ℝ) (32445649913/62500000000 : ℝ) (519130398617/1000000000000 : ℝ) (32445649913/62500000000 : ℝ) (519130398617/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4587/32768 : ℝ))) 7 (32445649913/62500000000 : ℝ) (519130398617/1000000000000 : ℝ) (32445649913/62500000000 : ℝ) (519130398617/1000000000000 : ℝ) (32445649913/62500000000 : ℝ) (519130398617/1000000000000 : ℝ) (32445649913/62500000000 : ℝ) (519130398617/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4587/32768 : ℝ)) hmem 8 (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ) (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4587/32768 : ℝ))) hcmem 8 (32445649913/62500000000 : ℝ) (519130398617/1000000000000 : ℝ) (32445649913/62500000000 : ℝ) (519130398617/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4587/32768 : ℝ)) (495037850847/500000000000 : ℝ) (990075701697/1000000000000 : ℝ) (32445649913/62500000000 : ℝ) (519130398617/1000000000000 : ℝ) (411810996807/500000000000 : ℝ) (25738187301/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0507_exp_lower
  have heNumeric : (504761933157/250000000000 : ℝ)/4 ≤ Real.exp (-2734673521403/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504761933157/250000000000 : ℝ)/4 ≤ Real.exp ((2293/16384 : ℝ)-(25738187301/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2293/16384 : ℝ) (4587/32768 : ℝ) (25738187301/31250000000 : ℝ) (504761933157/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0508; no trusted numerical premise.
theorem cover7_leaf0508_exp_radius : (997502861471384527/1000000000000000000 : ℝ) ≤ Real.exp ((-1147/57344 : ℝ)/8) ∧ Real.exp ((-1147/57344 : ℝ)/8) ≤ (62343928841961533/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1147/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0508_exp_lower : (918091262780448199/1000000000000000000 : ℝ) ≤ Real.exp ((-1093868524921/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093868524921/1600000000000 : ℝ)/8) ≤ (4590456313902241/5000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093868524921/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0508_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009524423849/500000000000 : ℝ) ≤ 4*Real.exp (4587/32768 : ℝ)*Real.exp (-mu (radius 7 (1147/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (1009524423849/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1147/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0508_exp_radius
  have hrNumeric : (980196622111/1000000000000 : ℝ) ≤ Real.exp (-1147/57344 : ℝ) ∧ Real.exp (-1147/57344 : ℝ) ≤ (30631144441/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980196622111/1000000000000 : ℝ) ≤ (radius 7 (1147/8192 : ℝ)) ∧ (radius 7 (1147/8192 : ℝ)) ≤ (30631144441/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1147/8192 : ℝ)) (980196622111/1000000000000 : ℝ) (30631144441/31250000000 : ℝ) (198026720419/1000000000000 : ℝ) (7921068817/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1147/8192 : ℝ)) (980196622111/1000000000000 : ℝ) (30631144441/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1147/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980196622111/1000000000000 : ℝ) (30631144441/31250000000 : ℝ) (198019662211/200000000000 : ℝ) (61881144441/62500000000 : ℝ) (990048797843/1000000000000 : ℝ) (247512199461/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1147/8192 : ℝ)) 1 (198019662211/200000000000 : ℝ) (61881144441/62500000000 : ℝ) (990048797843/1000000000000 : ℝ) (247512199461/250000000000 : ℝ) (990073554449/1000000000000 : ℝ) (19801471089/20000000000 : ℝ) (990073554139/1000000000000 : ℝ) (990073554141/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1147/8192 : ℝ)) 2 (990073554449/1000000000000 : ℝ) (19801471089/20000000000 : ℝ) (990073554139/1000000000000 : ℝ) (990073554141/1000000000000 : ℝ) (495036777147/500000000000 : ℝ) (123759194287/125000000000 : ℝ) (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1147/8192 : ℝ)) 3 (495036777147/500000000000 : ℝ) (123759194287/125000000000 : ℝ) (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ) (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ) (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1147/8192 : ℝ)) 4 (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ) (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ) (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ) (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1147/8192 : ℝ)) 5 (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ) (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ) (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ) (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1147/8192 : ℝ)) 6 (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ) (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ) (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ) (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1147/8192 : ℝ)) 7 (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ) (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ) (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ) (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1147/8192 : ℝ))) (198026720419/1000000000000 : ℝ) (7921068817/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1147/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (198026720419/1000000000000 : ℝ) (7921068817/40000000000 : ℝ) (599013360209/1000000000000 : ℝ) (599013360213/1000000000000 : ℝ) (8900038661/20000000000 : ℝ) (222500966529/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1147/8192 : ℝ))) 1 (599013360209/1000000000000 : ℝ) (599013360213/1000000000000 : ℝ) (8900038661/20000000000 : ℝ) (222500966529/500000000000 : ℝ) (522007646629/1000000000000 : ℝ) (130501911659/250000000000 : ℝ) (516296526441/1000000000000 : ℝ) (516296526449/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1147/8192 : ℝ))) 2 (522007646629/1000000000000 : ℝ) (130501911659/250000000000 : ℝ) (516296526441/1000000000000 : ℝ) (516296526449/1000000000000 : ℝ) (103830417307/200000000000 : ℝ) (519152086543/1000000000000 : ℝ) (51914423307/100000000000 : ℝ) (259572116539/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1147/8192 : ℝ))) 3 (103830417307/200000000000 : ℝ) (519152086543/1000000000000 : ℝ) (51914423307/100000000000 : ℝ) (259572116539/500000000000 : ℝ) (259574079901/500000000000 : ℝ) (519148159811/1000000000000 : ℝ) (519148159787/1000000000000 : ℝ) (129787039949/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1147/8192 : ℝ))) 4 (259574079901/500000000000 : ℝ) (519148159811/1000000000000 : ℝ) (519148159787/1000000000000 : ℝ) (129787039949/250000000000 : ℝ) (259574079897/500000000000 : ℝ) (129787039951/250000000000 : ℝ) (259574079897/500000000000 : ℝ) (129787039951/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1147/8192 : ℝ))) 5 (259574079897/500000000000 : ℝ) (129787039951/250000000000 : ℝ) (259574079897/500000000000 : ℝ) (129787039951/250000000000 : ℝ) (259574079897/500000000000 : ℝ) (129787039951/250000000000 : ℝ) (259574079897/500000000000 : ℝ) (129787039951/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1147/8192 : ℝ))) 6 (259574079897/500000000000 : ℝ) (129787039951/250000000000 : ℝ) (259574079897/500000000000 : ℝ) (129787039951/250000000000 : ℝ) (259574079897/500000000000 : ℝ) (129787039951/250000000000 : ℝ) (259574079897/500000000000 : ℝ) (129787039951/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1147/8192 : ℝ))) 7 (259574079897/500000000000 : ℝ) (129787039951/250000000000 : ℝ) (259574079897/500000000000 : ℝ) (129787039951/250000000000 : ℝ) (259574079897/500000000000 : ℝ) (129787039951/250000000000 : ℝ) (259574079897/500000000000 : ℝ) (129787039951/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1147/8192 : ℝ)) hmem 8 (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ) (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1147/8192 : ℝ))) hcmem 8 (259574079897/500000000000 : ℝ) (129787039951/250000000000 : ℝ) (259574079897/500000000000 : ℝ) (129787039951/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1147/8192 : ℝ)) (990073554293/1000000000000 : ℝ) (123759194287/125000000000 : ℝ) (259574079897/500000000000 : ℝ) (129787039951/250000000000 : ℝ) (164730391783/200000000000 : ℝ) (164730391787/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0508_exp_lower
  have heNumeric : (1009524423849/500000000000 : ℝ)/4 ≤ Real.exp (-1093868524921/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009524423849/500000000000 : ℝ)/4 ≤ Real.exp ((4587/32768 : ℝ)-(164730391787/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4587/32768 : ℝ) (1147/8192 : ℝ) (164730391787/200000000000 : ℝ) (1009524423849/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0509; no trusted numerical premise.
theorem cover7_leaf0509_exp_radius : (199500463575122583/200000000000000000 : ℝ) ≤ Real.exp ((-4589/229376 : ℝ)/8) ∧ Real.exp ((-4589/229376 : ℝ)/8) ≤ (249375579468903229/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4589/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0509_exp_lower : (183618265332159157/200000000000000000 : ℝ) ≤ Real.exp ((-1367334542879/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367334542879/2000000000000 : ℝ)/8) ≤ (459045663330397893/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367334542879/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0509_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009524985787/500000000000 : ℝ) ≤ 4*Real.exp (1147/8192 : ℝ)*Real.exp (-mu (radius 7 (4589/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009524985787/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4589/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0509_exp_radius
  have hrNumeric : (980192348803/1000000000000 : ℝ) ≤ Real.exp (-4589/229376 : ℝ) ∧ Real.exp (-4589/229376 : ℝ) ≤ (245048087201/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980192348803/1000000000000 : ℝ) ≤ (radius 7 (4589/32768 : ℝ)) ∧ (radius 7 (4589/32768 : ℝ)) ≤ (245048087201/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4589/32768 : ℝ)) (980192348803/1000000000000 : ℝ) (245048087201/250000000000 : ℝ) (198047871349/1000000000000 : ℝ) (39609574271/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4589/32768 : ℝ)) (980192348803/1000000000000 : ℝ) (245048087201/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4589/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980192348803/1000000000000 : ℝ) (245048087201/250000000000 : ℝ) (990096174401/1000000000000 : ℝ) (495048087201/500000000000 : ℝ) (99004663971/100000000000 : ℝ) (30938957491/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4589/32768 : ℝ)) 1 (990096174401/1000000000000 : ℝ) (495048087201/500000000000 : ℝ) (99004663971/100000000000 : ℝ) (30938957491/31250000000 : ℝ) (198014281411/200000000000 : ℝ) (990071407057/1000000000000 : ℝ) (198014281349/200000000000 : ℝ) (247517851687/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4589/32768 : ℝ)) 2 (198014281411/200000000000 : ℝ) (990071407057/1000000000000 : ℝ) (198014281349/200000000000 : ℝ) (247517851687/250000000000 : ℝ) (9900714069/10000000000 : ℝ) (990071406903/1000000000000 : ℝ) (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4589/32768 : ℝ)) 3 (9900714069/10000000000 : ℝ) (990071406903/1000000000000 : ℝ) (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ) (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ) (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4589/32768 : ℝ)) 4 (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ) (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ) (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ) (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4589/32768 : ℝ)) 5 (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ) (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ) (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ) (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4589/32768 : ℝ)) 6 (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ) (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ) (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ) (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4589/32768 : ℝ)) 7 (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ) (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ) (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ) (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4589/32768 : ℝ))) (198047871349/1000000000000 : ℝ) (39609574271/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4589/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (198047871349/1000000000000 : ℝ) (39609574271/200000000000 : ℝ) (299511967837/500000000000 : ℝ) (299511967839/500000000000 : ℝ) (222512848701/500000000000 : ℝ) (44502569741/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4589/32768 : ℝ))) 1 (299511967837/500000000000 : ℝ) (299511967839/500000000000 : ℝ) (222512848701/500000000000 : ℝ) (44502569741/100000000000 : ℝ) (261012408269/500000000000 : ℝ) (16313275517/31250000000 : ℝ) (258157434879/500000000000 : ℝ) (103262973953/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4589/32768 : ℝ))) 2 (261012408269/500000000000 : ℝ) (16313275517/31250000000 : ℝ) (258157434879/500000000000 : ℝ) (103262973953/200000000000 : ℝ) (129792460787/250000000000 : ℝ) (103833968631/200000000000 : ℝ) (259580996589/500000000000 : ℝ) (259580996593/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4589/32768 : ℝ))) 3 (129792460787/250000000000 : ℝ) (103833968631/200000000000 : ℝ) (259580996589/500000000000 : ℝ) (259580996593/500000000000 : ℝ) (519165918163/1000000000000 : ℝ) (519165918171/1000000000000 : ℝ) (129791479537/250000000000 : ℝ) (129791479539/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4589/32768 : ℝ))) 4 (519165918163/1000000000000 : ℝ) (519165918171/1000000000000 : ℝ) (129791479537/250000000000 : ℝ) (129791479539/250000000000 : ℝ) (103833183631/200000000000 : ℝ) (129791479541/250000000000 : ℝ) (103833183631/200000000000 : ℝ) (129791479541/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4589/32768 : ℝ))) 5 (103833183631/200000000000 : ℝ) (129791479541/250000000000 : ℝ) (103833183631/200000000000 : ℝ) (129791479541/250000000000 : ℝ) (103833183631/200000000000 : ℝ) (129791479541/250000000000 : ℝ) (103833183631/200000000000 : ℝ) (129791479541/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4589/32768 : ℝ))) 6 (103833183631/200000000000 : ℝ) (129791479541/250000000000 : ℝ) (103833183631/200000000000 : ℝ) (129791479541/250000000000 : ℝ) (103833183631/200000000000 : ℝ) (129791479541/250000000000 : ℝ) (103833183631/200000000000 : ℝ) (129791479541/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4589/32768 : ℝ))) 7 (103833183631/200000000000 : ℝ) (129791479541/250000000000 : ℝ) (103833183631/200000000000 : ℝ) (129791479541/250000000000 : ℝ) (103833183631/200000000000 : ℝ) (129791479541/250000000000 : ℝ) (103833183631/200000000000 : ℝ) (129791479541/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4589/32768 : ℝ)) hmem 8 (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ) (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4589/32768 : ℝ))) hcmem 8 (103833183631/200000000000 : ℝ) (129791479541/250000000000 : ℝ) (103833183631/200000000000 : ℝ) (129791479541/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4589/32768 : ℝ)) (990071406899/1000000000000 : ℝ) (990071406903/1000000000000 : ℝ) (103833183631/200000000000 : ℝ) (129791479541/250000000000 : ℝ) (411840959929/500000000000 : ℝ) (823681919877/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0509_exp_lower
  have heNumeric : (1009524985787/500000000000 : ℝ)/4 ≤ Real.exp (-1367334542879/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009524985787/500000000000 : ℝ)/4 ≤ Real.exp ((1147/8192 : ℝ)-(823681919877/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1147/8192 : ℝ) (4589/32768 : ℝ) (823681919877/1000000000000 : ℝ) (1009524985787/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0510; no trusted numerical premise.
theorem cover7_leaf0510_exp_radius : (49875088714006877/50000000000000000 : ℝ) ≤ Real.exp ((-2295/114688 : ℝ)/8) ∧ Real.exp ((-2295/114688 : ℝ)/8) ≤ (997501774280137541/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2295/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0510_exp_lower : (229522847759803099/250000000000000000 : ℝ) ≤ Real.exp ((-5469333683707/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469333683707/8000000000000 : ℝ)/8) ≤ (918091391039212397/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469333683707/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0510_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019051104213/1000000000000 : ℝ) ≤ 4*Real.exp (4589/32768 : ℝ)*Real.exp (-mu (radius 7 (2295/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019051104213/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2295/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0510_exp_radius
  have hrNumeric : (122523509439/125000000000 : ℝ) ≤ Real.exp (-2295/114688 : ℝ) ∧ Real.exp (-2295/114688 : ℝ) ≤ (980188075513/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122523509439/125000000000 : ℝ) ≤ (radius 7 (2295/16384 : ℝ)) ∧ (radius 7 (2295/16384 : ℝ)) ≤ (980188075513/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2295/16384 : ℝ)) (122523509439/125000000000 : ℝ) (980188075513/1000000000000 : ℝ) (49517254961/250000000000 : ℝ) (3961380397/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2295/16384 : ℝ)) (122523509439/125000000000 : ℝ) (980188075513/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2295/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122523509439/125000000000 : ℝ) (980188075513/1000000000000 : ℝ) (247523509439/250000000000 : ℝ) (990094037757/1000000000000 : ℝ) (495022240791/500000000000 : ℝ) (61877780099/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2295/16384 : ℝ)) 1 (247523509439/250000000000 : ℝ) (990094037757/1000000000000 : ℝ) (495022240791/500000000000 : ℝ) (61877780099/62500000000 : ℝ) (990069259669/1000000000000 : ℝ) (990069259671/1000000000000 : ℝ) (495034629679/500000000000 : ℝ) (990069259361/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2295/16384 : ℝ)) 2 (990069259669/1000000000000 : ℝ) (990069259671/1000000000000 : ℝ) (495034629679/500000000000 : ℝ) (990069259361/1000000000000 : ℝ) (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ) (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2295/16384 : ℝ)) 3 (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ) (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ) (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ) (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2295/16384 : ℝ)) 4 (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ) (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ) (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ) (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2295/16384 : ℝ)) 5 (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ) (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ) (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ) (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2295/16384 : ℝ)) 6 (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ) (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ) (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ) (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2295/16384 : ℝ)) 7 (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ) (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ) (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ) (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2295/16384 : ℝ))) (49517254961/250000000000 : ℝ) (3961380397/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2295/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49517254961/250000000000 : ℝ) (3961380397/20000000000 : ℝ) (299517254961/500000000000 : ℝ) (23961380397/40000000000 : ℝ) (1780197831/4000000000 : ℝ) (222524728879/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2295/16384 : ℝ))) 1 (299517254961/500000000000 : ℝ) (23961380397/40000000000 : ℝ) (1780197831/4000000000 : ℝ) (222524728879/500000000000 : ℝ) (130510495959/250000000000 : ℝ) (261020991921/500000000000 : ℝ) (516333210063/1000000000000 : ℝ) (51633321007/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2295/16384 : ℝ))) 2 (130510495959/250000000000 : ℝ) (261020991921/500000000000 : ℝ) (516333210063/1000000000000 : ℝ) (51633321007/100000000000 : ℝ) (519187596949/1000000000000 : ℝ) (129796899239/250000000000 : ℝ) (519179750473/1000000000000 : ℝ) (6489746881/12500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2295/16384 : ℝ))) 3 (519187596949/1000000000000 : ℝ) (129796899239/250000000000 : ℝ) (519179750473/1000000000000 : ℝ) (6489746881/12500000000 : ℝ) (519183673711/1000000000000 : ℝ) (259591836859/500000000000 : ℝ) (16224489803/31250000000 : ℝ) (64897959213/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2295/16384 : ℝ))) 4 (519183673711/1000000000000 : ℝ) (259591836859/500000000000 : ℝ) (16224489803/31250000000 : ℝ) (64897959213/125000000000 : ℝ) (519183673703/1000000000000 : ℝ) (519183673711/1000000000000 : ℝ) (519183673703/1000000000000 : ℝ) (519183673711/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2295/16384 : ℝ))) 5 (519183673703/1000000000000 : ℝ) (519183673711/1000000000000 : ℝ) (519183673703/1000000000000 : ℝ) (519183673711/1000000000000 : ℝ) (519183673703/1000000000000 : ℝ) (519183673711/1000000000000 : ℝ) (519183673703/1000000000000 : ℝ) (519183673711/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2295/16384 : ℝ))) 6 (519183673703/1000000000000 : ℝ) (519183673711/1000000000000 : ℝ) (519183673703/1000000000000 : ℝ) (519183673711/1000000000000 : ℝ) (519183673703/1000000000000 : ℝ) (519183673711/1000000000000 : ℝ) (519183673703/1000000000000 : ℝ) (519183673711/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2295/16384 : ℝ))) 7 (519183673703/1000000000000 : ℝ) (519183673711/1000000000000 : ℝ) (519183673703/1000000000000 : ℝ) (519183673711/1000000000000 : ℝ) (519183673703/1000000000000 : ℝ) (519183673711/1000000000000 : ℝ) (519183673703/1000000000000 : ℝ) (519183673711/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2295/16384 : ℝ)) hmem 8 (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ) (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2295/16384 : ℝ))) hcmem 8 (519183673703/1000000000000 : ℝ) (519183673711/1000000000000 : ℝ) (519183673703/1000000000000 : ℝ) (519183673711/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2295/16384 : ℝ)) (990069259513/1000000000000 : ℝ) (247517314879/250000000000 : ℝ) (519183673703/1000000000000 : ℝ) (519183673711/1000000000000 : ℝ) (823711876463/1000000000000 : ℝ) (823711876479/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0510_exp_lower
  have heNumeric : (2019051104213/1000000000000 : ℝ)/4 ≤ Real.exp (-5469333683707/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019051104213/1000000000000 : ℝ)/4 ≤ Real.exp ((4589/32768 : ℝ)-(823711876479/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4589/32768 : ℝ) (2295/16384 : ℝ) (823711876479/1000000000000 : ℝ) (2019051104213/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0511; no trusted numerical premise.
theorem cover7_leaf0511_exp_radius : (623438269178099/625000000000000 : ℝ) ≤ Real.exp ((-4591/229376 : ℝ)/8) ∧ Real.exp ((-4591/229376 : ℝ)/8) ≤ (997501230684958401/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4591/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0511_exp_lower : (183618291183460959/200000000000000000 : ℝ) ≤ Real.exp ((-2734664580533/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734664580533/4000000000000 : ℝ)/8) ≤ (229522863979326199/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734664580533/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0511_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504763061411/250000000000 : ℝ) ≤ 4*Real.exp (2295/16384 : ℝ)*Real.exp (-mu (radius 7 (4591/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (504763061411/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4591/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0511_exp_radius
  have hrNumeric : (980183802241/1000000000000 : ℝ) ≤ Real.exp (-4591/229376 : ℝ) ∧ Real.exp (-4591/229376 : ℝ) ≤ (490091901121/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980183802241/1000000000000 : ℝ) ≤ (radius 7 (4591/32768 : ℝ)) ∧ (radius 7 (4591/32768 : ℝ)) ≤ (490091901121/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4591/32768 : ℝ)) (980183802241/1000000000000 : ℝ) (490091901121/500000000000 : ℝ) (19809016589/100000000000 : ℝ) (24761270737/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4591/32768 : ℝ)) (980183802241/1000000000000 : ℝ) (490091901121/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4591/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980183802241/1000000000000 : ℝ) (490091901121/500000000000 : ℝ) (3094037191/3125000000 : ℝ) (990091901121/1000000000000 : ℝ) (990042323459/1000000000000 : ℝ) (49502116173/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4591/32768 : ℝ)) 1 (3094037191/3125000000 : ℝ) (990091901121/1000000000000 : ℝ) (990042323459/1000000000000 : ℝ) (49502116173/50000000000 : ℝ) (990067112289/1000000000000 : ℝ) (990067112291/1000000000000 : ℝ) (990067111979/1000000000000 : ℝ) (990067111981/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4591/32768 : ℝ)) 2 (990067112289/1000000000000 : ℝ) (990067112291/1000000000000 : ℝ) (990067111979/1000000000000 : ℝ) (990067111981/1000000000000 : ℝ) (495033556067/500000000000 : ℝ) (123758389017/125000000000 : ℝ) (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4591/32768 : ℝ)) 3 (495033556067/500000000000 : ℝ) (123758389017/125000000000 : ℝ) (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ) (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ) (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4591/32768 : ℝ)) 4 (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ) (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ) (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ) (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4591/32768 : ℝ)) 5 (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ) (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ) (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ) (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4591/32768 : ℝ)) 6 (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ) (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ) (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ) (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4591/32768 : ℝ)) 7 (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ) (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ) (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ) (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4591/32768 : ℝ))) (19809016589/100000000000 : ℝ) (24761270737/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4591/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19809016589/100000000000 : ℝ) (24761270737/125000000000 : ℝ) (119809016589/200000000000 : ℝ) (149761270737/250000000000 : ℝ) (222536607039/500000000000 : ℝ) (222536607043/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4591/32768 : ℝ))) 1 (119809016589/200000000000 : ℝ) (149761270737/250000000000 : ℝ) (222536607039/500000000000 : ℝ) (222536607043/500000000000 : ℝ) (522059148511/1000000000000 : ℝ) (522059148517/1000000000000 : ℝ) (516351547343/1000000000000 : ℝ) (10327030947/20000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4591/32768 : ℝ))) 2 (522059148511/1000000000000 : ℝ) (522059148517/1000000000000 : ℝ) (516351547343/1000000000000 : ℝ) (10327030947/20000000000 : ℝ) (519205347927/1000000000000 : ℝ) (259602673967/500000000000 : ℝ) (259598752471/500000000000 : ℝ) (519197504949/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4591/32768 : ℝ))) 3 (519205347927/1000000000000 : ℝ) (259602673967/500000000000 : ℝ) (259598752471/500000000000 : ℝ) (519197504949/1000000000000 : ℝ) (259600713217/500000000000 : ℝ) (259600713221/500000000000 : ℝ) (519201426419/1000000000000 : ℝ) (519201426427/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4591/32768 : ℝ))) 4 (259600713217/500000000000 : ℝ) (259600713221/500000000000 : ℝ) (519201426419/1000000000000 : ℝ) (519201426427/1000000000000 : ℝ) (259600713213/500000000000 : ℝ) (103840285287/200000000000 : ℝ) (259600713213/500000000000 : ℝ) (103840285287/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4591/32768 : ℝ))) 5 (259600713213/500000000000 : ℝ) (103840285287/200000000000 : ℝ) (259600713213/500000000000 : ℝ) (103840285287/200000000000 : ℝ) (259600713213/500000000000 : ℝ) (103840285287/200000000000 : ℝ) (259600713213/500000000000 : ℝ) (103840285287/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4591/32768 : ℝ))) 6 (259600713213/500000000000 : ℝ) (103840285287/200000000000 : ℝ) (259600713213/500000000000 : ℝ) (103840285287/200000000000 : ℝ) (259600713213/500000000000 : ℝ) (103840285287/200000000000 : ℝ) (259600713213/500000000000 : ℝ) (103840285287/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4591/32768 : ℝ))) 7 (259600713213/500000000000 : ℝ) (103840285287/200000000000 : ℝ) (259600713213/500000000000 : ℝ) (103840285287/200000000000 : ℝ) (259600713213/500000000000 : ℝ) (103840285287/200000000000 : ℝ) (259600713213/500000000000 : ℝ) (103840285287/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4591/32768 : ℝ)) hmem 8 (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ) (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4591/32768 : ℝ))) hcmem 8 (259600713213/500000000000 : ℝ) (103840285287/200000000000 : ℝ) (259600713213/500000000000 : ℝ) (103840285287/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4591/32768 : ℝ)) (990067112133/1000000000000 : ℝ) (123758389017/125000000000 : ℝ) (259600713213/500000000000 : ℝ) (103840285287/200000000000 : ℝ) (82374182871/100000000000 : ℝ) (823741828727/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0511_exp_lower
  have heNumeric : (504763061411/250000000000 : ℝ)/4 ≤ Real.exp (-2734664580533/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504763061411/250000000000 : ℝ)/4 ≤ Real.exp ((2295/16384 : ℝ)-(823741828727/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2295/16384 : ℝ) (4591/32768 : ℝ) (823741828727/1000000000000 : ℝ) (504763061411/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0512; no trusted numerical premise.
theorem cover7_leaf0512_exp_radius : (124687585886259437/125000000000000000 : ℝ) ≤ Real.exp ((-41/2048 : ℝ)/8) ∧ Real.exp ((-41/2048 : ℝ)/8) ≤ (997500687090075497/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-41/2048 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0512_exp_lower : (36723660851757019/40000000000000000 : ℝ) ≤ Real.exp ((-5469324603673/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469324603673/8000000000000 : ℝ)/8) ≤ (229522880323481369/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469324603673/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0512_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009526697923/500000000000 : ℝ) ≤ 4*Real.exp (4591/32768 : ℝ)*Real.exp (-mu (radius 7 (287/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (1009526697923/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (287/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0512_exp_radius
  have hrNumeric : (245044882247/250000000000 : ℝ) ≤ Real.exp (-41/2048 : ℝ) ∧ Real.exp (-41/2048 : ℝ) ≤ (980179528989/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245044882247/250000000000 : ℝ) ≤ (radius 7 (287/2048 : ℝ)) ∧ (radius 7 (287/2048 : ℝ)) ≤ (980179528989/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (287/2048 : ℝ)) (245044882247/250000000000 : ℝ) (980179528989/1000000000000 : ℝ) (198111309497/1000000000000 : ℝ) (198111309503/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (287/2048 : ℝ)) (245044882247/250000000000 : ℝ) (980179528989/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (287/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245044882247/250000000000 : ℝ) (980179528989/1000000000000 : ℝ) (495044882247/500000000000 : ℝ) (198017952899/200000000000 : ℝ) (49502008267/50000000000 : ℝ) (495020082671/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (287/2048 : ℝ)) 1 (495044882247/500000000000 : ℝ) (198017952899/200000000000 : ℝ) (49502008267/50000000000 : ℝ) (495020082671/500000000000 : ℝ) (990064964917/1000000000000 : ℝ) (990064964919/1000000000000 : ℝ) (495032482303/500000000000 : ℝ) (966860317/976562500 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (287/2048 : ℝ)) 2 (990064964917/1000000000000 : ℝ) (990064964919/1000000000000 : ℝ) (495032482303/500000000000 : ℝ) (966860317/976562500 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (287/2048 : ℝ)) 3 (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (287/2048 : ℝ)) 4 (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (287/2048 : ℝ)) 5 (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (287/2048 : ℝ)) 6 (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (287/2048 : ℝ)) 7 (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (287/2048 : ℝ))) (198111309497/1000000000000 : ℝ) (198111309503/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (287/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (198111309497/1000000000000 : ℝ) (198111309503/1000000000000 : ℝ) (149763913687/250000000000 : ℝ) (18720489211/31250000000 : ℝ) (222548483199/500000000000 : ℝ) (222548483203/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (287/2048 : ℝ))) 1 (149763913687/250000000000 : ℝ) (18720489211/31250000000 : ℝ) (222548483199/500000000000 : ℝ) (222548483203/500000000000 : ℝ) (522076310573/1000000000000 : ℝ) (522076310579/1000000000000 : ℝ) (64546235201/125000000000 : ℝ) (103273976323/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (287/2048 : ℝ))) 2 (522076310573/1000000000000 : ℝ) (522076310579/1000000000000 : ℝ) (64546235201/125000000000 : ℝ) (103273976323/200000000000 : ℝ) (51922309609/100000000000 : ℝ) (519223096097/1000000000000 : ℝ) (259607628297/500000000000 : ℝ) (259607628301/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (287/2048 : ℝ))) 3 (51922309609/100000000000 : ℝ) (519223096097/1000000000000 : ℝ) (259607628297/500000000000 : ℝ) (259607628301/500000000000 : ℝ) (259609588171/500000000000 : ℝ) (10384383527/20000000000 : ℝ) (519219176327/1000000000000 : ℝ) (103843835267/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (287/2048 : ℝ))) 4 (259609588171/500000000000 : ℝ) (10384383527/20000000000 : ℝ) (519219176327/1000000000000 : ℝ) (103843835267/200000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (287/2048 : ℝ))) 5 (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (287/2048 : ℝ))) 6 (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (287/2048 : ℝ))) 7 (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (287/2048 : ℝ)) hmem 8 (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (287/2048 : ℝ))) hcmem 8 (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (287/2048 : ℝ)) (990064964761/1000000000000 : ℝ) (247516241191/250000000000 : ℝ) (259609588167/500000000000 : ℝ) (519219176343/1000000000000 : ℝ) (411885888307/500000000000 : ℝ) (823771776631/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0512_exp_lower
  have heNumeric : (1009526697923/500000000000 : ℝ)/4 ≤ Real.exp (-5469324603673/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009526697923/500000000000 : ℝ)/4 ≤ Real.exp ((4591/32768 : ℝ)-(823771776631/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4591/32768 : ℝ) (287/2048 : ℝ) (823771776631/1000000000000 : ℝ) (1009526697923/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0513; no trusted numerical premise.
theorem cover7_leaf0513_exp_radius : (249375035873872207/250000000000000000 : ℝ) ≤ Real.exp ((-4593/229376 : ℝ)/8) ∧ Real.exp ((-4593/229376 : ℝ)/8) ≤ (997500143495488829/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4593/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0513_exp_lower : (459045793584652033/500000000000000000 : ℝ) ≤ Real.exp ((-683665001439/1000000000000 : ℝ)/8) ∧ Real.exp ((-683665001439/1000000000000 : ℝ)/8) ≤ (918091587169304067/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683665001439/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0513_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252381819353/125000000000 : ℝ) ≤ 4*Real.exp (287/2048 : ℝ)*Real.exp (-mu (radius 7 (4593/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (252381819353/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4593/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0513_exp_radius
  have hrNumeric : (490087627877/500000000000 : ℝ) ≤ Real.exp (-4593/229376 : ℝ) ∧ Real.exp (-4593/229376 : ℝ) ≤ (196035051151/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490087627877/500000000000 : ℝ) ≤ (radius 7 (4593/32768 : ℝ)) ∧ (radius 7 (4593/32768 : ℝ)) ≤ (196035051151/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4593/32768 : ℝ)) (490087627877/500000000000 : ℝ) (196035051151/200000000000 : ℝ) (99066225331/500000000000 : ℝ) (49533112667/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4593/32768 : ℝ)) (490087627877/500000000000 : ℝ) (196035051151/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4593/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490087627877/500000000000 : ℝ) (196035051151/200000000000 : ℝ) (990087627877/1000000000000 : ℝ) (495043813939/500000000000 : ℝ) (495019003613/500000000000 : ℝ) (247509501807/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4593/32768 : ℝ)) 1 (990087627877/1000000000000 : ℝ) (495043813939/500000000000 : ℝ) (495019003613/500000000000 : ℝ) (247509501807/250000000000 : ℝ) (990062817551/1000000000000 : ℝ) (990062817553/1000000000000 : ℝ) (24751570431/25000000000 : ℝ) (990062817243/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4593/32768 : ℝ)) 2 (990062817551/1000000000000 : ℝ) (990062817553/1000000000000 : ℝ) (24751570431/25000000000 : ℝ) (990062817243/1000000000000 : ℝ) (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ) (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4593/32768 : ℝ)) 3 (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ) (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ) (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ) (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4593/32768 : ℝ)) 4 (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ) (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ) (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ) (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4593/32768 : ℝ)) 5 (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ) (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ) (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ) (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4593/32768 : ℝ)) 6 (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ) (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ) (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ) (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4593/32768 : ℝ)) 7 (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ) (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ) (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ) (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4593/32768 : ℝ))) (99066225331/500000000000 : ℝ) (49533112667/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4593/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (99066225331/500000000000 : ℝ) (49533112667/250000000000 : ℝ) (599066225331/1000000000000 : ℝ) (299533112667/500000000000 : ℝ) (445120714707/1000000000000 : ℝ) (89024142943/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4593/32768 : ℝ))) 1 (599066225331/1000000000000 : ℝ) (299533112667/500000000000 : ℝ) (445120714707/1000000000000 : ℝ) (89024142943/200000000000 : ℝ) (522093470019/1000000000000 : ℝ) (20883738801/40000000000 : ℝ) (103277642571/200000000000 : ℝ) (258194106431/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4593/32768 : ℝ))) 2 (522093470019/1000000000000 : ℝ) (20883738801/40000000000 : ℝ) (103277642571/200000000000 : ℝ) (258194106431/500000000000 : ℝ) (519240841437/1000000000000 : ℝ) (129810210361/250000000000 : ℝ) (129808251357/250000000000 : ℝ) (129808251359/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4593/32768 : ℝ))) 3 (519240841437/1000000000000 : ℝ) (129810210361/250000000000 : ℝ) (129808251357/250000000000 : ℝ) (129808251359/250000000000 : ℝ) (64904615429/125000000000 : ℝ) (6490461543/12500000000 : ℝ) (519236923417/1000000000000 : ℝ) (259618461713/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4593/32768 : ℝ))) 4 (64904615429/125000000000 : ℝ) (6490461543/12500000000 : ℝ) (519236923417/1000000000000 : ℝ) (259618461713/500000000000 : ℝ) (16226153857/31250000000 : ℝ) (519236923433/1000000000000 : ℝ) (16226153857/31250000000 : ℝ) (519236923433/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4593/32768 : ℝ))) 5 (16226153857/31250000000 : ℝ) (519236923433/1000000000000 : ℝ) (16226153857/31250000000 : ℝ) (519236923433/1000000000000 : ℝ) (16226153857/31250000000 : ℝ) (519236923433/1000000000000 : ℝ) (16226153857/31250000000 : ℝ) (519236923433/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4593/32768 : ℝ))) 6 (16226153857/31250000000 : ℝ) (519236923433/1000000000000 : ℝ) (16226153857/31250000000 : ℝ) (519236923433/1000000000000 : ℝ) (16226153857/31250000000 : ℝ) (519236923433/1000000000000 : ℝ) (16226153857/31250000000 : ℝ) (519236923433/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4593/32768 : ℝ))) 7 (16226153857/31250000000 : ℝ) (519236923433/1000000000000 : ℝ) (16226153857/31250000000 : ℝ) (519236923433/1000000000000 : ℝ) (16226153857/31250000000 : ℝ) (519236923433/1000000000000 : ℝ) (16226153857/31250000000 : ℝ) (519236923433/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4593/32768 : ℝ)) hmem 8 (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ) (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4593/32768 : ℝ))) hcmem 8 (16226153857/31250000000 : ℝ) (519236923433/1000000000000 : ℝ) (16226153857/31250000000 : ℝ) (519236923433/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4593/32768 : ℝ)) (198012563479/200000000000 : ℝ) (495031408699/500000000000 : ℝ) (16226153857/31250000000 : ℝ) (519236923433/1000000000000 : ℝ) (823801720171/1000000000000 : ℝ) (823801720189/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0513_exp_lower
  have heNumeric : (252381819353/125000000000 : ℝ)/4 ≤ Real.exp (-683665001439/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252381819353/125000000000 : ℝ)/4 ≤ Real.exp ((287/2048 : ℝ)-(823801720189/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (287/2048 : ℝ) (4593/32768 : ℝ) (823801720189/1000000000000 : ℝ) (252381819353/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0514; no trusted numerical premise.
theorem cover7_leaf0514_exp_radius : (249374899975299599/250000000000000000 : ℝ) ≤ Real.exp ((-2297/114688 : ℝ)/8) ∧ Real.exp ((-2297/114688 : ℝ)/8) ≤ (997499599901198397/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2297/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0514_exp_lower : (918091653542637343/1000000000000000000 : ℝ) ≤ Real.exp ((-5469315384639/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469315384639/8000000000000 : ℝ)/8) ≤ (28690364173207417/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469315384639/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0514_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019055722563/1000000000000 : ℝ) ≤ 4*Real.exp (4593/32768 : ℝ)*Real.exp (-mu (radius 7 (2297/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019055722563/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2297/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0514_exp_radius
  have hrNumeric : (490085491269/500000000000 : ℝ) ≤ Real.exp (-2297/114688 : ℝ) ∧ Real.exp (-2297/114688 : ℝ) ≤ (980170982539/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490085491269/500000000000 : ℝ) ≤ (radius 7 (2297/16384 : ℝ)) ∧ (radius 7 (2297/16384 : ℝ)) ≤ (980170982539/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2297/16384 : ℝ)) (490085491269/500000000000 : ℝ) (980170982539/1000000000000 : ℝ) (19815358939/100000000000 : ℝ) (49538397349/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2297/16384 : ℝ)) (490085491269/500000000000 : ℝ) (980170982539/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2297/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490085491269/500000000000 : ℝ) (980170982539/1000000000000 : ℝ) (990085491269/1000000000000 : ℝ) (99008549127/100000000000 : ℝ) (990035849117/1000000000000 : ℝ) (990035849119/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2297/16384 : ℝ)) 1 (990085491269/1000000000000 : ℝ) (99008549127/100000000000 : ℝ) (990035849117/1000000000000 : ℝ) (990035849119/1000000000000 : ℝ) (990060670193/1000000000000 : ℝ) (198012134039/200000000000 : ℝ) (990060669881/1000000000000 : ℝ) (247515167471/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2297/16384 : ℝ)) 2 (990060670193/1000000000000 : ℝ) (198012134039/200000000000 : ℝ) (990060669881/1000000000000 : ℝ) (247515167471/250000000000 : ℝ) (990060670037/1000000000000 : ℝ) (24751516751/25000000000 : ℝ) (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2297/16384 : ℝ)) 3 (990060670037/1000000000000 : ℝ) (24751516751/25000000000 : ℝ) (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ) (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ) (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2297/16384 : ℝ)) 4 (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ) (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ) (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ) (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2297/16384 : ℝ)) 5 (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ) (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ) (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ) (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2297/16384 : ℝ)) 6 (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ) (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ) (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ) (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2297/16384 : ℝ)) 7 (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ) (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ) (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ) (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2297/16384 : ℝ))) (19815358939/100000000000 : ℝ) (49538397349/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2297/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19815358939/100000000000 : ℝ) (49538397349/250000000000 : ℝ) (119815358939/200000000000 : ℝ) (299538397349/500000000000 : ℝ) (445144459013/1000000000000 : ℝ) (22257222951/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2297/16384 : ℝ))) 1 (119815358939/200000000000 : ℝ) (299538397349/500000000000 : ℝ) (445144459013/1000000000000 : ℝ) (22257222951/50000000000 : ℝ) (261055313427/500000000000 : ℝ) (522110626859/1000000000000 : ℝ) (516406541091/1000000000000 : ℝ) (516406541097/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2297/16384 : ℝ))) 2 (261055313427/500000000000 : ℝ) (522110626859/1000000000000 : ℝ) (516406541091/1000000000000 : ℝ) (516406541097/1000000000000 : ℝ) (129814645993/250000000000 : ℝ) (259629291989/500000000000 : ℝ) (519250751449/1000000000000 : ℝ) (103850150291/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2297/16384 : ℝ))) 3 (129814645993/250000000000 : ℝ) (259629291989/500000000000 : ℝ) (519250751449/1000000000000 : ℝ) (103850150291/200000000000 : ℝ) (51925466771/100000000000 : ℝ) (519254667717/1000000000000 : ℝ) (103850933539/200000000000 : ℝ) (259627333851/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2297/16384 : ℝ))) 4 (51925466771/100000000000 : ℝ) (519254667717/1000000000000 : ℝ) (103850933539/200000000000 : ℝ) (259627333851/500000000000 : ℝ) (259627333851/500000000000 : ℝ) (51925466771/100000000000 : ℝ) (259627333851/500000000000 : ℝ) (51925466771/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2297/16384 : ℝ))) 5 (259627333851/500000000000 : ℝ) (51925466771/100000000000 : ℝ) (259627333851/500000000000 : ℝ) (51925466771/100000000000 : ℝ) (259627333851/500000000000 : ℝ) (51925466771/100000000000 : ℝ) (259627333851/500000000000 : ℝ) (51925466771/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2297/16384 : ℝ))) 6 (259627333851/500000000000 : ℝ) (51925466771/100000000000 : ℝ) (259627333851/500000000000 : ℝ) (51925466771/100000000000 : ℝ) (259627333851/500000000000 : ℝ) (51925466771/100000000000 : ℝ) (259627333851/500000000000 : ℝ) (51925466771/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2297/16384 : ℝ))) 7 (259627333851/500000000000 : ℝ) (51925466771/100000000000 : ℝ) (259627333851/500000000000 : ℝ) (51925466771/100000000000 : ℝ) (259627333851/500000000000 : ℝ) (51925466771/100000000000 : ℝ) (259627333851/500000000000 : ℝ) (51925466771/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2297/16384 : ℝ)) hmem 8 (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ) (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2297/16384 : ℝ))) hcmem 8 (259627333851/500000000000 : ℝ) (51925466771/100000000000 : ℝ) (259627333851/500000000000 : ℝ) (51925466771/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2297/16384 : ℝ)) (247515167509/250000000000 : ℝ) (24751516751/25000000000 : ℝ) (259627333851/500000000000 : ℝ) (51925466771/100000000000 : ℝ) (823831659391/1000000000000 : ℝ) (51489478713/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0514_exp_lower
  have heNumeric : (2019055722563/1000000000000 : ℝ)/4 ≤ Real.exp (-5469315384639/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019055722563/1000000000000 : ℝ)/4 ≤ Real.exp ((4593/32768 : ℝ)-(51489478713/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4593/32768 : ℝ) (2297/16384 : ℝ) (51489478713/62500000000 : ℝ) (2019055722563/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0515; no trusted numerical premise.
theorem cover7_leaf0515_exp_radius : (498749528153602099/500000000000000000 : ℝ) ≤ Real.exp ((-4595/229376 : ℝ)/8) ∧ Real.exp ((-4595/229376 : ℝ)/8) ≤ (997499056307204199/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4595/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0515_exp_lower : (918091720414384461/1000000000000000000 : ℝ) ≤ Real.exp ((-2734655361511/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734655361511/4000000000000 : ℝ)/8) ≤ (459045860207192231/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734655361511/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0515_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019056899071/1000000000000 : ℝ) ≤ 4*Real.exp (2297/16384 : ℝ)*Real.exp (-mu (radius 7 (4595/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019056899071/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4595/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0515_exp_radius
  have hrNumeric : (980166709341/1000000000000 : ℝ) ≤ Real.exp (-4595/229376 : ℝ) ∧ Real.exp (-4595/229376 : ℝ) ≤ (490083354671/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980166709341/1000000000000 : ℝ) ≤ (radius 7 (4595/32768 : ℝ)) ∧ (radius 7 (4595/32768 : ℝ)) ≤ (490083354671/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4595/32768 : ℝ)) (980166709341/1000000000000 : ℝ) (490083354671/500000000000 : ℝ) (99087362839/500000000000 : ℝ) (49543681421/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4595/32768 : ℝ)) (980166709341/1000000000000 : ℝ) (490083354671/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4595/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980166709341/1000000000000 : ℝ) (490083354671/500000000000 : ℝ) (99008335467/100000000000 : ℝ) (990083354671/1000000000000 : ℝ) (990033691013/1000000000000 : ℝ) (495016845507/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4595/32768 : ℝ)) 1 (99008335467/100000000000 : ℝ) (990083354671/1000000000000 : ℝ) (990033691013/1000000000000 : ℝ) (495016845507/500000000000 : ℝ) (990058522841/1000000000000 : ℝ) (990058522843/1000000000000 : ℝ) (99005852253/100000000000 : ℝ) (247514630633/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4595/32768 : ℝ)) 2 (990058522841/1000000000000 : ℝ) (990058522843/1000000000000 : ℝ) (99005852253/100000000000 : ℝ) (247514630633/250000000000 : ℝ) (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ) (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4595/32768 : ℝ)) 3 (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ) (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ) (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ) (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4595/32768 : ℝ)) 4 (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ) (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ) (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ) (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4595/32768 : ℝ)) 5 (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ) (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ) (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ) (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4595/32768 : ℝ)) 6 (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ) (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ) (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ) (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4595/32768 : ℝ)) 7 (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ) (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ) (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ) (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4595/32768 : ℝ))) (99087362839/500000000000 : ℝ) (49543681421/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4595/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (99087362839/500000000000 : ℝ) (49543681421/250000000000 : ℝ) (599087362839/1000000000000 : ℝ) (299543681421/500000000000 : ℝ) (445168199311/1000000000000 : ℝ) (222584099659/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4595/32768 : ℝ))) 1 (599087362839/1000000000000 : ℝ) (299543681421/500000000000 : ℝ) (445168199311/1000000000000 : ℝ) (222584099659/500000000000 : ℝ) (20885111243/40000000000 : ℝ) (13053194527/25000000000 : ℝ) (516424866311/1000000000000 : ℝ) (258212433159/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4595/32768 : ℝ))) 2 (20885111243/40000000000 : ℝ) (13053194527/25000000000 : ℝ) (516424866311/1000000000000 : ℝ) (258212433159/500000000000 : ℝ) (519276323693/1000000000000 : ℝ) (519276323699/1000000000000 : ℝ) (129817123663/250000000000 : ℝ) (519268494659/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4595/32768 : ℝ))) 3 (519276323693/1000000000000 : ℝ) (519276323699/1000000000000 : ℝ) (129817123663/250000000000 : ℝ) (519268494659/1000000000000 : ℝ) (129818102293/250000000000 : ℝ) (519272409179/1000000000000 : ℝ) (519272409157/1000000000000 : ℝ) (103854481833/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4595/32768 : ℝ))) 4 (129818102293/250000000000 : ℝ) (519272409179/1000000000000 : ℝ) (519272409157/1000000000000 : ℝ) (103854481833/200000000000 : ℝ) (129818102291/250000000000 : ℝ) (129818102293/250000000000 : ℝ) (129818102291/250000000000 : ℝ) (129818102293/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4595/32768 : ℝ))) 5 (129818102291/250000000000 : ℝ) (129818102293/250000000000 : ℝ) (129818102291/250000000000 : ℝ) (129818102293/250000000000 : ℝ) (129818102291/250000000000 : ℝ) (129818102293/250000000000 : ℝ) (129818102291/250000000000 : ℝ) (129818102293/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4595/32768 : ℝ))) 6 (129818102291/250000000000 : ℝ) (129818102293/250000000000 : ℝ) (129818102291/250000000000 : ℝ) (129818102293/250000000000 : ℝ) (129818102291/250000000000 : ℝ) (129818102293/250000000000 : ℝ) (129818102291/250000000000 : ℝ) (129818102293/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4595/32768 : ℝ))) 7 (129818102291/250000000000 : ℝ) (129818102293/250000000000 : ℝ) (129818102291/250000000000 : ℝ) (129818102293/250000000000 : ℝ) (129818102291/250000000000 : ℝ) (129818102293/250000000000 : ℝ) (129818102291/250000000000 : ℝ) (129818102293/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4595/32768 : ℝ)) hmem 8 (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ) (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4595/32768 : ℝ))) hcmem 8 (129818102291/250000000000 : ℝ) (129818102293/250000000000 : ℝ) (129818102291/250000000000 : ℝ) (129818102293/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4595/32768 : ℝ)) (198011704537/200000000000 : ℝ) (15469664417/15625000000 : ℝ) (129818102291/250000000000 : ℝ) (129818102293/250000000000 : ℝ) (205965398567/250000000000 : ℝ) (205965398571/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0515_exp_lower
  have heNumeric : (2019056899071/1000000000000 : ℝ)/4 ≤ Real.exp (-2734655361511/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019056899071/1000000000000 : ℝ)/4 ≤ Real.exp ((2297/16384 : ℝ)-(205965398571/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2297/16384 : ℝ) (4595/32768 : ℝ) (205965398571/250000000000 : ℝ) (2019056899071/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0516; no trusted numerical premise.
theorem cover7_leaf0516_exp_radius : (249374628178376559/250000000000000000 : ℝ) ≤ Real.exp ((-1149/57344 : ℝ)/8) ∧ Real.exp ((-1149/57344 : ℝ)/8) ≤ (997498512713506237/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1149/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0516_exp_lower : (183618357556679583/200000000000000000 : ℝ) ≤ Real.exp ((-5469306026741/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469306026741/8000000000000 : ℝ)/8) ≤ (229522946945849479/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469306026741/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0516_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019058084329/1000000000000 : ℝ) ≤ 4*Real.exp (4595/32768 : ℝ)*Real.exp (-mu (radius 7 (1149/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019058084329/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1149/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0516_exp_radius
  have hrNumeric : (490081218081/500000000000 : ℝ) ≤ Real.exp (-1149/57344 : ℝ) ∧ Real.exp (-1149/57344 : ℝ) ≤ (980162436163/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490081218081/500000000000 : ℝ) ≤ (radius 7 (1149/8192 : ℝ)) ∧ (radius 7 (1149/8192 : ℝ)) ≤ (980162436163/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1149/8192 : ℝ)) (490081218081/500000000000 : ℝ) (980162436163/1000000000000 : ℝ) (19819585953/100000000000 : ℝ) (12387241221/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1149/8192 : ℝ)) (490081218081/500000000000 : ℝ) (980162436163/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1149/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490081218081/500000000000 : ℝ) (980162436163/1000000000000 : ℝ) (990081218081/1000000000000 : ℝ) (495040609041/500000000000 : ℝ) (61876970807/62500000000 : ℝ) (495015766457/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1149/8192 : ℝ)) 1 (990081218081/1000000000000 : ℝ) (495040609041/500000000000 : ℝ) (61876970807/62500000000 : ℝ) (495015766457/500000000000 : ℝ) (123757046937/125000000000 : ℝ) (495028187749/500000000000 : ℝ) (61878523449/62500000000 : ℝ) (990056375187/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1149/8192 : ℝ)) 2 (123757046937/125000000000 : ℝ) (495028187749/500000000000 : ℝ) (61878523449/62500000000 : ℝ) (990056375187/1000000000000 : ℝ) (49502818767/50000000000 : ℝ) (990056375343/1000000000000 : ℝ) (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1149/8192 : ℝ)) 3 (49502818767/50000000000 : ℝ) (990056375343/1000000000000 : ℝ) (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ) (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ) (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1149/8192 : ℝ)) 4 (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ) (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ) (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ) (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1149/8192 : ℝ)) 5 (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ) (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ) (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ) (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1149/8192 : ℝ)) 6 (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ) (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ) (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ) (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1149/8192 : ℝ)) 7 (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ) (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ) (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ) (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1149/8192 : ℝ))) (19819585953/100000000000 : ℝ) (12387241221/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1149/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19819585953/100000000000 : ℝ) (12387241221/62500000000 : ℝ) (119819585953/200000000000 : ℝ) (74887241221/125000000000 : ℝ) (445191935607/1000000000000 : ℝ) (89038387123/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1149/8192 : ℝ))) 1 (119819585953/200000000000 : ℝ) (74887241221/125000000000 : ℝ) (445191935607/1000000000000 : ℝ) (89038387123/200000000000 : ℝ) (261072466343/500000000000 : ℝ) (130536233173/250000000000 : ℝ) (516443188521/1000000000000 : ℝ) (32277699283/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1149/8192 : ℝ))) 2 (261072466343/500000000000 : ℝ) (130536233173/250000000000 : ℝ) (516443188521/1000000000000 : ℝ) (32277699283/62500000000 : ℝ) (519294060603/1000000000000 : ℝ) (51929406061/100000000000 : ℝ) (129821558761/250000000000 : ℝ) (519286235051/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1149/8192 : ℝ))) 3 (519294060603/1000000000000 : ℝ) (51929406061/100000000000 : ℝ) (129821558761/250000000000 : ℝ) (519286235051/1000000000000 : ℝ) (519290147823/1000000000000 : ℝ) (519290147831/1000000000000 : ℝ) (16227817119/31250000000 : ℝ) (64911268477/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1149/8192 : ℝ))) 4 (519290147823/1000000000000 : ℝ) (519290147831/1000000000000 : ℝ) (16227817119/31250000000 : ℝ) (64911268477/125000000000 : ℝ) (103858029563/200000000000 : ℝ) (32455634239/62500000000 : ℝ) (103858029563/200000000000 : ℝ) (32455634239/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1149/8192 : ℝ))) 5 (103858029563/200000000000 : ℝ) (32455634239/62500000000 : ℝ) (103858029563/200000000000 : ℝ) (32455634239/62500000000 : ℝ) (103858029563/200000000000 : ℝ) (32455634239/62500000000 : ℝ) (103858029563/200000000000 : ℝ) (32455634239/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1149/8192 : ℝ))) 6 (103858029563/200000000000 : ℝ) (32455634239/62500000000 : ℝ) (103858029563/200000000000 : ℝ) (32455634239/62500000000 : ℝ) (103858029563/200000000000 : ℝ) (32455634239/62500000000 : ℝ) (103858029563/200000000000 : ℝ) (32455634239/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1149/8192 : ℝ))) 7 (103858029563/200000000000 : ℝ) (32455634239/62500000000 : ℝ) (103858029563/200000000000 : ℝ) (32455634239/62500000000 : ℝ) (103858029563/200000000000 : ℝ) (32455634239/62500000000 : ℝ) (103858029563/200000000000 : ℝ) (32455634239/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1149/8192 : ℝ)) hmem 8 (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ) (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1149/8192 : ℝ))) hcmem 8 (103858029563/200000000000 : ℝ) (32455634239/62500000000 : ℝ) (103858029563/200000000000 : ℝ) (32455634239/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1149/8192 : ℝ)) (990056375339/1000000000000 : ℝ) (990056375343/1000000000000 : ℝ) (103858029563/200000000000 : ℝ) (32455634239/62500000000 : ℝ) (823891524809/1000000000000 : ℝ) (823891524827/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0516_exp_lower
  have heNumeric : (2019058084329/1000000000000 : ℝ)/4 ≤ Real.exp (-5469306026741/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019058084329/1000000000000 : ℝ)/4 ≤ Real.exp ((4595/32768 : ℝ)-(823891524827/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4595/32768 : ℝ) (1149/8192 : ℝ) (823891524827/1000000000000 : ℝ) (2019058084329/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0517; no trusted numerical premise.
theorem cover7_leaf0517_exp_radius : (997497969120104509/1000000000000000000 : ℝ) ≤ Real.exp ((-4597/229376 : ℝ)/8) ∧ Real.exp ((-4597/229376 : ℝ)/8) ≤ (99749796912010451/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4597/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0517_exp_lower : (918091855651513997/1000000000000000000 : ℝ) ≤ Real.exp ((-1367325323917/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367325323917/2000000000000 : ℝ)/8) ≤ (459045927825756999/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367325323917/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0517_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (63095602449/31250000000 : ℝ) ≤ 4*Real.exp (1149/8192 : ℝ)*Real.exp (-mu (radius 7 (4597/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (63095602449/31250000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4597/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0517_exp_radius
  have hrNumeric : (980158163003/1000000000000 : ℝ) ≤ Real.exp (-4597/229376 : ℝ) ∧ Real.exp (-4597/229376 : ℝ) ≤ (245039540751/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980158163003/1000000000000 : ℝ) ≤ (radius 7 (4597/32768 : ℝ)) ∧ (radius 7 (4597/32768 : ℝ)) ≤ (245039540751/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4597/32768 : ℝ)) (980158163003/1000000000000 : ℝ) (245039540751/250000000000 : ℝ) (99108495469/500000000000 : ℝ) (6194280967/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4597/32768 : ℝ)) (980158163003/1000000000000 : ℝ) (245039540751/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4597/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980158163003/1000000000000 : ℝ) (245039540751/250000000000 : ℝ) (990079081501/1000000000000 : ℝ) (495039540751/500000000000 : ℝ) (495014687409/500000000000 : ℝ) (990029374819/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4597/32768 : ℝ)) 1 (990079081501/1000000000000 : ℝ) (495039540751/500000000000 : ℝ) (495014687409/500000000000 : ℝ) (990029374819/1000000000000 : ℝ) (990054228159/1000000000000 : ℝ) (990054228161/1000000000000 : ℝ) (990054227847/1000000000000 : ℝ) (990054227849/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4597/32768 : ℝ)) 2 (990054228159/1000000000000 : ℝ) (990054228161/1000000000000 : ℝ) (990054227847/1000000000000 : ℝ) (990054227849/1000000000000 : ℝ) (990054228003/1000000000000 : ℝ) (198010845601/200000000000 : ℝ) (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4597/32768 : ℝ)) 3 (990054228003/1000000000000 : ℝ) (198010845601/200000000000 : ℝ) (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ) (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ) (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4597/32768 : ℝ)) 4 (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ) (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ) (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ) (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4597/32768 : ℝ)) 5 (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ) (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ) (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ) (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4597/32768 : ℝ)) 6 (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ) (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ) (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ) (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4597/32768 : ℝ)) 7 (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ) (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ) (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ) (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4597/32768 : ℝ))) (99108495469/500000000000 : ℝ) (6194280967/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4597/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (99108495469/500000000000 : ℝ) (6194280967/31250000000 : ℝ) (599108495469/1000000000000 : ℝ) (37444280967/62500000000 : ℝ) (445215667893/1000000000000 : ℝ) (445215667901/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4597/32768 : ℝ))) 1 (599108495469/1000000000000 : ℝ) (37444280967/62500000000 : ℝ) (445215667893/1000000000000 : ℝ) (445215667901/1000000000000 : ℝ) (522162081681/1000000000000 : ℝ) (522162081687/1000000000000 : ℝ) (258230753857/500000000000 : ℝ) (516461507721/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4597/32768 : ℝ))) 2 (522162081681/1000000000000 : ℝ) (522162081687/1000000000000 : ℝ) (258230753857/500000000000 : ℝ) (516461507721/1000000000000 : ℝ) (519311794697/1000000000000 : ℝ) (32456987169/62500000000 : ℝ) (519303972617/1000000000000 : ℝ) (32456498289/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4597/32768 : ℝ))) 3 (519311794697/1000000000000 : ℝ) (32456987169/62500000000 : ℝ) (519303972617/1000000000000 : ℝ) (32456498289/62500000000 : ℝ) (519307883657/1000000000000 : ℝ) (32456742729/62500000000 : ℝ) (259653941821/500000000000 : ℝ) (10386157673/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4597/32768 : ℝ))) 4 (519307883657/1000000000000 : ℝ) (32456742729/62500000000 : ℝ) (259653941821/500000000000 : ℝ) (10386157673/20000000000 : ℝ) (519307883649/1000000000000 : ℝ) (519307883657/1000000000000 : ℝ) (519307883649/1000000000000 : ℝ) (519307883657/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4597/32768 : ℝ))) 5 (519307883649/1000000000000 : ℝ) (519307883657/1000000000000 : ℝ) (519307883649/1000000000000 : ℝ) (519307883657/1000000000000 : ℝ) (519307883649/1000000000000 : ℝ) (519307883657/1000000000000 : ℝ) (519307883649/1000000000000 : ℝ) (519307883657/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4597/32768 : ℝ))) 6 (519307883649/1000000000000 : ℝ) (519307883657/1000000000000 : ℝ) (519307883649/1000000000000 : ℝ) (519307883657/1000000000000 : ℝ) (519307883649/1000000000000 : ℝ) (519307883657/1000000000000 : ℝ) (519307883649/1000000000000 : ℝ) (519307883657/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4597/32768 : ℝ))) 7 (519307883649/1000000000000 : ℝ) (519307883657/1000000000000 : ℝ) (519307883649/1000000000000 : ℝ) (519307883657/1000000000000 : ℝ) (519307883649/1000000000000 : ℝ) (519307883657/1000000000000 : ℝ) (519307883649/1000000000000 : ℝ) (519307883657/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4597/32768 : ℝ)) hmem 8 (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ) (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4597/32768 : ℝ))) hcmem 8 (519307883649/1000000000000 : ℝ) (519307883657/1000000000000 : ℝ) (519307883649/1000000000000 : ℝ) (519307883657/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4597/32768 : ℝ)) (495027114001/500000000000 : ℝ) (198010845601/200000000000 : ℝ) (519307883649/1000000000000 : ℝ) (519307883657/1000000000000 : ℝ) (205980362751/250000000000 : ℝ) (823921451021/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0517_exp_lower
  have heNumeric : (63095602449/31250000000 : ℝ)/4 ≤ Real.exp (-1367325323917/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (63095602449/31250000000 : ℝ)/4 ≤ Real.exp ((1149/8192 : ℝ)-(823921451021/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1149/8192 : ℝ) (4597/32768 : ℝ) (823921451021/1000000000000 : ℝ) (63095602449/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0518; no trusted numerical premise.
theorem cover7_leaf0518_exp_radius : (124687178190874877/125000000000000000 : ℝ) ≤ Real.exp ((-2299/114688 : ℝ)/8) ∧ Real.exp ((-2299/114688 : ℝ)/8) ≤ (997497425526999017/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2299/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0518_exp_lower : (459045962007989271/500000000000000000 : ℝ) ≤ Real.exp ((-1093859305999/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093859305999/1600000000000 : ℝ)/8) ≤ (918091924015978543/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093859305999/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0518_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (100953024057/50000000000 : ℝ) ≤ 4*Real.exp (4597/32768 : ℝ)*Real.exp (-mu (radius 7 (2299/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (100953024057/50000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2299/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0518_exp_radius
  have hrNumeric : (980153889861/1000000000000 : ℝ) ≤ Real.exp (-2299/114688 : ℝ) ∧ Real.exp (-2299/114688 : ℝ) ≤ (490076944931/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980153889861/1000000000000 : ℝ) ≤ (radius 7 (2299/16384 : ℝ)) ∧ (radius 7 (2299/16384 : ℝ)) ≤ (490076944931/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2299/16384 : ℝ)) (980153889861/1000000000000 : ℝ) (490076944931/500000000000 : ℝ) (198238119917/1000000000000 : ℝ) (198238119923/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2299/16384 : ℝ)) (980153889861/1000000000000 : ℝ) (490076944931/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2299/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980153889861/1000000000000 : ℝ) (490076944931/500000000000 : ℝ) (99007694493/100000000000 : ℝ) (990076944931/1000000000000 : ℝ) (990027216727/1000000000000 : ℝ) (123753402091/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2299/16384 : ℝ)) 1 (99007694493/100000000000 : ℝ) (990076944931/1000000000000 : ℝ) (990027216727/1000000000000 : ℝ) (123753402091/125000000000 : ℝ) (247513020207/250000000000 : ℝ) (99005208083/100000000000 : ℝ) (247513020129/250000000000 : ℝ) (495026040259/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2299/16384 : ℝ)) 2 (247513020207/250000000000 : ℝ) (99005208083/100000000000 : ℝ) (247513020129/250000000000 : ℝ) (495026040259/500000000000 : ℝ) (30939127521/31250000000 : ℝ) (495026040337/500000000000 : ℝ) (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2299/16384 : ℝ)) 3 (30939127521/31250000000 : ℝ) (495026040337/500000000000 : ℝ) (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ) (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ) (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2299/16384 : ℝ)) 4 (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ) (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ) (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ) (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2299/16384 : ℝ)) 5 (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ) (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ) (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ) (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2299/16384 : ℝ)) 6 (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ) (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ) (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ) (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2299/16384 : ℝ)) 7 (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ) (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ) (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ) (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2299/16384 : ℝ))) (198238119917/1000000000000 : ℝ) (198238119923/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2299/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (198238119917/1000000000000 : ℝ) (198238119923/1000000000000 : ℝ) (299559529979/500000000000 : ℝ) (299559529981/500000000000 : ℝ) (445239396187/1000000000000 : ℝ) (222619698097/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2299/16384 : ℝ))) 1 (299559529979/500000000000 : ℝ) (299559529981/500000000000 : ℝ) (445239396187/1000000000000 : ℝ) (222619698097/500000000000 : ℝ) (65272403509/125000000000 : ℝ) (261089614039/500000000000 : ℝ) (516479823903/1000000000000 : ℝ) (51647982391/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2299/16384 : ℝ))) 2 (65272403509/125000000000 : ℝ) (261089614039/500000000000 : ℝ) (516479823903/1000000000000 : ℝ) (51647982391/100000000000 : ℝ) (519329525987/1000000000000 : ℝ) (259664762997/500000000000 : ℝ) (64915213423/125000000000 : ℝ) (519321707391/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2299/16384 : ℝ))) 3 (519329525987/1000000000000 : ℝ) (259664762997/500000000000 : ℝ) (64915213423/125000000000 : ℝ) (519321707391/1000000000000 : ℝ) (103865123337/200000000000 : ℝ) (519325616693/1000000000000 : ℝ) (51932561667/100000000000 : ℝ) (259662808339/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2299/16384 : ℝ))) 4 (103865123337/200000000000 : ℝ) (519325616693/1000000000000 : ℝ) (51932561667/100000000000 : ℝ) (259662808339/500000000000 : ℝ) (519325616677/1000000000000 : ℝ) (259662808343/500000000000 : ℝ) (519325616677/1000000000000 : ℝ) (259662808343/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2299/16384 : ℝ))) 5 (519325616677/1000000000000 : ℝ) (259662808343/500000000000 : ℝ) (519325616677/1000000000000 : ℝ) (259662808343/500000000000 : ℝ) (519325616677/1000000000000 : ℝ) (259662808343/500000000000 : ℝ) (519325616677/1000000000000 : ℝ) (259662808343/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2299/16384 : ℝ))) 6 (519325616677/1000000000000 : ℝ) (259662808343/500000000000 : ℝ) (519325616677/1000000000000 : ℝ) (259662808343/500000000000 : ℝ) (519325616677/1000000000000 : ℝ) (259662808343/500000000000 : ℝ) (519325616677/1000000000000 : ℝ) (259662808343/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2299/16384 : ℝ))) 7 (519325616677/1000000000000 : ℝ) (259662808343/500000000000 : ℝ) (519325616677/1000000000000 : ℝ) (259662808343/500000000000 : ℝ) (519325616677/1000000000000 : ℝ) (259662808343/500000000000 : ℝ) (519325616677/1000000000000 : ℝ) (259662808343/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2299/16384 : ℝ)) hmem 8 (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ) (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2299/16384 : ℝ))) hcmem 8 (519325616677/1000000000000 : ℝ) (259662808343/500000000000 : ℝ) (519325616677/1000000000000 : ℝ) (259662808343/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2299/16384 : ℝ)) (990052080671/1000000000000 : ℝ) (495026040337/500000000000 : ℝ) (519325616677/1000000000000 : ℝ) (259662808343/500000000000 : ℝ) (102993921609/125000000000 : ℝ) (82395137289/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0518_exp_lower
  have heNumeric : (100953024057/50000000000 : ℝ)/4 ≤ Real.exp (-1093859305999/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (100953024057/50000000000 : ℝ)/4 ≤ Real.exp ((4597/32768 : ℝ)-(82395137289/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4597/32768 : ℝ) (2299/16384 : ℝ) (82395137289/100000000000 : ℝ) (100953024057/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0519; no trusted numerical premise.
theorem cover7_leaf0519_exp_radius : (199499267668335347/200000000000000000 : ℝ) ≤ Real.exp ((-575/28672 : ℝ)/8) ∧ Real.exp ((-575/28672 : ℝ)/8) ≤ (15585880286588699/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-575/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0519_exp_lower : (183617712000411853/200000000000000000 : ℝ) ≤ Real.exp ((-2734765517573/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734765517573/4000000000000 : ℝ)/8) ≤ (459044280001029633/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734765517573/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0519_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019001296997/1000000000000 : ℝ) ≤ 4*Real.exp (2299/16384 : ℝ)*Real.exp (-mu (radius 7 (575/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019001296997/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (575/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0519_exp_radius
  have hrNumeric : (196029068727/200000000000 : ℝ) ≤ Real.exp (-575/28672 : ℝ) ∧ Real.exp (-575/28672 : ℝ) ≤ (245036335909/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196029068727/200000000000 : ℝ) ≤ (radius 7 (575/4096 : ℝ)) ∧ (radius 7 (575/4096 : ℝ)) ≤ (245036335909/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (575/4096 : ℝ)) (196029068727/200000000000 : ℝ) (245036335909/250000000000 : ℝ) (99140185279/500000000000 : ℝ) (49570092641/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (575/4096 : ℝ)) (196029068727/200000000000 : ℝ) (245036335909/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (575/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196029068727/200000000000 : ℝ) (245036335909/250000000000 : ℝ) (990072671817/1000000000000 : ℝ) (495036335909/500000000000 : ℝ) (12375286257/12500000000 : ℝ) (495011450281/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (575/4096 : ℝ)) 1 (990072671817/1000000000000 : ℝ) (495036335909/500000000000 : ℝ) (12375286257/12500000000 : ℝ) (495011450281/500000000000 : ℝ) (247511946547/250000000000 : ℝ) (99004778619/100000000000 : ℝ) (7920382287/8000000000 : ℝ) (495023892939/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (575/4096 : ℝ)) 2 (247511946547/250000000000 : ℝ) (99004778619/100000000000 : ℝ) (7920382287/8000000000 : ℝ) (495023892939/500000000000 : ℝ) (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ) (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (575/4096 : ℝ)) 3 (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ) (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ) (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ) (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (575/4096 : ℝ)) 4 (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ) (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ) (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ) (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (575/4096 : ℝ)) 5 (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ) (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ) (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ) (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (575/4096 : ℝ)) 6 (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ) (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ) (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ) (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (575/4096 : ℝ)) 7 (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ) (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ) (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ) (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (575/4096 : ℝ))) (99140185279/500000000000 : ℝ) (49570092641/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (575/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (99140185279/500000000000 : ℝ) (49570092641/250000000000 : ℝ) (599140185279/1000000000000 : ℝ) (299570092641/500000000000 : ℝ) (111321710191/250000000000 : ℝ) (111321710193/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (575/4096 : ℝ))) 1 (599140185279/1000000000000 : ℝ) (299570092641/500000000000 : ℝ) (111321710191/250000000000 : ℝ) (111321710193/250000000000 : ℝ) (522213513021/1000000000000 : ℝ) (522213513027/1000000000000 : ℝ) (516516447247/1000000000000 : ℝ) (258258223627/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (575/4096 : ℝ))) 2 (522213513021/1000000000000 : ℝ) (522213513027/1000000000000 : ℝ) (516516447247/1000000000000 : ℝ) (258258223627/500000000000 : ℝ) (259682490067/500000000000 : ℝ) (519364980141/1000000000000 : ℝ) (259678584239/500000000000 : ℝ) (103871433697/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (575/4096 : ℝ))) 3 (259682490067/500000000000 : ℝ) (519364980141/1000000000000 : ℝ) (259678584239/500000000000 : ℝ) (103871433697/200000000000 : ℝ) (259680537153/500000000000 : ℝ) (519361074313/1000000000000 : ℝ) (519361074291/1000000000000 : ℝ) (519361074299/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (575/4096 : ℝ))) 4 (259680537153/500000000000 : ℝ) (519361074313/1000000000000 : ℝ) (519361074291/1000000000000 : ℝ) (519361074299/1000000000000 : ℝ) (259680537149/500000000000 : ℝ) (259680537153/500000000000 : ℝ) (259680537149/500000000000 : ℝ) (259680537153/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (575/4096 : ℝ))) 5 (259680537149/500000000000 : ℝ) (259680537153/500000000000 : ℝ) (259680537149/500000000000 : ℝ) (259680537153/500000000000 : ℝ) (259680537149/500000000000 : ℝ) (259680537153/500000000000 : ℝ) (259680537149/500000000000 : ℝ) (259680537153/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (575/4096 : ℝ))) 6 (259680537149/500000000000 : ℝ) (259680537153/500000000000 : ℝ) (259680537149/500000000000 : ℝ) (259680537153/500000000000 : ℝ) (259680537149/500000000000 : ℝ) (259680537153/500000000000 : ℝ) (259680537149/500000000000 : ℝ) (259680537153/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (575/4096 : ℝ))) 7 (259680537149/500000000000 : ℝ) (259680537153/500000000000 : ℝ) (259680537149/500000000000 : ℝ) (259680537153/500000000000 : ℝ) (259680537149/500000000000 : ℝ) (259680537153/500000000000 : ℝ) (259680537149/500000000000 : ℝ) (259680537153/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (575/4096 : ℝ)) hmem 8 (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ) (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (575/4096 : ℝ))) hcmem 8 (259680537149/500000000000 : ℝ) (259680537153/500000000000 : ℝ) (259680537149/500000000000 : ℝ) (259680537153/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (575/4096 : ℝ)) (990047786031/1000000000000 : ℝ) (495023893017/500000000000 : ℝ) (259680537149/500000000000 : ℝ) (259680537153/500000000000 : ℝ) (206002800899/250000000000 : ℝ) (206002800903/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0519_exp_lower
  have heNumeric : (2019001296997/1000000000000 : ℝ)/4 ≤ Real.exp (-2734765517573/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019001296997/1000000000000 : ℝ)/4 ≤ Real.exp ((2299/16384 : ℝ)-(206002800903/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2299/16384 : ℝ) (575/4096 : ℝ) (206002800903/250000000000 : ℝ) (2019001296997/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0520; no trusted numerical premise.
theorem cover7_leaf0520_exp_radius : (997495251157539391/1000000000000000000 : ℝ) ≤ Real.exp ((-2301/114688 : ℝ)/8) ∧ Real.exp ((-2301/114688 : ℝ)/8) ≤ (15585863299336553/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2301/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0520_exp_lower : (918088700212124501/1000000000000000000 : ℝ) ≤ Real.exp ((-683690157637/1000000000000 : ℝ)/8) ∧ Real.exp ((-683690157637/1000000000000 : ℝ)/8) ≤ (459044350106062251/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683690157637/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0520_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009501881863/500000000000 : ℝ) ≤ 4*Real.exp (575/4096 : ℝ)*Real.exp (-mu (radius 7 (2301/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (1009501881863/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2301/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0520_exp_radius
  have hrNumeric : (980136797483/1000000000000 : ℝ) ≤ Real.exp (-2301/114688 : ℝ) ∧ Real.exp (-2301/114688 : ℝ) ≤ (245034199371/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980136797483/1000000000000 : ℝ) ≤ (radius 7 (2301/16384 : ℝ)) ∧ (radius 7 (2301/16384 : ℝ)) ≤ (245034199371/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2301/16384 : ℝ)) (980136797483/1000000000000 : ℝ) (245034199371/250000000000 : ℝ) (198322611463/1000000000000 : ℝ) (198322611469/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2301/16384 : ℝ)) (980136797483/1000000000000 : ℝ) (245034199371/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2301/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980136797483/1000000000000 : ℝ) (245034199371/250000000000 : ℝ) (990068398741/1000000000000 : ℝ) (495034199371/500000000000 : ℝ) (247504646103/250000000000 : ℝ) (495009292207/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2301/16384 : ℝ)) 1 (990068398741/1000000000000 : ℝ) (495034199371/500000000000 : ℝ) (247504646103/250000000000 : ℝ) (495009292207/500000000000 : ℝ) (123755436447/125000000000 : ℝ) (495021745789/500000000000 : ℝ) (990043491263/1000000000000 : ℝ) (198008698253/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2301/16384 : ℝ)) 2 (123755436447/125000000000 : ℝ) (495021745789/500000000000 : ℝ) (990043491263/1000000000000 : ℝ) (198008698253/200000000000 : ℝ) (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ) (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2301/16384 : ℝ)) 3 (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ) (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ) (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ) (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2301/16384 : ℝ)) 4 (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ) (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ) (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ) (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2301/16384 : ℝ)) 5 (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ) (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ) (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ) (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2301/16384 : ℝ)) 6 (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ) (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ) (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ) (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2301/16384 : ℝ)) 7 (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ) (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ) (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ) (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2301/16384 : ℝ))) (198322611463/1000000000000 : ℝ) (198322611469/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2301/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (198322611463/1000000000000 : ℝ) (198322611469/1000000000000 : ℝ) (599161305731/1000000000000 : ℝ) (119832261147/200000000000 : ℝ) (111333567339/250000000000 : ℝ) (445334269363/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2301/16384 : ℝ))) 1 (599161305731/1000000000000 : ℝ) (119832261147/200000000000 : ℝ) (111333567339/250000000000 : ℝ) (445334269363/1000000000000 : ℝ) (522247787543/1000000000000 : ℝ) (522247787549/1000000000000 : ℝ) (258276529283/500000000000 : ℝ) (129138264643/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2301/16384 : ℝ))) 2 (522247787543/1000000000000 : ℝ) (522247787549/1000000000000 : ℝ) (258276529283/500000000000 : ℝ) (129138264643/250000000000 : ℝ) (259700211527/500000000000 : ℝ) (519400423061/1000000000000 : ℝ) (259696309169/500000000000 : ℝ) (103878523669/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2301/16384 : ℝ))) 3 (259700211527/500000000000 : ℝ) (519400423061/1000000000000 : ℝ) (259696309169/500000000000 : ℝ) (103878523669/200000000000 : ℝ) (64924565087/125000000000 : ℝ) (519396520703/1000000000000 : ℝ) (519396520681/1000000000000 : ℝ) (519396520689/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2301/16384 : ℝ))) 4 (64924565087/125000000000 : ℝ) (519396520703/1000000000000 : ℝ) (519396520681/1000000000000 : ℝ) (519396520689/1000000000000 : ℝ) (32462282543/62500000000 : ℝ) (64924565087/125000000000 : ℝ) (32462282543/62500000000 : ℝ) (64924565087/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2301/16384 : ℝ))) 5 (32462282543/62500000000 : ℝ) (64924565087/125000000000 : ℝ) (32462282543/62500000000 : ℝ) (64924565087/125000000000 : ℝ) (32462282543/62500000000 : ℝ) (64924565087/125000000000 : ℝ) (32462282543/62500000000 : ℝ) (64924565087/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2301/16384 : ℝ))) 6 (32462282543/62500000000 : ℝ) (64924565087/125000000000 : ℝ) (32462282543/62500000000 : ℝ) (64924565087/125000000000 : ℝ) (32462282543/62500000000 : ℝ) (64924565087/125000000000 : ℝ) (32462282543/62500000000 : ℝ) (64924565087/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2301/16384 : ℝ))) 7 (32462282543/62500000000 : ℝ) (64924565087/125000000000 : ℝ) (32462282543/62500000000 : ℝ) (64924565087/125000000000 : ℝ) (32462282543/62500000000 : ℝ) (64924565087/125000000000 : ℝ) (32462282543/62500000000 : ℝ) (64924565087/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2301/16384 : ℝ)) hmem 8 (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ) (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2301/16384 : ℝ))) hcmem 8 (32462282543/62500000000 : ℝ) (64924565087/125000000000 : ℝ) (32462282543/62500000000 : ℝ) (64924565087/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2301/16384 : ℝ)) (990043491419/1000000000000 : ℝ) (495021745711/500000000000 : ℝ) (32462282543/62500000000 : ℝ) (64924565087/125000000000 : ℝ) (206017754249/250000000000 : ℝ) (206017754253/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0520_exp_lower
  have heNumeric : (1009501881863/500000000000 : ℝ)/4 ≤ Real.exp (-683690157637/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009501881863/500000000000 : ℝ)/4 ≤ Real.exp ((575/4096 : ℝ)-(206017754253/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (575/4096 : ℝ) (2301/16384 : ℝ) (206017754253/250000000000 : ℝ) (1009501881863/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0521; no trusted numerical premise.
theorem cover7_leaf0521_exp_radius : (997494163974586983/1000000000000000000 : ℝ) ≤ Real.exp ((-1151/57344 : ℝ)/8) ∧ Real.exp ((-1151/57344 : ℝ)/8) ≤ (124686770496823373/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1151/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0521_exp_lower : (918088842408955403/1000000000000000000 : ℝ) ≤ Real.exp ((-109390226971/160000000000 : ℝ)/8) ∧ Real.exp ((-109390226971/160000000000 : ℝ)/8) ≤ (229522210602238851/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-109390226971/160000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0521_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019006265411/1000000000000 : ℝ) ≤ 4*Real.exp (2301/16384 : ℝ)*Real.exp (-mu (radius 7 (1151/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019006265411/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1151/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0521_exp_radius
  have hrNumeric : (490064125703/500000000000 : ℝ) ≤ Real.exp (-1151/57344 : ℝ) ∧ Real.exp (-1151/57344 : ℝ) ≤ (980128251407/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490064125703/500000000000 : ℝ) ≤ (radius 7 (1151/8192 : ℝ)) ∧ (radius 7 (1151/8192 : ℝ)) ≤ (980128251407/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1151/8192 : ℝ)) (490064125703/500000000000 : ℝ) (980128251407/1000000000000 : ℝ) (39672968527/200000000000 : ℝ) (198364842641/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1151/8192 : ℝ)) (490064125703/500000000000 : ℝ) (980128251407/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1151/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490064125703/500000000000 : ℝ) (980128251407/1000000000000 : ℝ) (990064125703/1000000000000 : ℝ) (123758015713/125000000000 : ℝ) (247503567071/250000000000 : ℝ) (198002853657/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1151/8192 : ℝ)) 1 (990064125703/1000000000000 : ℝ) (123758015713/125000000000 : ℝ) (247503567071/250000000000 : ℝ) (198002853657/200000000000 : ℝ) (990039196993/1000000000000 : ℝ) (198007839399/200000000000 : ℝ) (990039196679/1000000000000 : ℝ) (990039196681/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1151/8192 : ℝ)) 2 (990039196993/1000000000000 : ℝ) (198007839399/200000000000 : ℝ) (990039196679/1000000000000 : ℝ) (990039196681/1000000000000 : ℝ) (247509799209/250000000000 : ℝ) (495019598419/500000000000 : ℝ) (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1151/8192 : ℝ)) 3 (247509799209/250000000000 : ℝ) (495019598419/500000000000 : ℝ) (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ) (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ) (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1151/8192 : ℝ)) 4 (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ) (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ) (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ) (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1151/8192 : ℝ)) 5 (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ) (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ) (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ) (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1151/8192 : ℝ)) 6 (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ) (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ) (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ) (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1151/8192 : ℝ)) 7 (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ) (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ) (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ) (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1151/8192 : ℝ))) (39672968527/200000000000 : ℝ) (198364842641/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1151/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39672968527/200000000000 : ℝ) (198364842641/1000000000000 : ℝ) (599182421317/1000000000000 : ℝ) (599182421321/1000000000000 : ℝ) (44538168197/100000000000 : ℝ) (222690840989/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1151/8192 : ℝ))) 1 (599182421317/1000000000000 : ℝ) (599182421321/1000000000000 : ℝ) (44538168197/100000000000 : ℝ) (222690840989/500000000000 : ℝ) (522282051643/1000000000000 : ℝ) (10445641033/20000000000 : ℝ) (64573707233/125000000000 : ℝ) (32286853617/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1151/8192 : ℝ))) 2 (522282051643/1000000000000 : ℝ) (10445641033/20000000000 : ℝ) (64573707233/125000000000 : ℝ) (32286853617/62500000000 : ℝ) (519435854753/1000000000000 : ℝ) (519435854761/1000000000000 : ℝ) (519428056969/1000000000000 : ℝ) (519428056977/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1151/8192 : ℝ))) 3 (519435854753/1000000000000 : ℝ) (519435854761/1000000000000 : ℝ) (519428056969/1000000000000 : ℝ) (519428056977/1000000000000 : ℝ) (519431955861/1000000000000 : ℝ) (519431955869/1000000000000 : ℝ) (259715977923/500000000000 : ℝ) (103886391171/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1151/8192 : ℝ))) 4 (519431955861/1000000000000 : ℝ) (519431955869/1000000000000 : ℝ) (259715977923/500000000000 : ℝ) (103886391171/200000000000 : ℝ) (519431955853/1000000000000 : ℝ) (259715977931/500000000000 : ℝ) (519431955853/1000000000000 : ℝ) (259715977931/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1151/8192 : ℝ))) 5 (519431955853/1000000000000 : ℝ) (259715977931/500000000000 : ℝ) (519431955853/1000000000000 : ℝ) (259715977931/500000000000 : ℝ) (519431955853/1000000000000 : ℝ) (259715977931/500000000000 : ℝ) (519431955853/1000000000000 : ℝ) (259715977931/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1151/8192 : ℝ))) 6 (519431955853/1000000000000 : ℝ) (259715977931/500000000000 : ℝ) (519431955853/1000000000000 : ℝ) (259715977931/500000000000 : ℝ) (519431955853/1000000000000 : ℝ) (259715977931/500000000000 : ℝ) (519431955853/1000000000000 : ℝ) (259715977931/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1151/8192 : ℝ))) 7 (519431955853/1000000000000 : ℝ) (259715977931/500000000000 : ℝ) (519431955853/1000000000000 : ℝ) (259715977931/500000000000 : ℝ) (519431955853/1000000000000 : ℝ) (259715977931/500000000000 : ℝ) (519431955853/1000000000000 : ℝ) (259715977931/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1151/8192 : ℝ)) hmem 8 (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ) (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1151/8192 : ℝ))) hcmem 8 (519431955853/1000000000000 : ℝ) (259715977931/500000000000 : ℝ) (519431955853/1000000000000 : ℝ) (259715977931/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1151/8192 : ℝ)) (198007839367/200000000000 : ℝ) (495019598419/500000000000 : ℝ) (519431955853/1000000000000 : ℝ) (259715977931/500000000000 : ℝ) (412065406541/500000000000 : ℝ) (8241308131/10000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0521_exp_lower
  have heNumeric : (2019006265411/1000000000000 : ℝ)/4 ≤ Real.exp (-109390226971/160000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019006265411/1000000000000 : ℝ)/4 ≤ Real.exp ((2301/16384 : ℝ)-(8241308131/10000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2301/16384 : ℝ) (1151/8192 : ℝ) (8241308131/10000000000 : ℝ) (2019006265411/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0522; no trusted numerical premise.
theorem cover7_leaf0522_exp_radius : (99749307679281951/100000000000000000 : ℝ) ≤ Real.exp ((-329/16384 : ℝ)/8) ∧ Real.exp ((-329/16384 : ℝ)/8) ≤ (997493076792819511/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-329/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0522_exp_lower : (229522246647707869/250000000000000000 : ℝ) ≤ Real.exp ((-1367375324407/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367375324407/2000000000000 : ℝ)/8) ≤ (918088986590831477/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367375324407/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0522_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009504401011/500000000000 : ℝ) ≤ 4*Real.exp (1151/8192 : ℝ)*Real.exp (-mu (radius 7 (2303/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (1009504401011/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2303/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0522_exp_radius
  have hrNumeric : (980119705403/1000000000000 : ℝ) ≤ Real.exp (-329/16384 : ℝ) ∧ Real.exp (-329/16384 : ℝ) ≤ (245029926351/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980119705403/1000000000000 : ℝ) ≤ (radius 7 (2303/16384 : ℝ)) ∧ (radius 7 (2303/16384 : ℝ)) ≤ (245029926351/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2303/16384 : ℝ)) (980119705403/1000000000000 : ℝ) (245029926351/250000000000 : ℝ) (49601766021/250000000000 : ℝ) (19840706409/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2303/16384 : ℝ)) (980119705403/1000000000000 : ℝ) (245029926351/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2303/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980119705403/1000000000000 : ℝ) (245029926351/250000000000 : ℝ) (990059852701/1000000000000 : ℝ) (495029926351/500000000000 : ℝ) (990009952173/1000000000000 : ℝ) (39600398087/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2303/16384 : ℝ)) 1 (990059852701/1000000000000 : ℝ) (495029926351/500000000000 : ℝ) (990009952173/1000000000000 : ℝ) (39600398087/40000000000 : ℝ) (990034902437/1000000000000 : ℝ) (990034902439/1000000000000 : ℝ) (495017451061/500000000000 : ℝ) (7920279217/8000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2303/16384 : ℝ)) 2 (990034902437/1000000000000 : ℝ) (990034902439/1000000000000 : ℝ) (495017451061/500000000000 : ℝ) (7920279217/8000000000 : ℝ) (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ) (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2303/16384 : ℝ)) 3 (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ) (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ) (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ) (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2303/16384 : ℝ)) 4 (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ) (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ) (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ) (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2303/16384 : ℝ)) 5 (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ) (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ) (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ) (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2303/16384 : ℝ)) 6 (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ) (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ) (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ) (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2303/16384 : ℝ)) 7 (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ) (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ) (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ) (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2303/16384 : ℝ))) (49601766021/250000000000 : ℝ) (19840706409/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2303/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49601766021/250000000000 : ℝ) (19840706409/100000000000 : ℝ) (299601766021/500000000000 : ℝ) (119840706409/200000000000 : ℝ) (13919658707/31250000000 : ℝ) (445429078631/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2303/16384 : ℝ))) 1 (299601766021/500000000000 : ℝ) (119840706409/200000000000 : ℝ) (13919658707/31250000000 : ℝ) (445429078631/1000000000000 : ℝ) (522316305333/1000000000000 : ℝ) (261158152669/500000000000 : ℝ) (516626245157/1000000000000 : ℝ) (129156561291/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2303/16384 : ℝ))) 2 (522316305333/1000000000000 : ℝ) (261158152669/500000000000 : ℝ) (516626245157/1000000000000 : ℝ) (129156561291/250000000000 : ℝ) (103894255049/200000000000 : ℝ) (519471275251/1000000000000 : ℝ) (16233233887/31250000000 : ℝ) (519463484391/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2303/16384 : ℝ))) 3 (103894255049/200000000000 : ℝ) (519471275251/1000000000000 : ℝ) (16233233887/31250000000 : ℝ) (519463484391/1000000000000 : ℝ) (259733689907/500000000000 : ℝ) (519467379821/1000000000000 : ℝ) (519467379799/1000000000000 : ℝ) (519467379807/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2303/16384 : ℝ))) 4 (259733689907/500000000000 : ℝ) (519467379821/1000000000000 : ℝ) (519467379799/1000000000000 : ℝ) (519467379807/1000000000000 : ℝ) (259733689903/500000000000 : ℝ) (259733689907/500000000000 : ℝ) (259733689903/500000000000 : ℝ) (259733689907/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2303/16384 : ℝ))) 5 (259733689903/500000000000 : ℝ) (259733689907/500000000000 : ℝ) (259733689903/500000000000 : ℝ) (259733689907/500000000000 : ℝ) (259733689903/500000000000 : ℝ) (259733689907/500000000000 : ℝ) (259733689903/500000000000 : ℝ) (259733689907/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2303/16384 : ℝ))) 6 (259733689903/500000000000 : ℝ) (259733689907/500000000000 : ℝ) (259733689903/500000000000 : ℝ) (259733689907/500000000000 : ℝ) (259733689903/500000000000 : ℝ) (259733689907/500000000000 : ℝ) (259733689903/500000000000 : ℝ) (259733689907/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2303/16384 : ℝ))) 7 (259733689903/500000000000 : ℝ) (259733689907/500000000000 : ℝ) (259733689903/500000000000 : ℝ) (259733689907/500000000000 : ℝ) (259733689903/500000000000 : ℝ) (259733689907/500000000000 : ℝ) (259733689903/500000000000 : ℝ) (259733689907/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2303/16384 : ℝ)) hmem 8 (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ) (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2303/16384 : ℝ))) hcmem 8 (259733689903/500000000000 : ℝ) (259733689907/500000000000 : ℝ) (259733689903/500000000000 : ℝ) (259733689907/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2303/16384 : ℝ)) (990034902279/1000000000000 : ℝ) (495017451141/500000000000 : ℝ) (259733689903/500000000000 : ℝ) (259733689907/500000000000 : ℝ) (1318704947/1600000000 : ℝ) (824190591891/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0522_exp_lower
  have heNumeric : (1009504401011/500000000000 : ℝ)/4 ≤ Real.exp (-1367375324407/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009504401011/500000000000 : ℝ)/4 ≤ Real.exp ((1151/8192 : ℝ)-(824190591891/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1151/8192 : ℝ) (2303/16384 : ℝ) (824190591891/1000000000000 : ℝ) (1009504401011/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0523; no trusted numerical premise.
theorem cover7_leaf0523_exp_radius : (997491989612236971/1000000000000000000 : ℝ) ≤ Real.exp ((-9/448 : ℝ)/8) ∧ Real.exp ((-9/448 : ℝ)/8) ≤ (249372997403059243/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9/448 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0523_exp_lower : (918089132755687957/1000000000000000000 : ℝ) ≤ Real.exp ((-2734745554237/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734745554237/4000000000000 : ℝ)/8) ≤ (459044566377843979/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734745554237/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0523_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019011373523/1000000000000 : ℝ) ≤ 4*Real.exp (2303/16384 : ℝ)*Real.exp (-mu (radius 7 (9/64 : ℝ))) ∧ (2019/1000 : ℝ) < (2019011373523/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9/64 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0523_exp_radius
  have hrNumeric : (490055579737/500000000000 : ℝ) ≤ Real.exp (-9/448 : ℝ) ∧ Real.exp (-9/448 : ℝ) ≤ (39204446379/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490055579737/500000000000 : ℝ) ≤ (radius 7 (9/64 : ℝ)) ∧ (radius 7 (9/64 : ℝ)) ≤ (39204446379/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9/64 : ℝ)) (490055579737/500000000000 : ℝ) (39204446379/40000000000 : ℝ) (198449275817/1000000000000 : ℝ) (198449275823/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9/64 : ℝ)) (490055579737/500000000000 : ℝ) (39204446379/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9/64 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490055579737/500000000000 : ℝ) (39204446379/40000000000 : ℝ) (990055579737/1000000000000 : ℝ) (495027789869/500000000000 : ℝ) (990005636081/1000000000000 : ℝ) (990005636083/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9/64 : ℝ)) 1 (990055579737/1000000000000 : ℝ) (495027789869/500000000000 : ℝ) (990005636081/1000000000000 : ℝ) (990005636083/1000000000000 : ℝ) (990030607909/1000000000000 : ℝ) (990030607911/1000000000000 : ℝ) (495015303797/500000000000 : ℝ) (247507651899/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9/64 : ℝ)) 2 (990030607909/1000000000000 : ℝ) (990030607911/1000000000000 : ℝ) (495015303797/500000000000 : ℝ) (247507651899/250000000000 : ℝ) (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ) (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9/64 : ℝ)) 3 (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ) (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ) (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ) (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9/64 : ℝ)) 4 (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ) (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ) (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ) (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9/64 : ℝ)) 5 (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ) (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ) (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ) (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9/64 : ℝ)) 6 (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ) (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ) (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ) (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9/64 : ℝ)) 7 (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ) (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ) (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ) (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9/64 : ℝ))) (198449275817/1000000000000 : ℝ) (198449275823/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9/64 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (198449275817/1000000000000 : ℝ) (198449275823/1000000000000 : ℝ) (149806159477/250000000000 : ℝ) (74903079739/125000000000 : ℝ) (445476459329/1000000000000 : ℝ) (445476459337/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9/64 : ℝ))) 1 (149806159477/250000000000 : ℝ) (74903079739/125000000000 : ℝ) (445476459329/1000000000000 : ℝ) (445476459337/1000000000000 : ℝ) (261175274309/500000000000 : ℝ) (4178804389/8000000000 : ℝ) (129165705113/250000000000 : ℝ) (516662820459/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9/64 : ℝ))) 2 (261175274309/500000000000 : ℝ) (4178804389/8000000000 : ℝ) (129165705113/250000000000 : ℝ) (516662820459/1000000000000 : ℝ) (103901336907/200000000000 : ℝ) (259753342271/500000000000 : ℝ) (519498900589/1000000000000 : ℝ) (519498900597/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9/64 : ℝ))) 3 (103901336907/200000000000 : ℝ) (259753342271/500000000000 : ℝ) (519498900589/1000000000000 : ℝ) (519498900597/1000000000000 : ℝ) (259751396281/500000000000 : ℝ) (51950279257/100000000000 : ℝ) (519502792547/1000000000000 : ℝ) (103900558511/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9/64 : ℝ))) 4 (259751396281/500000000000 : ℝ) (51950279257/100000000000 : ℝ) (519502792547/1000000000000 : ℝ) (103900558511/200000000000 : ℝ) (259751396277/500000000000 : ℝ) (519502792563/1000000000000 : ℝ) (259751396277/500000000000 : ℝ) (519502792563/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9/64 : ℝ))) 5 (259751396277/500000000000 : ℝ) (519502792563/1000000000000 : ℝ) (259751396277/500000000000 : ℝ) (519502792563/1000000000000 : ℝ) (259751396277/500000000000 : ℝ) (519502792563/1000000000000 : ℝ) (259751396277/500000000000 : ℝ) (519502792563/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9/64 : ℝ))) 6 (259751396277/500000000000 : ℝ) (519502792563/1000000000000 : ℝ) (259751396277/500000000000 : ℝ) (519502792563/1000000000000 : ℝ) (259751396277/500000000000 : ℝ) (519502792563/1000000000000 : ℝ) (259751396277/500000000000 : ℝ) (519502792563/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9/64 : ℝ))) 7 (259751396277/500000000000 : ℝ) (519502792563/1000000000000 : ℝ) (259751396277/500000000000 : ℝ) (519502792563/1000000000000 : ℝ) (259751396277/500000000000 : ℝ) (519502792563/1000000000000 : ℝ) (259751396277/500000000000 : ℝ) (519502792563/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9/64 : ℝ)) hmem 8 (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ) (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9/64 : ℝ))) hcmem 8 (259751396277/500000000000 : ℝ) (519502792563/1000000000000 : ℝ) (259751396277/500000000000 : ℝ) (519502792563/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9/64 : ℝ)) (990030607751/1000000000000 : ℝ) (495015303877/500000000000 : ℝ) (259751396277/500000000000 : ℝ) (519502792563/1000000000000 : ℝ) (164850070677/200000000000 : ℝ) (824250353403/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0523_exp_lower
  have heNumeric : (2019011373523/1000000000000 : ℝ)/4 ≤ Real.exp (-2734745554237/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019011373523/1000000000000 : ℝ)/4 ≤ Real.exp ((2303/16384 : ℝ)-(824250353403/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2303/16384 : ℝ) (9/64 : ℝ) (824250353403/1000000000000 : ℝ) (2019011373523/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0524; no trusted numerical premise.
theorem cover7_leaf0524_exp_radius : (997490902432839363/1000000000000000000 : ℝ) ≤ Real.exp ((-2305/114688 : ℝ)/8) ∧ Real.exp ((-2305/114688 : ℝ)/8) ≤ (249372725608209841/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2305/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0524_exp_lower : (229522320226024899/250000000000000000 : ℝ) ≤ Real.exp ((-683685097631/1000000000000 : ℝ)/8) ∧ Real.exp ((-683685097631/1000000000000 : ℝ)/8) ≤ (918089280904099597/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683685097631/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0524_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019013979923/1000000000000 : ℝ) ≤ 4*Real.exp (9/64 : ℝ)*Real.exp (-mu (radius 7 (2305/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019013979923/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2305/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0524_exp_radius
  have hrNumeric : (980102613621/1000000000000 : ℝ) ≤ Real.exp (-2305/114688 : ℝ) ∧ Real.exp (-2305/114688 : ℝ) ≤ (490051306811/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980102613621/1000000000000 : ℝ) ≤ (radius 7 (2305/16384 : ℝ)) ∧ (radius 7 (2305/16384 : ℝ)) ≤ (490051306811/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2305/16384 : ℝ)) (980102613621/1000000000000 : ℝ) (490051306811/500000000000 : ℝ) (19849147783/100000000000 : ℝ) (49622869459/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2305/16384 : ℝ)) (980102613621/1000000000000 : ℝ) (490051306811/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2305/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980102613621/1000000000000 : ℝ) (490051306811/500000000000 : ℝ) (99005130681/100000000000 : ℝ) (990051306811/1000000000000 : ℝ) (990001320009/1000000000000 : ℝ) (990001320011/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2305/16384 : ℝ)) 1 (99005130681/100000000000 : ℝ) (990051306811/1000000000000 : ℝ) (990001320009/1000000000000 : ℝ) (990001320011/1000000000000 : ℝ) (990026313409/1000000000000 : ℝ) (990026313411/1000000000000 : ℝ) (495013156547/500000000000 : ℝ) (123753289137/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2305/16384 : ℝ)) 2 (990026313409/1000000000000 : ℝ) (990026313411/1000000000000 : ℝ) (495013156547/500000000000 : ℝ) (123753289137/125000000000 : ℝ) (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ) (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2305/16384 : ℝ)) 3 (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ) (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ) (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ) (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2305/16384 : ℝ)) 4 (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ) (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ) (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ) (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2305/16384 : ℝ)) 5 (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ) (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ) (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ) (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2305/16384 : ℝ)) 6 (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ) (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ) (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ) (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2305/16384 : ℝ)) 7 (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ) (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ) (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ) (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2305/16384 : ℝ))) (19849147783/100000000000 : ℝ) (49622869459/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2305/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19849147783/100000000000 : ℝ) (49622869459/250000000000 : ℝ) (119849147783/200000000000 : ℝ) (299622869459/500000000000 : ℝ) (55690478011/125000000000 : ℝ) (89104764819/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2305/16384 : ℝ))) 1 (119849147783/200000000000 : ℝ) (299622869459/500000000000 : ℝ) (55690478011/125000000000 : ℝ) (89104764819/200000000000 : ℝ) (522384781501/1000000000000 : ℝ) (522384781507/1000000000000 : ℝ) (64587422969/125000000000 : ℝ) (258349691879/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2305/16384 : ℝ))) 2 (522384781501/1000000000000 : ℝ) (522384781507/1000000000000 : ℝ) (64587422969/125000000000 : ℝ) (258349691879/500000000000 : ℝ) (259771041313/500000000000 : ℝ) (519542082633/1000000000000 : ℝ) (129883576397/250000000000 : ℝ) (103906861119/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2305/16384 : ℝ))) 3 (259771041313/500000000000 : ℝ) (519542082633/1000000000000 : ℝ) (129883576397/250000000000 : ℝ) (103906861119/200000000000 : ℝ) (519538194107/1000000000000 : ℝ) (259769097057/500000000000 : ℝ) (129884548523/250000000000 : ℝ) (5195381941/10000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2305/16384 : ℝ))) 4 (519538194107/1000000000000 : ℝ) (259769097057/500000000000 : ℝ) (129884548523/250000000000 : ℝ) (5195381941/10000000000 : ℝ) (519538194099/1000000000000 : ℝ) (519538194107/1000000000000 : ℝ) (519538194099/1000000000000 : ℝ) (519538194107/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2305/16384 : ℝ))) 5 (519538194099/1000000000000 : ℝ) (519538194107/1000000000000 : ℝ) (519538194099/1000000000000 : ℝ) (519538194107/1000000000000 : ℝ) (519538194099/1000000000000 : ℝ) (519538194107/1000000000000 : ℝ) (519538194099/1000000000000 : ℝ) (519538194107/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2305/16384 : ℝ))) 6 (519538194099/1000000000000 : ℝ) (519538194107/1000000000000 : ℝ) (519538194099/1000000000000 : ℝ) (519538194107/1000000000000 : ℝ) (519538194099/1000000000000 : ℝ) (519538194107/1000000000000 : ℝ) (519538194099/1000000000000 : ℝ) (519538194107/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2305/16384 : ℝ))) 7 (519538194099/1000000000000 : ℝ) (519538194107/1000000000000 : ℝ) (519538194099/1000000000000 : ℝ) (519538194107/1000000000000 : ℝ) (519538194099/1000000000000 : ℝ) (519538194107/1000000000000 : ℝ) (519538194099/1000000000000 : ℝ) (519538194107/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2305/16384 : ℝ)) hmem 8 (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ) (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2305/16384 : ℝ))) hcmem 8 (519538194099/1000000000000 : ℝ) (519538194107/1000000000000 : ℝ) (519538194099/1000000000000 : ℝ) (519538194107/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2305/16384 : ℝ)) (990026313251/1000000000000 : ℝ) (495013156627/500000000000 : ℝ) (519538194099/1000000000000 : ℝ) (519538194107/1000000000000 : ℝ) (164862019523/200000000000 : ℝ) (824310097631/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0524_exp_lower
  have heNumeric : (2019013979923/1000000000000 : ℝ)/4 ≤ Real.exp (-683685097631/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019013979923/1000000000000 : ℝ)/4 ≤ Real.exp ((9/64 : ℝ)-(824310097631/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9/64 : ℝ) (2305/16384 : ℝ) (824310097631/1000000000000 : ℝ) (2019013979923/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0500_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0500_certificate
#check SmaleRate.Proofs.cover7_leaf0501_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0501_certificate
#check SmaleRate.Proofs.cover7_leaf0502_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0502_certificate
#check SmaleRate.Proofs.cover7_leaf0503_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0503_certificate
#check SmaleRate.Proofs.cover7_leaf0504_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0504_certificate
#check SmaleRate.Proofs.cover7_leaf0505_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0505_certificate
#check SmaleRate.Proofs.cover7_leaf0506_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0506_certificate
#check SmaleRate.Proofs.cover7_leaf0507_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0507_certificate
#check SmaleRate.Proofs.cover7_leaf0508_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0508_certificate
#check SmaleRate.Proofs.cover7_leaf0509_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0509_certificate
#check SmaleRate.Proofs.cover7_leaf0510_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0510_certificate
#check SmaleRate.Proofs.cover7_leaf0511_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0511_certificate
#check SmaleRate.Proofs.cover7_leaf0512_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0512_certificate
#check SmaleRate.Proofs.cover7_leaf0513_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0513_certificate
#check SmaleRate.Proofs.cover7_leaf0514_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0514_certificate
#check SmaleRate.Proofs.cover7_leaf0515_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0515_certificate
#check SmaleRate.Proofs.cover7_leaf0516_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0516_certificate
#check SmaleRate.Proofs.cover7_leaf0517_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0517_certificate
#check SmaleRate.Proofs.cover7_leaf0518_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0518_certificate
#check SmaleRate.Proofs.cover7_leaf0519_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0519_certificate
#check SmaleRate.Proofs.cover7_leaf0520_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0520_certificate
#check SmaleRate.Proofs.cover7_leaf0521_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0521_certificate
#check SmaleRate.Proofs.cover7_leaf0522_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0522_certificate
#check SmaleRate.Proofs.cover7_leaf0523_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0523_certificate
#check SmaleRate.Proofs.cover7_leaf0524_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0524_certificate
