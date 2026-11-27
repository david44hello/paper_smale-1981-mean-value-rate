/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0125; no trusted numerical premise.
theorem cover8_leaf0125_exp_radius : (998070197140747673/1000000000000000000 : ℝ) ≤ Real.exp ((-4051/262144 : ℝ)/8) ∧ Real.exp ((-4051/262144 : ℝ)/8) ≤ (499035098570373837/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4051/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0125_exp_lower : (184023046612467097/200000000000000000 : ℝ) ≤ Real.exp ((-2664203630527/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664203630527/4000000000000 : ℝ)/8) ≤ (460057616531167743/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664203630527/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0125_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027466715231/500000000000 : ℝ) ≤ 4*Real.exp (2025/16384 : ℝ)*Real.exp (-mu (radius 8 (4051/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027466715231/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4051/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0125_exp_radius
  have hrNumeric : (39386618061/40000000000 : ℝ) ≤ Real.exp (-4051/262144 : ℝ) ∧ Real.exp (-4051/262144 : ℝ) ≤ (492332725763/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39386618061/40000000000 : ℝ) ≤ (radius 8 (4051/32768 : ℝ)) ∧ (radius 8 (4051/32768 : ℝ)) ≤ (492332725763/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4051/32768 : ℝ)) (39386618061/40000000000 : ℝ) (492332725763/500000000000 : ℝ) (174453284781/1000000000000 : ℝ) (43613321197/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4051/32768 : ℝ)) (39386618061/40000000000 : ℝ) (492332725763/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4051/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39386618061/40000000000 : ℝ) (492332725763/500000000000 : ℝ) (496166362881/500000000000 : ℝ) (992332725763/1000000000000 : ℝ) (992303104663/1000000000000 : ℝ) (198460620933/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4051/32768 : ℝ)) 1 (496166362881/500000000000 : ℝ) (992332725763/1000000000000 : ℝ) (992303104663/1000000000000 : ℝ) (198460620933/200000000000 : ℝ) (248079478803/250000000000 : ℝ) (496158957607/500000000000 : ℝ) (992317915101/1000000000000 : ℝ) (31009934847/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4051/32768 : ℝ)) 2 (248079478803/250000000000 : ℝ) (496158957607/500000000000 : ℝ) (992317915101/1000000000000 : ℝ) (31009934847/31250000000 : ℝ) (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ) (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4051/32768 : ℝ)) 3 (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ) (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ) (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ) (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4051/32768 : ℝ)) 4 (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ) (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ) (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ) (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4051/32768 : ℝ)) 5 (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ) (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ) (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ) (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4051/32768 : ℝ)) 6 (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ) (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ) (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ) (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4051/32768 : ℝ)) 7 (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ) (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ) (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ) (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4051/32768 : ℝ))) (174453284781/1000000000000 : ℝ) (43613321197/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4051/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174453284781/1000000000000 : ℝ) (43613321197/250000000000 : ℝ) (58722664239/100000000000 : ℝ) (293613321197/500000000000 : ℝ) (208838026219/500000000000 : ℝ) (13052376639/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4051/32768 : ℝ))) 1 (58722664239/100000000000 : ℝ) (293613321197/500000000000 : ℝ) (208838026219/500000000000 : ℝ) (13052376639/31250000000 : ℝ) (251225673707/500000000000 : ℝ) (502451347421/1000000000000 : ℝ) (9904958473/20000000000 : ℝ) (247623961829/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4051/32768 : ℝ))) 2 (251225673707/500000000000 : ℝ) (502451347421/1000000000000 : ℝ) (9904958473/20000000000 : ℝ) (247623961829/500000000000 : ℝ) (124712408883/250000000000 : ℝ) (24942481777/50000000000 : ℝ) (498836633119/1000000000000 : ℝ) (498836633127/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4051/32768 : ℝ))) 3 (124712408883/250000000000 : ℝ) (24942481777/50000000000 : ℝ) (498836633119/1000000000000 : ℝ) (498836633127/1000000000000 : ℝ) (19953725373/40000000000 : ℝ) (249421567167/500000000000 : ℝ) (498843134283/1000000000000 : ℝ) (124710783573/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4051/32768 : ℝ))) 4 (19953725373/40000000000 : ℝ) (249421567167/500000000000 : ℝ) (498843134283/1000000000000 : ℝ) (124710783573/250000000000 : ℝ) (15588847947/31250000000 : ℝ) (498843134313/1000000000000 : ℝ) (498843134303/1000000000000 : ℝ) (498843134313/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4051/32768 : ℝ))) 5 (15588847947/31250000000 : ℝ) (498843134313/1000000000000 : ℝ) (498843134303/1000000000000 : ℝ) (498843134313/1000000000000 : ℝ) (498843134303/1000000000000 : ℝ) (498843134313/1000000000000 : ℝ) (498843134303/1000000000000 : ℝ) (498843134313/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4051/32768 : ℝ))) 6 (498843134303/1000000000000 : ℝ) (498843134313/1000000000000 : ℝ) (498843134303/1000000000000 : ℝ) (498843134313/1000000000000 : ℝ) (498843134303/1000000000000 : ℝ) (498843134313/1000000000000 : ℝ) (498843134303/1000000000000 : ℝ) (498843134313/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4051/32768 : ℝ))) 7 (498843134303/1000000000000 : ℝ) (498843134313/1000000000000 : ℝ) (498843134303/1000000000000 : ℝ) (498843134313/1000000000000 : ℝ) (498843134303/1000000000000 : ℝ) (498843134313/1000000000000 : ℝ) (498843134303/1000000000000 : ℝ) (498843134313/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4051/32768 : ℝ)) hmem 8 (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ) (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4051/32768 : ℝ))) hcmem 8 (498843134303/1000000000000 : ℝ) (498843134313/1000000000000 : ℝ) (498843134303/1000000000000 : ℝ) (498843134313/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4051/32768 : ℝ)) (248079478789/250000000000 : ℝ) (992317915159/1000000000000 : ℝ) (498843134303/1000000000000 : ℝ) (498843134313/1000000000000 : ℝ) (789647099019/1000000000000 : ℝ) (394823549519/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0125_exp_lower
  have heNumeric : (1027466715231/500000000000 : ℝ)/4 ≤ Real.exp (-2664203630527/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027466715231/500000000000 : ℝ)/4 ≤ Real.exp ((2025/16384 : ℝ)-(394823549519/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2025/16384 : ℝ) (4051/32768 : ℝ) (394823549519/500000000000 : ℝ) (1027466715231/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0126; no trusted numerical premise.
theorem cover8_leaf0126_exp_radius : (124758715152988081/125000000000000000 : ℝ) ≤ Real.exp ((-1013/65536 : ℝ)/8) ∧ Real.exp ((-1013/65536 : ℝ)/8) ≤ (998069721223904649/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1013/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0126_exp_lower : (460057577953275143/500000000000000000 : ℝ) ≤ Real.exp ((-5328412627741/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328412627741/8000000000000 : ℝ)/8) ≤ (920115155906550287/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328412627741/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0126_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102746602597/50000000000 : ℝ) ≤ 4*Real.exp (4051/32768 : ℝ)*Real.exp (-mu (radius 8 (1013/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (102746602597/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1013/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0126_exp_radius
  have hrNumeric : (246165423833/250000000000 : ℝ) ≤ Real.exp (-1013/65536 : ℝ) ∧ Real.exp (-1013/65536 : ℝ) ≤ (984661695333/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246165423833/250000000000 : ℝ) ≤ (radius 8 (1013/8192 : ℝ)) ∧ (radius 8 (1013/8192 : ℝ)) ≤ (984661695333/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1013/8192 : ℝ)) (246165423833/250000000000 : ℝ) (984661695333/1000000000000 : ℝ) (87237242253/500000000000 : ℝ) (174474484513/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1013/8192 : ℝ)) (246165423833/250000000000 : ℝ) (984661695333/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1013/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246165423833/250000000000 : ℝ) (984661695333/1000000000000 : ℝ) (496165423833/500000000000 : ℝ) (992330847667/1000000000000 : ℝ) (992301211997/1000000000000 : ℝ) (992301211999/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1013/8192 : ℝ)) 1 (496165423833/500000000000 : ℝ) (992330847667/1000000000000 : ℝ) (992301211997/1000000000000 : ℝ) (992301211999/1000000000000 : ℝ) (992316029831/1000000000000 : ℝ) (992316029833/1000000000000 : ℝ) (24807900743/25000000000 : ℝ) (992316029723/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1013/8192 : ℝ)) 2 (992316029831/1000000000000 : ℝ) (992316029833/1000000000000 : ℝ) (24807900743/25000000000 : ℝ) (992316029723/1000000000000 : ℝ) (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ) (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1013/8192 : ℝ)) 3 (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ) (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ) (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ) (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1013/8192 : ℝ)) 4 (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ) (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ) (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ) (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1013/8192 : ℝ)) 5 (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ) (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ) (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ) (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1013/8192 : ℝ)) 6 (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ) (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ) (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ) (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1013/8192 : ℝ)) 7 (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ) (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ) (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ) (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1013/8192 : ℝ))) (87237242253/500000000000 : ℝ) (174474484513/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1013/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87237242253/500000000000 : ℝ) (174474484513/1000000000000 : ℝ) (587237242253/1000000000000 : ℝ) (587237242257/1000000000000 : ℝ) (208850714929/500000000000 : ℝ) (104425357467/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1013/8192 : ℝ))) 1 (587237242253/1000000000000 : ℝ) (587237242257/1000000000000 : ℝ) (208850714929/500000000000 : ℝ) (104425357467/250000000000 : ℝ) (100493867211/200000000000 : ℝ) (502469336063/1000000000000 : ℝ) (495267438617/1000000000000 : ℝ) (247633719313/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1013/8192 : ℝ))) 2 (100493867211/200000000000 : ℝ) (502469336063/1000000000000 : ℝ) (495267438617/1000000000000 : ℝ) (247633719313/500000000000 : ℝ) (62358548417/125000000000 : ℝ) (99773677469/200000000000 : ℝ) (498855390921/1000000000000 : ℝ) (498855390931/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1013/8192 : ℝ))) 3 (62358548417/125000000000 : ℝ) (99773677469/200000000000 : ℝ) (498855390921/1000000000000 : ℝ) (498855390931/1000000000000 : ℝ) (62357736141/125000000000 : ℝ) (249430944569/500000000000 : ℝ) (249430944543/500000000000 : ℝ) (62357736137/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1013/8192 : ℝ))) 4 (62357736141/125000000000 : ℝ) (249430944569/500000000000 : ℝ) (249430944543/500000000000 : ℝ) (62357736137/125000000000 : ℝ) (498861889107/1000000000000 : ℝ) (498861889117/1000000000000 : ℝ) (249430944553/500000000000 : ℝ) (498861889117/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1013/8192 : ℝ))) 5 (498861889107/1000000000000 : ℝ) (498861889117/1000000000000 : ℝ) (249430944553/500000000000 : ℝ) (498861889117/1000000000000 : ℝ) (249430944553/500000000000 : ℝ) (498861889117/1000000000000 : ℝ) (249430944553/500000000000 : ℝ) (498861889117/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1013/8192 : ℝ))) 6 (249430944553/500000000000 : ℝ) (498861889117/1000000000000 : ℝ) (249430944553/500000000000 : ℝ) (498861889117/1000000000000 : ℝ) (249430944553/500000000000 : ℝ) (498861889117/1000000000000 : ℝ) (249430944553/500000000000 : ℝ) (498861889117/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1013/8192 : ℝ))) 7 (249430944553/500000000000 : ℝ) (498861889117/1000000000000 : ℝ) (249430944553/500000000000 : ℝ) (498861889117/1000000000000 : ℝ) (249430944553/500000000000 : ℝ) (498861889117/1000000000000 : ℝ) (249430944553/500000000000 : ℝ) (498861889117/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1013/8192 : ℝ)) hmem 8 (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ) (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1013/8192 : ℝ))) hcmem 8 (249430944553/500000000000 : ℝ) (498861889117/1000000000000 : ℝ) (249430944553/500000000000 : ℝ) (498861889117/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1013/8192 : ℝ)) (39692641191/40000000000 : ℝ) (496158014889/500000000000 : ℝ) (249430944553/500000000000 : ℝ) (498861889117/1000000000000 : ℝ) (789678287431/1000000000000 : ℝ) (197419571863/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0126_exp_lower
  have heNumeric : (102746602597/50000000000 : ℝ)/4 ≤ Real.exp (-5328412627741/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102746602597/50000000000 : ℝ)/4 ≤ Real.exp ((4051/32768 : ℝ)-(197419571863/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4051/32768 : ℝ) (1013/8192 : ℝ) (197419571863/250000000000 : ℝ) (102746602597/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0127; no trusted numerical premise.
theorem cover8_leaf0127_exp_radius : (998069245307288559/1000000000000000000 : ℝ) ≤ Real.exp ((-4053/262144 : ℝ)/8) ∧ Real.exp ((-4053/262144 : ℝ)/8) ≤ (12475865566341107/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4053/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0127_exp_lower : (460057539676263409/500000000000000000 : ℝ) ≤ Real.exp ((-1332104488143/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332104488143/2000000000000 : ℝ)/8) ≤ (920115079352526819/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332104488143/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0127_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054930684169/1000000000000 : ℝ) ≤ 4*Real.exp (1013/8192 : ℝ)*Real.exp (-mu (radius 8 (4053/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054930684169/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4053/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0127_exp_radius
  have hrNumeric : (984657939153/1000000000000 : ℝ) ≤ Real.exp (-4053/262144 : ℝ) ∧ Real.exp (-4053/262144 : ℝ) ≤ (492328969577/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984657939153/1000000000000 : ℝ) ≤ (radius 8 (4053/32768 : ℝ)) ∧ (radius 8 (4053/32768 : ℝ)) ≤ (492328969577/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4053/32768 : ℝ)) (984657939153/1000000000000 : ℝ) (492328969577/500000000000 : ℝ) (21811960187/125000000000 : ℝ) (174495681503/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4053/32768 : ℝ)) (984657939153/1000000000000 : ℝ) (492328969577/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4053/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984657939153/1000000000000 : ℝ) (492328969577/500000000000 : ℝ) (124041121197/125000000000 : ℝ) (992328969577/1000000000000 : ℝ) (198459863867/200000000000 : ℝ) (124037414917/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4053/32768 : ℝ)) 1 (124041121197/125000000000 : ℝ) (992328969577/1000000000000 : ℝ) (198459863867/200000000000 : ℝ) (124037414917/125000000000 : ℝ) (198462828891/200000000000 : ℝ) (992314144457/1000000000000 : ℝ) (124039268043/125000000000 : ℝ) (496157072173/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4053/32768 : ℝ)) 2 (198462828891/200000000000 : ℝ) (992314144457/1000000000000 : ℝ) (124039268043/125000000000 : ℝ) (496157072173/500000000000 : ℝ) (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ) (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4053/32768 : ℝ)) 3 (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ) (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ) (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ) (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4053/32768 : ℝ)) 4 (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ) (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ) (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ) (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4053/32768 : ℝ)) 5 (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ) (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ) (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ) (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4053/32768 : ℝ)) 6 (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ) (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ) (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ) (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4053/32768 : ℝ)) 7 (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ) (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ) (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ) (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4053/32768 : ℝ))) (21811960187/125000000000 : ℝ) (174495681503/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4053/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (21811960187/125000000000 : ℝ) (174495681503/1000000000000 : ℝ) (146811960187/250000000000 : ℝ) (36702990047/62500000000 : ℝ) (417726802463/1000000000000 : ℝ) (52215850309/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4053/32768 : ℝ))) 1 (146811960187/250000000000 : ℝ) (36702990047/62500000000 : ℝ) (417726802463/1000000000000 : ℝ) (52215850309/125000000000 : ℝ) (100497464321/200000000000 : ℝ) (125621830403/250000000000 : ℝ) (495286949927/1000000000000 : ℝ) (30955434371/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4053/32768 : ℝ))) 2 (100497464321/200000000000 : ℝ) (125621830403/250000000000 : ℝ) (495286949927/1000000000000 : ℝ) (30955434371/62500000000 : ℝ) (249443567883/500000000000 : ℝ) (249443567887/500000000000 : ℝ) (249437072673/500000000000 : ℝ) (99774829071/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4053/32768 : ℝ))) 3 (249443567883/500000000000 : ℝ) (249443567887/500000000000 : ℝ) (249437072673/500000000000 : ℝ) (99774829071/200000000000 : ℝ) (124720160139/250000000000 : ℝ) (99776128113/200000000000 : ℝ) (498880640513/1000000000000 : ℝ) (498880640523/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4053/32768 : ℝ))) 4 (124720160139/250000000000 : ℝ) (99776128113/200000000000 : ℝ) (498880640513/1000000000000 : ℝ) (498880640523/1000000000000 : ℝ) (249440320267/500000000000 : ℝ) (15590020017/31250000000 : ℝ) (249440320267/500000000000 : ℝ) (15590020017/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4053/32768 : ℝ))) 5 (249440320267/500000000000 : ℝ) (15590020017/31250000000 : ℝ) (249440320267/500000000000 : ℝ) (15590020017/31250000000 : ℝ) (249440320267/500000000000 : ℝ) (15590020017/31250000000 : ℝ) (249440320267/500000000000 : ℝ) (15590020017/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4053/32768 : ℝ))) 6 (249440320267/500000000000 : ℝ) (15590020017/31250000000 : ℝ) (249440320267/500000000000 : ℝ) (15590020017/31250000000 : ℝ) (249440320267/500000000000 : ℝ) (15590020017/31250000000 : ℝ) (249440320267/500000000000 : ℝ) (15590020017/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4053/32768 : ℝ))) 7 (249440320267/500000000000 : ℝ) (15590020017/31250000000 : ℝ) (249440320267/500000000000 : ℝ) (15590020017/31250000000 : ℝ) (249440320267/500000000000 : ℝ) (15590020017/31250000000 : ℝ) (249440320267/500000000000 : ℝ) (15590020017/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4053/32768 : ℝ)) hmem 8 (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ) (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4053/32768 : ℝ))) hcmem 8 (249440320267/500000000000 : ℝ) (15590020017/31250000000 : ℝ) (249440320267/500000000000 : ℝ) (15590020017/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4053/32768 : ℝ)) (992314144399/1000000000000 : ℝ) (496157072201/500000000000 : ℝ) (249440320267/500000000000 : ℝ) (15590020017/31250000000 : ℝ) (157941894123/200000000000 : ℝ) (394854735317/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0127_exp_lower
  have heNumeric : (2054930684169/1000000000000 : ℝ)/4 ≤ Real.exp (-1332104488143/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054930684169/1000000000000 : ℝ)/4 ≤ Real.exp ((1013/8192 : ℝ)-(394854735317/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1013/8192 : ℝ) (4053/32768 : ℝ) (394854735317/500000000000 : ℝ) (2054930684169/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0128; no trusted numerical premise.
theorem cover8_leaf0128_exp_radius : (249517192347724851/250000000000000000 : ℝ) ≤ Real.exp ((-2027/131072 : ℝ)/8) ∧ Real.exp ((-2027/131072 : ℝ)/8) ≤ (199613753878179881/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2027/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0128_exp_lower : (115014375425004363/125000000000000000 : ℝ) ≤ Real.exp ((-5328423235563/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328423235563/8000000000000 : ℝ)/8) ≤ (184023000680006981/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328423235563/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0128_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054929327147/1000000000000 : ℝ) ≤ 4*Real.exp (4053/32768 : ℝ)*Real.exp (-mu (radius 8 (2027/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054929327147/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2027/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0128_exp_radius
  have hrNumeric : (246163545747/250000000000 : ℝ) ≤ Real.exp (-2027/131072 : ℝ) ∧ Real.exp (-2027/131072 : ℝ) ≤ (984654182989/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246163545747/250000000000 : ℝ) ≤ (radius 8 (2027/16384 : ℝ)) ∧ (radius 8 (2027/16384 : ℝ)) ≤ (984654182989/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2027/16384 : ℝ)) (246163545747/250000000000 : ℝ) (984654182989/1000000000000 : ℝ) (21814609469/125000000000 : ℝ) (87258437879/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2027/16384 : ℝ)) (246163545747/250000000000 : ℝ) (984654182989/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2027/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246163545747/250000000000 : ℝ) (984654182989/1000000000000 : ℝ) (496163545747/500000000000 : ℝ) (198465418299/200000000000 : ℝ) (248074356669/250000000000 : ℝ) (992297426677/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2027/16384 : ℝ)) 1 (496163545747/500000000000 : ℝ) (198465418299/200000000000 : ℝ) (248074356669/250000000000 : ℝ) (992297426677/1000000000000 : ℝ) (198462451817/200000000000 : ℝ) (496156129543/500000000000 : ℝ) (496156129487/500000000000 : ℝ) (31009758093/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2027/16384 : ℝ)) 2 (198462451817/200000000000 : ℝ) (496156129543/500000000000 : ℝ) (496156129487/500000000000 : ℝ) (31009758093/31250000000 : ℝ) (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ) (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2027/16384 : ℝ)) 3 (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ) (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ) (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ) (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2027/16384 : ℝ)) 4 (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ) (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ) (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ) (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2027/16384 : ℝ)) 5 (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ) (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ) (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ) (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2027/16384 : ℝ)) 6 (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ) (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ) (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ) (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2027/16384 : ℝ)) 7 (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ) (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ) (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ) (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2027/16384 : ℝ))) (21814609469/125000000000 : ℝ) (87258437879/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2027/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (21814609469/125000000000 : ℝ) (87258437879/500000000000 : ℝ) (146814609469/250000000000 : ℝ) (587258437879/1000000000000 : ℝ) (208876085127/500000000000 : ℝ) (208876085131/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2027/16384 : ℝ))) 1 (146814609469/250000000000 : ℝ) (587258437879/1000000000000 : ℝ) (208876085127/500000000000 : ℝ) (208876085131/500000000000 : ℝ) (100501060813/200000000000 : ℝ) (502505304071/1000000000000 : ℝ) (247653228791/500000000000 : ℝ) (495306457589/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2027/16384 : ℝ))) 2 (100501060813/200000000000 : ℝ) (502505304071/1000000000000 : ℝ) (247653228791/500000000000 : ℝ) (495306457589/1000000000000 : ℝ) (498905880823/1000000000000 : ℝ) (49890588083/100000000000 : ℝ) (249446448197/500000000000 : ℝ) (498892896401/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2027/16384 : ℝ))) 3 (498905880823/1000000000000 : ℝ) (49890588083/100000000000 : ℝ) (249446448197/500000000000 : ℝ) (498892896401/1000000000000 : ℝ) (7795302947/15625000000 : ℝ) (62362423577/125000000000 : ℝ) (249449694283/500000000000 : ℝ) (249449694287/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2027/16384 : ℝ))) 4 (7795302947/15625000000 : ℝ) (62362423577/125000000000 : ℝ) (249449694283/500000000000 : ℝ) (249449694287/500000000000 : ℝ) (498899388587/1000000000000 : ℝ) (99779877719/200000000000 : ℝ) (249449694293/500000000000 : ℝ) (99779877719/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2027/16384 : ℝ))) 5 (498899388587/1000000000000 : ℝ) (99779877719/200000000000 : ℝ) (249449694293/500000000000 : ℝ) (99779877719/200000000000 : ℝ) (249449694293/500000000000 : ℝ) (99779877719/200000000000 : ℝ) (249449694293/500000000000 : ℝ) (99779877719/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2027/16384 : ℝ))) 6 (249449694293/500000000000 : ℝ) (99779877719/200000000000 : ℝ) (249449694293/500000000000 : ℝ) (99779877719/200000000000 : ℝ) (249449694293/500000000000 : ℝ) (99779877719/200000000000 : ℝ) (249449694293/500000000000 : ℝ) (99779877719/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2027/16384 : ℝ))) 7 (249449694293/500000000000 : ℝ) (99779877719/200000000000 : ℝ) (249449694293/500000000000 : ℝ) (99779877719/200000000000 : ℝ) (249449694293/500000000000 : ℝ) (99779877719/200000000000 : ℝ) (249449694293/500000000000 : ℝ) (99779877719/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2027/16384 : ℝ)) hmem 8 (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ) (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2027/16384 : ℝ))) hcmem 8 (249449694293/500000000000 : ℝ) (99779877719/200000000000 : ℝ) (249449694293/500000000000 : ℝ) (99779877719/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2027/16384 : ℝ)) (992312259029/1000000000000 : ℝ) (992312259031/1000000000000 : ℝ) (249449694293/500000000000 : ℝ) (99779877719/200000000000 : ℝ) (78974064857/100000000000 : ℝ) (394870324293/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0128_exp_lower
  have heNumeric : (2054929327147/1000000000000 : ℝ)/4 ≤ Real.exp (-5328423235563/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054929327147/1000000000000 : ℝ)/4 ≤ Real.exp ((4053/32768 : ℝ)-(394870324293/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4053/32768 : ℝ) (2027/16384 : ℝ) (394870324293/500000000000 : ℝ) (2054929327147/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0129; no trusted numerical premise.
theorem cover8_leaf0129_exp_radius : (998068293474737183/1000000000000000000 : ℝ) ≤ Real.exp ((-4055/262144 : ℝ)/8) ∧ Real.exp ((-4055/262144 : ℝ)/8) ≤ (31189634171085537/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4055/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0129_exp_lower : (23002873201212483/25000000000000000 : ℝ) ≤ Real.exp ((-2664214238377/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664214238377/4000000000000 : ℝ)/8) ≤ (920114928048499321/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664214238377/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0129_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054927980863/1000000000000 : ℝ) ≤ 4*Real.exp (2027/16384 : ℝ)*Real.exp (-mu (radius 8 (4055/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054927980863/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4055/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0129_exp_radius
  have hrNumeric : (984650426837/1000000000000 : ℝ) ≤ Real.exp (-4055/262144 : ℝ) ∧ Real.exp (-4055/262144 : ℝ) ≤ (492325213419/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984650426837/1000000000000 : ℝ) ≤ (radius 8 (4055/32768 : ℝ)) ∧ (radius 8 (4055/32768 : ℝ)) ≤ (492325213419/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4055/32768 : ℝ)) (984650426837/1000000000000 : ℝ) (492325213419/500000000000 : ℝ) (87269033637/500000000000 : ℝ) (2181725841/12500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4055/32768 : ℝ)) (984650426837/1000000000000 : ℝ) (492325213419/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4055/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984650426837/1000000000000 : ℝ) (492325213419/500000000000 : ℝ) (496162606709/500000000000 : ℝ) (992325213419/1000000000000 : ℝ) (49614776701/50000000000 : ℝ) (992295534021/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4055/32768 : ℝ)) 1 (496162606709/500000000000 : ℝ) (992325213419/1000000000000 : ℝ) (49614776701/50000000000 : ℝ) (992295534021/1000000000000 : ℝ) (992310373719/1000000000000 : ℝ) (24807759343/25000000000 : ℝ) (124038796701/125000000000 : ℝ) (99231037361/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4055/32768 : ℝ)) 2 (992310373719/1000000000000 : ℝ) (24807759343/25000000000 : ℝ) (124038796701/125000000000 : ℝ) (99231037361/100000000000 : ℝ) (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ) (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4055/32768 : ℝ)) 3 (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ) (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ) (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ) (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4055/32768 : ℝ)) 4 (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ) (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ) (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ) (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4055/32768 : ℝ)) 5 (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ) (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ) (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ) (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4055/32768 : ℝ)) 6 (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ) (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ) (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ) (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4055/32768 : ℝ)) 7 (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ) (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ) (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ) (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4055/32768 : ℝ))) (87269033637/500000000000 : ℝ) (2181725841/12500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4055/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87269033637/500000000000 : ℝ) (2181725841/12500000000 : ℝ) (587269033637/1000000000000 : ℝ) (14681725841/25000000000 : ℝ) (26111095827/62500000000 : ℝ) (10444438331/25000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4055/32768 : ℝ))) 1 (587269033637/1000000000000 : ℝ) (14681725841/25000000000 : ℝ) (26111095827/62500000000 : ℝ) (10444438331/25000000000 : ℝ) (251261641717/500000000000 : ℝ) (6281541043/12500000000 : ℝ) (495325961581/1000000000000 : ℝ) (123831490397/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4055/32768 : ℝ))) 2 (251261641717/500000000000 : ℝ) (6281541043/12500000000 : ℝ) (495325961581/1000000000000 : ℝ) (123831490397/250000000000 : ℝ) (498924622507/1000000000000 : ℝ) (249462311257/500000000000 : ℝ) (99782328813/200000000000 : ℝ) (62363955509/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4055/32768 : ℝ))) 3 (498924622507/1000000000000 : ℝ) (249462311257/500000000000 : ℝ) (99782328813/200000000000 : ℝ) (62363955509/125000000000 : ℝ) (249459066643/500000000000 : ℝ) (498918133293/1000000000000 : ℝ) (498918133243/1000000000000 : ℝ) (498918133251/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4055/32768 : ℝ))) 4 (249459066643/500000000000 : ℝ) (498918133293/1000000000000 : ℝ) (498918133243/1000000000000 : ℝ) (498918133251/1000000000000 : ℝ) (31182383329/62500000000 : ℝ) (62364766659/125000000000 : ℝ) (31182383329/62500000000 : ℝ) (62364766659/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4055/32768 : ℝ))) 5 (31182383329/62500000000 : ℝ) (62364766659/125000000000 : ℝ) (31182383329/62500000000 : ℝ) (62364766659/125000000000 : ℝ) (31182383329/62500000000 : ℝ) (62364766659/125000000000 : ℝ) (31182383329/62500000000 : ℝ) (62364766659/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4055/32768 : ℝ))) 6 (31182383329/62500000000 : ℝ) (62364766659/125000000000 : ℝ) (31182383329/62500000000 : ℝ) (62364766659/125000000000 : ℝ) (31182383329/62500000000 : ℝ) (62364766659/125000000000 : ℝ) (31182383329/62500000000 : ℝ) (62364766659/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4055/32768 : ℝ))) 7 (31182383329/62500000000 : ℝ) (62364766659/125000000000 : ℝ) (31182383329/62500000000 : ℝ) (62364766659/125000000000 : ℝ) (31182383329/62500000000 : ℝ) (62364766659/125000000000 : ℝ) (31182383329/62500000000 : ℝ) (62364766659/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4055/32768 : ℝ)) hmem 8 (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ) (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4055/32768 : ℝ))) hcmem 8 (31182383329/62500000000 : ℝ) (62364766659/125000000000 : ℝ) (31182383329/62500000000 : ℝ) (62364766659/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4055/32768 : ℝ)) (992310373663/1000000000000 : ℝ) (198462074733/200000000000 : ℝ) (31182383329/62500000000 : ℝ) (62364766659/125000000000 : ℝ) (394885910649/500000000000 : ℝ) (789771821313/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0129_exp_lower
  have heNumeric : (2054927980863/1000000000000 : ℝ)/4 ≤ Real.exp (-2664214238377/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054927980863/1000000000000 : ℝ)/4 ≤ Real.exp ((2027/16384 : ℝ)-(789771821313/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2027/16384 : ℝ) (4055/32768 : ℝ) (789771821313/1000000000000 : ℝ) (2054927980863/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0130; no trusted numerical premise.
theorem cover8_leaf0130_exp_radius : (998067817558801897/1000000000000000000 : ℝ) ≤ Real.exp ((-507/32768 : ℝ)/8) ∧ Real.exp ((-507/32768 : ℝ)/8) ≤ (499033908779400949/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-507/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0130_exp_lower : (920114853298379979/1000000000000000000 : ℝ) ≤ Real.exp ((-5328433676113/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328433676113/8000000000000 : ℝ)/8) ≤ (46005742664918999/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328433676113/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0130_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (82197065813/40000000000 : ℝ) ≤ 4*Real.exp (4055/32768 : ℝ)*Real.exp (-mu (radius 8 (507/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (82197065813/40000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (507/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0130_exp_radius
  have hrNumeric : (984646670701/1000000000000 : ℝ) ≤ Real.exp (-507/32768 : ℝ) ∧ Real.exp (-507/32768 : ℝ) ≤ (492323335351/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984646670701/1000000000000 : ℝ) ≤ (radius 8 (507/4096 : ℝ)) ∧ (radius 8 (507/4096 : ℝ)) ≤ (492323335351/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (507/4096 : ℝ)) (984646670701/1000000000000 : ℝ) (492323335351/500000000000 : ℝ) (174559256057/1000000000000 : ℝ) (340936047/1953125000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (507/4096 : ℝ)) (984646670701/1000000000000 : ℝ) (492323335351/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (507/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984646670701/1000000000000 : ℝ) (492323335351/500000000000 : ℝ) (19846466707/20000000000 : ℝ) (992323335351/1000000000000 : ℝ) (124036705171/125000000000 : ℝ) (99229364137/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (507/4096 : ℝ)) 1 (19846466707/20000000000 : ℝ) (992323335351/1000000000000 : ℝ) (124036705171/125000000000 : ℝ) (99229364137/100000000000 : ℝ) (992308488359/1000000000000 : ℝ) (992308488361/1000000000000 : ℝ) (992308488247/1000000000000 : ℝ) (3969233953/4000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (507/4096 : ℝ)) 2 (992308488359/1000000000000 : ℝ) (992308488361/1000000000000 : ℝ) (992308488247/1000000000000 : ℝ) (3969233953/4000000000 : ℝ) (992308488303/1000000000000 : ℝ) (496154244153/500000000000 : ℝ) (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (507/4096 : ℝ)) 3 (992308488303/1000000000000 : ℝ) (496154244153/500000000000 : ℝ) (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ) (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ) (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (507/4096 : ℝ)) 4 (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ) (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ) (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ) (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (507/4096 : ℝ)) 5 (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ) (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ) (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ) (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (507/4096 : ℝ)) 6 (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ) (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ) (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ) (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (507/4096 : ℝ)) 7 (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ) (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ) (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ) (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (507/4096 : ℝ))) (174559256057/1000000000000 : ℝ) (340936047/1953125000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (507/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174559256057/1000000000000 : ℝ) (340936047/1953125000 : ℝ) (146819907007/250000000000 : ℝ) (2294061047/3906250000 : ℝ) (417802891393/1000000000000 : ℝ) (417802891403/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (507/4096 : ℝ))) 1 (146819907007/250000000000 : ℝ) (2294061047/3906250000 : ℝ) (417802891393/1000000000000 : ℝ) (417802891403/1000000000000 : ℝ) (50254125971/100000000000 : ℝ) (251270629859/500000000000 : ℝ) (495345461921/1000000000000 : ℝ) (49534546193/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (507/4096 : ℝ))) 2 (50254125971/100000000000 : ℝ) (251270629859/500000000000 : ℝ) (495345461921/1000000000000 : ℝ) (49534546193/100000000000 : ℝ) (99788672163/200000000000 : ℝ) (62367920103/125000000000 : ℝ) (124732597089/250000000000 : ℝ) (99786077673/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (507/4096 : ℝ))) 3 (99788672163/200000000000 : ℝ) (62367920103/125000000000 : ℝ) (124732597089/250000000000 : ℝ) (99786077673/200000000000 : ℝ) (99787374917/200000000000 : ℝ) (99787374919/200000000000 : ℝ) (498936874543/1000000000000 : ℝ) (498936874553/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (507/4096 : ℝ))) 4 (99787374917/200000000000 : ℝ) (99787374919/200000000000 : ℝ) (498936874543/1000000000000 : ℝ) (498936874553/1000000000000 : ℝ) (124734218641/250000000000 : ℝ) (249468437287/500000000000 : ℝ) (498936874563/1000000000000 : ℝ) (249468437287/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (507/4096 : ℝ))) 5 (124734218641/250000000000 : ℝ) (249468437287/500000000000 : ℝ) (498936874563/1000000000000 : ℝ) (249468437287/500000000000 : ℝ) (498936874563/1000000000000 : ℝ) (249468437287/500000000000 : ℝ) (498936874563/1000000000000 : ℝ) (249468437287/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (507/4096 : ℝ))) 6 (498936874563/1000000000000 : ℝ) (249468437287/500000000000 : ℝ) (498936874563/1000000000000 : ℝ) (249468437287/500000000000 : ℝ) (498936874563/1000000000000 : ℝ) (249468437287/500000000000 : ℝ) (498936874563/1000000000000 : ℝ) (249468437287/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (507/4096 : ℝ))) 7 (498936874563/1000000000000 : ℝ) (249468437287/500000000000 : ℝ) (498936874563/1000000000000 : ℝ) (249468437287/500000000000 : ℝ) (498936874563/1000000000000 : ℝ) (249468437287/500000000000 : ℝ) (498936874563/1000000000000 : ℝ) (249468437287/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (507/4096 : ℝ)) hmem 8 (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ) (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (507/4096 : ℝ))) hcmem 8 (498936874563/1000000000000 : ℝ) (249468437287/500000000000 : ℝ) (498936874563/1000000000000 : ℝ) (249468437287/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (507/4096 : ℝ)) (496154244151/500000000000 : ℝ) (496154244153/500000000000 : ℝ) (498936874563/1000000000000 : ℝ) (249468437287/500000000000 : ℝ) (78980298879/100000000000 : ℝ) (789802988811/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0130_exp_lower
  have heNumeric : (82197065813/40000000000 : ℝ)/4 ≤ Real.exp (-5328433676113/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (82197065813/40000000000 : ℝ)/4 ≤ Real.exp ((4055/32768 : ℝ)-(789802988811/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4055/32768 : ℝ) (507/4096 : ℝ) (789802988811/1000000000000 : ℝ) (82197065813/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0131; no trusted numerical premise.
theorem cover8_leaf0131_exp_radius : (499033670821546773/500000000000000000 : ℝ) ≤ Real.exp ((-4057/262144 : ℝ)/8) ∧ Real.exp ((-4057/262144 : ℝ)/8) ≤ (998067341643093547/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4057/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0131_exp_lower : (920114779149101661/1000000000000000000 : ℝ) ≤ Real.exp ((-66605485421/100000000000 : ℝ)/8) ∧ Real.exp ((-66605485421/100000000000 : ℝ)/8) ≤ (460057389574550831/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66605485421/100000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0131_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054925320523/1000000000000 : ℝ) ≤ 4*Real.exp (507/4096 : ℝ)*Real.exp (-mu (radius 8 (4057/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054925320523/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4057/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0131_exp_radius
  have hrNumeric : (984642914579/1000000000000 : ℝ) ≤ Real.exp (-4057/262144 : ℝ) ∧ Real.exp (-4057/262144 : ℝ) ≤ (49232145729/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984642914579/1000000000000 : ℝ) ≤ (radius 8 (4057/32768 : ℝ)) ∧ (radius 8 (4057/32768 : ℝ)) ≤ (49232145729/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4057/32768 : ℝ)) (984642914579/1000000000000 : ℝ) (49232145729/50000000000 : ℝ) (17458044211/100000000000 : ℝ) (43645110529/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4057/32768 : ℝ)) (984642914579/1000000000000 : ℝ) (49232145729/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4057/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984642914579/1000000000000 : ℝ) (49232145729/50000000000 : ℝ) (992321457289/1000000000000 : ℝ) (99232145729/100000000000 : ℝ) (12403646859/12500000000 : ℝ) (496145874361/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4057/32768 : ℝ)) 1 (992321457289/1000000000000 : ℝ) (99232145729/100000000000 : ℝ) (12403646859/12500000000 : ℝ) (496145874361/500000000000 : ℝ) (248076650751/250000000000 : ℝ) (496153301503/500000000000 : ℝ) (992306602893/1000000000000 : ℝ) (198461320579/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4057/32768 : ℝ)) 2 (248076650751/250000000000 : ℝ) (496153301503/500000000000 : ℝ) (992306602893/1000000000000 : ℝ) (198461320579/200000000000 : ℝ) (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ) (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4057/32768 : ℝ)) 3 (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ) (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ) (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ) (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4057/32768 : ℝ)) 4 (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ) (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ) (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ) (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4057/32768 : ℝ)) 5 (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ) (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ) (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ) (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4057/32768 : ℝ)) 6 (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ) (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ) (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ) (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4057/32768 : ℝ)) 7 (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ) (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ) (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ) (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4057/32768 : ℝ))) (17458044211/100000000000 : ℝ) (43645110529/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4057/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17458044211/100000000000 : ℝ) (43645110529/250000000000 : ℝ) (117458044211/200000000000 : ℝ) (293645110529/500000000000 : ℝ) (104457061187/250000000000 : ℝ) (417828244757/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4057/32768 : ℝ))) 1 (117458044211/200000000000 : ℝ) (293645110529/500000000000 : ℝ) (104457061187/250000000000 : ℝ) (417828244757/1000000000000 : ℝ) (502559232901/1000000000000 : ℝ) (125639808227/250000000000 : ℝ) (123841239653/250000000000 : ℝ) (24768247931/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4057/32768 : ℝ))) 2 (502559232901/1000000000000 : ℝ) (125639808227/250000000000 : ℝ) (123841239653/250000000000 : ℝ) (24768247931/50000000000 : ℝ) (124740523939/250000000000 : ℝ) (124740523941/250000000000 : ℝ) (124737282319/250000000000 : ℝ) (99789825857/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4057/32768 : ℝ))) 3 (124740523939/250000000000 : ℝ) (124740523941/250000000000 : ℝ) (124737282319/250000000000 : ℝ) (99789825857/200000000000 : ℝ) (124738903129/250000000000 : ℝ) (19958224501/40000000000 : ℝ) (498955612473/1000000000000 : ℝ) (498955612483/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4057/32768 : ℝ))) 4 (124738903129/250000000000 : ℝ) (19958224501/40000000000 : ℝ) (498955612473/1000000000000 : ℝ) (498955612483/1000000000000 : ℝ) (249477806247/500000000000 : ℝ) (62369451563/125000000000 : ℝ) (249477806247/500000000000 : ℝ) (62369451563/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4057/32768 : ℝ))) 5 (249477806247/500000000000 : ℝ) (62369451563/125000000000 : ℝ) (249477806247/500000000000 : ℝ) (62369451563/125000000000 : ℝ) (249477806247/500000000000 : ℝ) (62369451563/125000000000 : ℝ) (249477806247/500000000000 : ℝ) (62369451563/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4057/32768 : ℝ))) 6 (249477806247/500000000000 : ℝ) (62369451563/125000000000 : ℝ) (249477806247/500000000000 : ℝ) (62369451563/125000000000 : ℝ) (249477806247/500000000000 : ℝ) (62369451563/125000000000 : ℝ) (249477806247/500000000000 : ℝ) (62369451563/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4057/32768 : ℝ))) 7 (249477806247/500000000000 : ℝ) (62369451563/125000000000 : ℝ) (249477806247/500000000000 : ℝ) (62369451563/125000000000 : ℝ) (249477806247/500000000000 : ℝ) (62369451563/125000000000 : ℝ) (249477806247/500000000000 : ℝ) (62369451563/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4057/32768 : ℝ)) hmem 8 (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ) (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4057/32768 : ℝ))) hcmem 8 (249477806247/500000000000 : ℝ) (62369451563/125000000000 : ℝ) (249477806247/500000000000 : ℝ) (62369451563/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4057/32768 : ℝ)) (248076650737/250000000000 : ℝ) (992306602951/1000000000000 : ℝ) (249477806247/500000000000 : ℝ) (62369451563/125000000000 : ℝ) (394917075533/500000000000 : ℝ) (157966830217/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0131_exp_lower
  have heNumeric : (2054925320523/1000000000000 : ℝ)/4 ≤ Real.exp (-66605485421/100000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054925320523/1000000000000 : ℝ)/4 ≤ Real.exp ((507/4096 : ℝ)-(157966830217/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (507/4096 : ℝ) (4057/32768 : ℝ) (157966830217/200000000000 : ℝ) (2054925320523/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0132; no trusted numerical premise.
theorem cover8_leaf0132_exp_radius : (31189589553987879/31250000000000000 : ℝ) ≤ Real.exp ((-2029/131072 : ℝ)/8) ∧ Real.exp ((-2029/131072 : ℝ)/8) ≤ (998066865727612129/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2029/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0132_exp_lower : (57507169100063079/62500000000000000 : ℝ) ≤ Real.exp ((-5328443949431/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328443949431/8000000000000 : ℝ)/8) ≤ (184022941120201853/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328443949431/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0132_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027462003231/500000000000 : ℝ) ≤ 4*Real.exp (4057/32768 : ℝ)*Real.exp (-mu (radius 8 (2029/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027462003231/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2029/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0132_exp_radius
  have hrNumeric : (123079894809/125000000000 : ℝ) ≤ Real.exp (-2029/131072 : ℝ) ∧ Real.exp (-2029/131072 : ℝ) ≤ (984639158473/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123079894809/125000000000 : ℝ) ≤ (radius 8 (2029/16384 : ℝ)) ∧ (radius 8 (2029/16384 : ℝ)) ≤ (984639158473/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2029/16384 : ℝ)) (123079894809/125000000000 : ℝ) (984639158473/1000000000000 : ℝ) (87300812713/500000000000 : ℝ) (174601625433/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2029/16384 : ℝ)) (123079894809/125000000000 : ℝ) (984639158473/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2029/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123079894809/125000000000 : ℝ) (984639158473/1000000000000 : ℝ) (248079894809/250000000000 : ℝ) (992319579237/1000000000000 : ℝ) (248072464019/250000000000 : ℝ) (992289856077/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2029/16384 : ℝ)) 1 (248079894809/250000000000 : ℝ) (992319579237/1000000000000 : ℝ) (248072464019/250000000000 : ℝ) (992289856077/1000000000000 : ℝ) (124038089707/125000000000 : ℝ) (992304717657/1000000000000 : ℝ) (124038089693/125000000000 : ℝ) (496152358773/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2029/16384 : ℝ)) 2 (124038089707/125000000000 : ℝ) (992304717657/1000000000000 : ℝ) (124038089693/125000000000 : ℝ) (496152358773/500000000000 : ℝ) (1240380897/1250000000 : ℝ) (496152358801/500000000000 : ℝ) (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2029/16384 : ℝ)) 3 (1240380897/1250000000 : ℝ) (496152358801/500000000000 : ℝ) (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ) (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ) (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2029/16384 : ℝ)) 4 (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ) (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ) (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ) (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2029/16384 : ℝ)) 5 (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ) (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ) (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ) (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2029/16384 : ℝ)) 6 (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ) (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ) (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ) (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2029/16384 : ℝ)) 7 (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ) (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ) (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ) (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2029/16384 : ℝ))) (87300812713/500000000000 : ℝ) (174601625433/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2029/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87300812713/500000000000 : ℝ) (174601625433/1000000000000 : ℝ) (587300812713/1000000000000 : ℝ) (587300812717/1000000000000 : ℝ) (41785359329/100000000000 : ℝ) (4178535933/10000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2029/16384 : ℝ))) 1 (587300812713/1000000000000 : ℝ) (587300812717/1000000000000 : ℝ) (41785359329/100000000000 : ℝ) (4178535933/10000000000 : ℝ) (502577203001/1000000000000 : ℝ) (502577203009/1000000000000 : ℝ) (495384451647/1000000000000 : ℝ) (61923056457/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2029/16384 : ℝ))) 2 (502577203001/1000000000000 : ℝ) (502577203009/1000000000000 : ℝ) (495384451647/1000000000000 : ℝ) (61923056457/125000000000 : ℝ) (124745206831/250000000000 : ℝ) (498980827333/1000000000000 : ℝ) (24948393341/50000000000 : ℝ) (498967866829/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2029/16384 : ℝ))) 3 (124745206831/250000000000 : ℝ) (498980827333/1000000000000 : ℝ) (24948393341/50000000000 : ℝ) (498967866829/1000000000000 : ℝ) (7796474173/15625000000 : ℝ) (498974347081/1000000000000 : ℝ) (498974347029/1000000000000 : ℝ) (498974347039/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2029/16384 : ℝ))) 4 (7796474173/15625000000 : ℝ) (498974347081/1000000000000 : ℝ) (498974347029/1000000000000 : ℝ) (498974347039/1000000000000 : ℝ) (9979486941/20000000000 : ℝ) (24948717353/50000000000 : ℝ) (9979486941/20000000000 : ℝ) (24948717353/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2029/16384 : ℝ))) 5 (9979486941/20000000000 : ℝ) (24948717353/50000000000 : ℝ) (9979486941/20000000000 : ℝ) (24948717353/50000000000 : ℝ) (9979486941/20000000000 : ℝ) (24948717353/50000000000 : ℝ) (9979486941/20000000000 : ℝ) (24948717353/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2029/16384 : ℝ))) 6 (9979486941/20000000000 : ℝ) (24948717353/50000000000 : ℝ) (9979486941/20000000000 : ℝ) (24948717353/50000000000 : ℝ) (9979486941/20000000000 : ℝ) (24948717353/50000000000 : ℝ) (9979486941/20000000000 : ℝ) (24948717353/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2029/16384 : ℝ))) 7 (9979486941/20000000000 : ℝ) (24948717353/50000000000 : ℝ) (9979486941/20000000000 : ℝ) (24948717353/50000000000 : ℝ) (9979486941/20000000000 : ℝ) (24948717353/50000000000 : ℝ) (9979486941/20000000000 : ℝ) (24948717353/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2029/16384 : ℝ)) hmem 8 (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ) (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2029/16384 : ℝ))) hcmem 8 (9979486941/20000000000 : ℝ) (24948717353/50000000000 : ℝ) (9979486941/20000000000 : ℝ) (24948717353/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2029/16384 : ℝ)) (992304717599/1000000000000 : ℝ) (496152358801/500000000000 : ℝ) (9979486941/20000000000 : ℝ) (24948717353/50000000000 : ℝ) (789865308113/1000000000000 : ℝ) (197466327033/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0132_exp_lower
  have heNumeric : (1027462003231/500000000000 : ℝ)/4 ≤ Real.exp (-5328443949431/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027462003231/500000000000 : ℝ)/4 ≤ Real.exp ((4057/32768 : ℝ)-(197466327033/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4057/32768 : ℝ) (2029/16384 : ℝ) (197466327033/250000000000 : ℝ) (1027462003231/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0133; no trusted numerical premise.
theorem cover8_leaf0133_exp_radius : (199613277962471529/200000000000000000 : ℝ) ≤ Real.exp ((-4059/262144 : ℝ)/8) ∧ Real.exp ((-4059/262144 : ℝ)/8) ≤ (499033194906178823/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4059/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0133_exp_lower : (920114632653182529/1000000000000000000 : ℝ) ≤ Real.exp ((-532844902343/800000000000 : ℝ)/8) ∧ Real.exp ((-532844902343/800000000000 : ℝ)/8) ≤ (92011463265318253/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-532844902343/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0133_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256865337891/125000000000 : ℝ) ≤ 4*Real.exp (2029/16384 : ℝ)*Real.exp (-mu (radius 8 (4059/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (256865337891/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4059/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0133_exp_radius
  have hrNumeric : (984635402379/1000000000000 : ℝ) ≤ Real.exp (-4059/262144 : ℝ) ∧ Real.exp (-4059/262144 : ℝ) ≤ (49231770119/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984635402379/1000000000000 : ℝ) ≤ (radius 8 (4059/32768 : ℝ)) ∧ (radius 8 (4059/32768 : ℝ)) ≤ (49231770119/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4059/32768 : ℝ)) (984635402379/1000000000000 : ℝ) (49231770119/50000000000 : ℝ) (174622806013/1000000000000 : ℝ) (174622806019/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4059/32768 : ℝ)) (984635402379/1000000000000 : ℝ) (49231770119/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4059/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984635402379/1000000000000 : ℝ) (49231770119/50000000000 : ℝ) (992317701189/1000000000000 : ℝ) (99231770119/100000000000 : ℝ) (198457592687/200000000000 : ℝ) (992287963437/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4059/32768 : ℝ)) 1 (992317701189/1000000000000 : ℝ) (99231770119/100000000000 : ℝ) (198457592687/200000000000 : ℝ) (992287963437/1000000000000 : ℝ) (124037854039/125000000000 : ℝ) (496151416157/500000000000 : ℝ) (4961514161/5000000000 : ℝ) (992302832203/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4059/32768 : ℝ)) 2 (124037854039/125000000000 : ℝ) (496151416157/500000000000 : ℝ) (4961514161/5000000000 : ℝ) (992302832203/1000000000000 : ℝ) (7752365877/7812500000 : ℝ) (992302832259/1000000000000 : ℝ) (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4059/32768 : ℝ)) 3 (7752365877/7812500000 : ℝ) (992302832259/1000000000000 : ℝ) (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ) (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ) (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4059/32768 : ℝ)) 4 (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ) (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ) (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ) (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4059/32768 : ℝ)) 5 (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ) (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ) (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ) (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4059/32768 : ℝ)) 6 (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ) (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ) (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ) (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4059/32768 : ℝ)) 7 (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ) (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ) (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ) (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4059/32768 : ℝ))) (174622806013/1000000000000 : ℝ) (174622806019/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4059/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174622806013/1000000000000 : ℝ) (174622806019/1000000000000 : ℝ) (293655701503/500000000000 : ℝ) (58731140301/100000000000 : ℝ) (417878937029/1000000000000 : ℝ) (417878937037/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4059/32768 : ℝ))) 1 (293655701503/500000000000 : ℝ) (58731140301/100000000000 : ℝ) (417878937029/1000000000000 : ℝ) (417878937037/1000000000000 : ℝ) (502595170017/1000000000000 : ℝ) (62824396253/125000000000 : ℝ) (99080788207/200000000000 : ℝ) (247701970521/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4059/32768 : ℝ))) 2 (502595170017/1000000000000 : ℝ) (62824396253/125000000000 : ℝ) (99080788207/200000000000 : ℝ) (247701970521/500000000000 : ℝ) (249499777763/500000000000 : ℝ) (498999555533/1000000000000 : ℝ) (249493300497/500000000000 : ℝ) (249493300501/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4059/32768 : ℝ))) 3 (249499777763/500000000000 : ℝ) (498999555533/1000000000000 : ℝ) (249493300497/500000000000 : ℝ) (249493300501/500000000000 : ℝ) (24949653913/50000000000 : ℝ) (124748269567/250000000000 : ℝ) (498993078217/1000000000000 : ℝ) (249496539113/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4059/32768 : ℝ))) 4 (24949653913/50000000000 : ℝ) (124748269567/250000000000 : ℝ) (498993078217/1000000000000 : ℝ) (249496539113/500000000000 : ℝ) (249496539119/500000000000 : ℝ) (498993078247/1000000000000 : ℝ) (249496539119/500000000000 : ℝ) (498993078247/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4059/32768 : ℝ))) 5 (249496539119/500000000000 : ℝ) (498993078247/1000000000000 : ℝ) (249496539119/500000000000 : ℝ) (498993078247/1000000000000 : ℝ) (249496539119/500000000000 : ℝ) (498993078247/1000000000000 : ℝ) (249496539119/500000000000 : ℝ) (498993078247/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4059/32768 : ℝ))) 6 (249496539119/500000000000 : ℝ) (498993078247/1000000000000 : ℝ) (249496539119/500000000000 : ℝ) (498993078247/1000000000000 : ℝ) (249496539119/500000000000 : ℝ) (498993078247/1000000000000 : ℝ) (249496539119/500000000000 : ℝ) (498993078247/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4059/32768 : ℝ))) 7 (249496539119/500000000000 : ℝ) (498993078247/1000000000000 : ℝ) (249496539119/500000000000 : ℝ) (498993078247/1000000000000 : ℝ) (249496539119/500000000000 : ℝ) (498993078247/1000000000000 : ℝ) (249496539119/500000000000 : ℝ) (498993078247/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4059/32768 : ℝ)) hmem 8 (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ) (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4059/32768 : ℝ))) hcmem 8 (249496539119/500000000000 : ℝ) (498993078247/1000000000000 : ℝ) (249496539119/500000000000 : ℝ) (498993078247/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4059/32768 : ℝ)) (198460566451/200000000000 : ℝ) (992302832259/1000000000000 : ℝ) (249496539119/500000000000 : ℝ) (498993078247/1000000000000 : ℝ) (394948229971/500000000000 : ℝ) (19747411499/25000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0133_exp_lower
  have heNumeric : (256865337891/125000000000 : ℝ)/4 ≤ Real.exp (-532844902343/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256865337891/125000000000 : ℝ)/4 ≤ Real.exp ((2029/16384 : ℝ)-(19747411499/25000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2029/16384 : ℝ) (4059/32768 : ℝ) (19747411499/25000000000 : ℝ) (256865337891/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0134; no trusted numerical premise.
theorem cover8_leaf0134_exp_radius : (62379119618583131/62500000000000000 : ℝ) ≤ Real.exp ((-1015/65536 : ℝ)/8) ∧ Real.exp ((-1015/65536 : ℝ)/8) ≤ (998065913897330097/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1015/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0134_exp_lower : (920114560304816213/1000000000000000000 : ℝ) ≤ Real.exp ((-5328454055733/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328454055733/8000000000000 : ℝ)/8) ≤ (460057280152408107/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328454055733/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0134_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256865176313/125000000000 : ℝ) ≤ 4*Real.exp (4059/32768 : ℝ)*Real.exp (-mu (radius 8 (1015/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (256865176313/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1015/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0134_exp_radius
  have hrNumeric : (9846316463/10000000000 : ℝ) ≤ Real.exp (-1015/65536 : ℝ) ∧ Real.exp (-1015/65536 : ℝ) ≤ (984631646301/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (9846316463/10000000000 : ℝ) ≤ (radius 8 (1015/8192 : ℝ)) ∧ (radius 8 (1015/8192 : ℝ)) ≤ (984631646301/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1015/8192 : ℝ)) (9846316463/10000000000 : ℝ) (984631646301/1000000000000 : ℝ) (174643983871/1000000000000 : ℝ) (87321991939/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1015/8192 : ℝ)) (9846316463/10000000000 : ℝ) (984631646301/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1015/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (9846316463/10000000000 : ℝ) (984631646301/1000000000000 : ℝ) (19846316463/20000000000 : ℝ) (992315823151/1000000000000 : ℝ) (496143035399/500000000000 : ℝ) (992286070799/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1015/8192 : ℝ)) 1 (19846316463/20000000000 : ℝ) (992315823151/1000000000000 : ℝ) (496143035399/500000000000 : ℝ) (992286070799/1000000000000 : ℝ) (496150473487/500000000000 : ℝ) (39692037879/40000000000 : ℝ) (496150473431/500000000000 : ℝ) (62018809179/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1015/8192 : ℝ)) 2 (496150473487/500000000000 : ℝ) (39692037879/40000000000 : ℝ) (496150473431/500000000000 : ℝ) (62018809179/62500000000 : ℝ) (496150473459/500000000000 : ℝ) (24807523673/25000000000 : ℝ) (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1015/8192 : ℝ)) 3 (496150473459/500000000000 : ℝ) (24807523673/25000000000 : ℝ) (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ) (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ) (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1015/8192 : ℝ)) 4 (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ) (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ) (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ) (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1015/8192 : ℝ)) 5 (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ) (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ) (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ) (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1015/8192 : ℝ)) 6 (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ) (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ) (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ) (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1015/8192 : ℝ)) 7 (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ) (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ) (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ) (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1015/8192 : ℝ))) (174643983871/1000000000000 : ℝ) (87321991939/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1015/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174643983871/1000000000000 : ℝ) (87321991939/500000000000 : ℝ) (117464398387/200000000000 : ℝ) (587321991939/1000000000000 : ℝ) (208952137983/500000000000 : ℝ) (16716171039/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1015/8192 : ℝ))) 1 (117464398387/200000000000 : ℝ) (587321991939/1000000000000 : ℝ) (208952137983/500000000000 : ℝ) (16716171039/40000000000 : ℝ) (10052262679/20000000000 : ℝ) (502613133957/1000000000000 : ℝ) (61927928347/125000000000 : ℝ) (15481982087/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1015/8192 : ℝ))) 2 (10052262679/20000000000 : ℝ) (502613133957/1000000000000 : ℝ) (61927928347/125000000000 : ℝ) (15481982087/31250000000 : ℝ) (499018280363/1000000000000 : ℝ) (499018280371/1000000000000 : ℝ) (499005331799/1000000000000 : ℝ) (499005331807/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1015/8192 : ℝ))) 3 (499018280363/1000000000000 : ℝ) (499018280371/1000000000000 : ℝ) (499005331799/1000000000000 : ℝ) (499005331807/1000000000000 : ℝ) (499011806081/1000000000000 : ℝ) (499011806089/1000000000000 : ℝ) (499011806039/1000000000000 : ℝ) (15594118939/31250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1015/8192 : ℝ))) 4 (499011806081/1000000000000 : ℝ) (499011806089/1000000000000 : ℝ) (499011806039/1000000000000 : ℝ) (15594118939/31250000000 : ℝ) (24950590303/50000000000 : ℝ) (499011806069/1000000000000 : ℝ) (499011806059/1000000000000 : ℝ) (499011806069/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1015/8192 : ℝ))) 5 (24950590303/50000000000 : ℝ) (499011806069/1000000000000 : ℝ) (499011806059/1000000000000 : ℝ) (499011806069/1000000000000 : ℝ) (499011806059/1000000000000 : ℝ) (499011806069/1000000000000 : ℝ) (499011806059/1000000000000 : ℝ) (499011806069/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1015/8192 : ℝ))) 6 (499011806059/1000000000000 : ℝ) (499011806069/1000000000000 : ℝ) (499011806059/1000000000000 : ℝ) (499011806069/1000000000000 : ℝ) (499011806059/1000000000000 : ℝ) (499011806069/1000000000000 : ℝ) (499011806059/1000000000000 : ℝ) (499011806069/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1015/8192 : ℝ))) 7 (499011806059/1000000000000 : ℝ) (499011806069/1000000000000 : ℝ) (499011806059/1000000000000 : ℝ) (499011806069/1000000000000 : ℝ) (499011806059/1000000000000 : ℝ) (499011806069/1000000000000 : ℝ) (499011806059/1000000000000 : ℝ) (499011806069/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1015/8192 : ℝ)) hmem 8 (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ) (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1015/8192 : ℝ))) hcmem 8 (499011806059/1000000000000 : ℝ) (499011806069/1000000000000 : ℝ) (499011806059/1000000000000 : ℝ) (499011806069/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1015/8192 : ℝ)) (992300946917/1000000000000 : ℝ) (24807523673/25000000000 : ℝ) (499011806059/1000000000000 : ℝ) (499011806069/1000000000000 : ℝ) (789927606557/1000000000000 : ℝ) (49370475411/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0134_exp_lower
  have heNumeric : (256865176313/125000000000 : ℝ)/4 ≤ Real.exp (-5328454055733/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256865176313/125000000000 : ℝ)/4 ≤ Real.exp ((4059/32768 : ℝ)-(49370475411/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4059/32768 : ℝ) (1015/8192 : ℝ) (49370475411/62500000000 : ℝ) (256865176313/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0135; no trusted numerical premise.
theorem cover8_leaf0135_exp_radius : (998065437982529481/1000000000000000000 : ℝ) ≤ Real.exp ((-4061/262144 : ℝ)/8) ∧ Real.exp ((-4061/262144 : ℝ)/8) ≤ (499032718991264741/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4061/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0135_exp_lower : (230028622139035051/250000000000000000 : ℝ) ≤ Real.exp ((-1332114761581/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332114761581/2000000000000 : ℝ)/8) ≤ (184022897711228041/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332114761581/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0135_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410984025719/200000000000 : ℝ) ≤ 4*Real.exp (1015/8192 : ℝ)*Real.exp (-mu (radius 8 (4061/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (410984025719/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4061/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0135_exp_radius
  have hrNumeric : (196925578047/200000000000 : ℝ) ≤ Real.exp (-4061/262144 : ℝ) ∧ Real.exp (-4061/262144 : ℝ) ≤ (246156972559/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196925578047/200000000000 : ℝ) ≤ (radius 8 (4061/32768 : ℝ)) ∧ (radius 8 (4061/32768 : ℝ)) ≤ (246156972559/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4061/32768 : ℝ)) (196925578047/200000000000 : ℝ) (246156972559/250000000000 : ℝ) (87332579501/500000000000 : ℝ) (174665159009/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4061/32768 : ℝ)) (196925578047/200000000000 : ℝ) (246156972559/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4061/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196925578047/200000000000 : ℝ) (246156972559/250000000000 : ℝ) (992313945117/1000000000000 : ℝ) (496156972559/500000000000 : ℝ) (248071044541/250000000000 : ℝ) (198456835633/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4061/32768 : ℝ)) 1 (992313945117/1000000000000 : ℝ) (496156972559/500000000000 : ℝ) (248071044541/250000000000 : ℝ) (198456835633/200000000000 : ℝ) (24807476541/25000000000 : ℝ) (496149530821/500000000000 : ℝ) (124037382691/125000000000 : ℝ) (99229906153/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4061/32768 : ℝ)) 2 (24807476541/25000000000 : ℝ) (496149530821/500000000000 : ℝ) (124037382691/125000000000 : ℝ) (99229906153/100000000000 : ℝ) (62018691349/62500000000 : ℝ) (496149530793/500000000000 : ℝ) (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4061/32768 : ℝ)) 3 (62018691349/62500000000 : ℝ) (496149530793/500000000000 : ℝ) (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ) (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ) (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4061/32768 : ℝ)) 4 (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ) (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ) (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ) (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4061/32768 : ℝ)) 5 (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ) (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ) (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ) (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4061/32768 : ℝ)) 6 (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ) (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ) (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ) (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4061/32768 : ℝ)) 7 (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ) (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ) (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ) (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4061/32768 : ℝ))) (87332579501/500000000000 : ℝ) (174665159009/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4061/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87332579501/500000000000 : ℝ) (174665159009/1000000000000 : ℝ) (587332579501/1000000000000 : ℝ) (117466515901/200000000000 : ℝ) (52241201263/125000000000 : ℝ) (417929610113/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4061/32768 : ℝ))) 1 (587332579501/1000000000000 : ℝ) (117466515901/200000000000 : ℝ) (52241201263/125000000000 : ℝ) (417929610113/1000000000000 : ℝ) (251315547401/500000000000 : ℝ) (502631094809/1000000000000 : ℝ) (61930363609/125000000000 : ℝ) (6193036361/12500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4061/32768 : ℝ))) 2 (251315547401/500000000000 : ℝ) (502631094809/1000000000000 : ℝ) (61930363609/125000000000 : ℝ) (6193036361/12500000000 : ℝ) (499037001837/1000000000000 : ℝ) (99807400369/200000000000 : ℝ) (499024059237/1000000000000 : ℝ) (249512029623/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4061/32768 : ℝ))) 3 (499037001837/1000000000000 : ℝ) (99807400369/200000000000 : ℝ) (499024059237/1000000000000 : ℝ) (249512029623/500000000000 : ℝ) (499030530537/1000000000000 : ℝ) (249515265273/500000000000 : ℝ) (99806106099/200000000000 : ℝ) (62378816313/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4061/32768 : ℝ))) 4 (499030530537/1000000000000 : ℝ) (249515265273/500000000000 : ℝ) (99806106099/200000000000 : ℝ) (62378816313/125000000000 : ℝ) (124757632629/250000000000 : ℝ) (19961221221/40000000000 : ℝ) (99806106103/200000000000 : ℝ) (19961221221/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4061/32768 : ℝ))) 5 (124757632629/250000000000 : ℝ) (19961221221/40000000000 : ℝ) (99806106103/200000000000 : ℝ) (19961221221/40000000000 : ℝ) (99806106103/200000000000 : ℝ) (19961221221/40000000000 : ℝ) (99806106103/200000000000 : ℝ) (19961221221/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4061/32768 : ℝ))) 6 (99806106103/200000000000 : ℝ) (19961221221/40000000000 : ℝ) (99806106103/200000000000 : ℝ) (19961221221/40000000000 : ℝ) (99806106103/200000000000 : ℝ) (19961221221/40000000000 : ℝ) (99806106103/200000000000 : ℝ) (19961221221/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4061/32768 : ℝ))) 7 (99806106103/200000000000 : ℝ) (19961221221/40000000000 : ℝ) (99806106103/200000000000 : ℝ) (19961221221/40000000000 : ℝ) (99806106103/200000000000 : ℝ) (19961221221/40000000000 : ℝ) (99806106103/200000000000 : ℝ) (19961221221/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4061/32768 : ℝ)) hmem 8 (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ) (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4061/32768 : ℝ))) hcmem 8 (99806106103/200000000000 : ℝ) (19961221221/40000000000 : ℝ) (99806106103/200000000000 : ℝ) (19961221221/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4061/32768 : ℝ)) (992299061583/1000000000000 : ℝ) (496149530793/500000000000 : ℝ) (99806106103/200000000000 : ℝ) (19961221221/40000000000 : ℝ) (789958747959/1000000000000 : ℝ) (394979373989/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0135_exp_lower
  have heNumeric : (410984025719/200000000000 : ℝ)/4 ≤ Real.exp (-1332114761581/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410984025719/200000000000 : ℝ)/4 ≤ Real.exp ((1015/8192 : ℝ)-(394979373989/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1015/8192 : ℝ) (4061/32768 : ℝ) (394979373989/500000000000 : ℝ) (410984025719/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0136; no trusted numerical premise.
theorem cover8_leaf0136_exp_radius : (998064962067955799/1000000000000000000 : ℝ) ≤ Real.exp ((-2031/131072 : ℝ)/8) ∧ Real.exp ((-2031/131072 : ℝ)/8) ≤ (4990324810339779/5000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2031/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0136_exp_lower : (115014302175966179/125000000000000000 : ℝ) ≤ Real.exp ((-5328463995163/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328463995163/8000000000000 : ℝ)/8) ≤ (920114417407729433/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328463995163/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0136_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513729714353/250000000000 : ℝ) ≤ 4*Real.exp (4061/32768 : ℝ)*Real.exp (-mu (radius 8 (2031/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (513729714353/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2031/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0136_exp_radius
  have hrNumeric : (196924826837/200000000000 : ℝ) ≤ Real.exp (-2031/131072 : ℝ) ∧ Real.exp (-2031/131072 : ℝ) ≤ (492312067093/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196924826837/200000000000 : ℝ) ≤ (radius 8 (2031/16384 : ℝ)) ∧ (radius 8 (2031/16384 : ℝ)) ≤ (492312067093/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2031/16384 : ℝ)) (196924826837/200000000000 : ℝ) (492312067093/500000000000 : ℝ) (174686331401/1000000000000 : ℝ) (10917895713/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2031/16384 : ℝ)) (196924826837/200000000000 : ℝ) (492312067093/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2031/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196924826837/200000000000 : ℝ) (492312067093/500000000000 : ℝ) (248078016773/250000000000 : ℝ) (992312067093/1000000000000 : ℝ) (496141142767/500000000000 : ℝ) (198456457107/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2031/16384 : ℝ)) 1 (248078016773/250000000000 : ℝ) (992312067093/1000000000000 : ℝ) (496141142767/500000000000 : ℝ) (198456457107/200000000000 : ℝ) (992297176313/1000000000000 : ℝ) (496148588157/500000000000 : ℝ) (992297176201/1000000000000 : ℝ) (992297176203/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2031/16384 : ℝ)) 2 (992297176313/1000000000000 : ℝ) (496148588157/500000000000 : ℝ) (992297176201/1000000000000 : ℝ) (992297176203/1000000000000 : ℝ) (992297176257/1000000000000 : ℝ) (992297176259/1000000000000 : ℝ) (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2031/16384 : ℝ)) 3 (992297176257/1000000000000 : ℝ) (992297176259/1000000000000 : ℝ) (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ) (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ) (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2031/16384 : ℝ)) 4 (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ) (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ) (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ) (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2031/16384 : ℝ)) 5 (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ) (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ) (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ) (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2031/16384 : ℝ)) 6 (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ) (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ) (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ) (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2031/16384 : ℝ)) 7 (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ) (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ) (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ) (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2031/16384 : ℝ))) (174686331401/1000000000000 : ℝ) (10917895713/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2031/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174686331401/1000000000000 : ℝ) (10917895713/62500000000 : ℝ) (5873431657/10000000000 : ℝ) (73417895713/125000000000 : ℝ) (208977469719/500000000000 : ℝ) (417954939447/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2031/16384 : ℝ))) 1 (5873431657/10000000000 : ℝ) (73417895713/125000000000 : ℝ) (208977469719/500000000000 : ℝ) (417954939447/1000000000000 : ℝ) (502649052569/1000000000000 : ℝ) (15707782893/31250000000 : ℝ) (12386559683/25000000000 : ℝ) (3870799901/7812500000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2031/16384 : ℝ))) 2 (502649052569/1000000000000 : ℝ) (15707782893/31250000000 : ℝ) (12386559683/25000000000 : ℝ) (3870799901/7812500000 : ℝ) (62381964993/125000000000 : ℝ) (31190982497/62500000000 : ℝ) (249521391653/500000000000 : ℝ) (249521391657/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2031/16384 : ℝ))) 3 (62381964993/125000000000 : ℝ) (31190982497/62500000000 : ℝ) (249521391653/500000000000 : ℝ) (249521391657/500000000000 : ℝ) (3992394013/8000000000 : ℝ) (499049251633/1000000000000 : ℝ) (499049251583/1000000000000 : ℝ) (62381156449/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2031/16384 : ℝ))) 4 (3992394013/8000000000 : ℝ) (499049251633/1000000000000 : ℝ) (499049251583/1000000000000 : ℝ) (62381156449/125000000000 : ℝ) (124762312901/250000000000 : ℝ) (499049251613/1000000000000 : ℝ) (499049251603/1000000000000 : ℝ) (499049251613/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2031/16384 : ℝ))) 5 (124762312901/250000000000 : ℝ) (499049251613/1000000000000 : ℝ) (499049251603/1000000000000 : ℝ) (499049251613/1000000000000 : ℝ) (499049251603/1000000000000 : ℝ) (499049251613/1000000000000 : ℝ) (499049251603/1000000000000 : ℝ) (499049251613/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2031/16384 : ℝ))) 6 (499049251603/1000000000000 : ℝ) (499049251613/1000000000000 : ℝ) (499049251603/1000000000000 : ℝ) (499049251613/1000000000000 : ℝ) (499049251603/1000000000000 : ℝ) (499049251613/1000000000000 : ℝ) (499049251603/1000000000000 : ℝ) (499049251613/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2031/16384 : ℝ))) 7 (499049251603/1000000000000 : ℝ) (499049251613/1000000000000 : ℝ) (499049251603/1000000000000 : ℝ) (499049251613/1000000000000 : ℝ) (499049251603/1000000000000 : ℝ) (499049251613/1000000000000 : ℝ) (499049251603/1000000000000 : ℝ) (499049251613/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2031/16384 : ℝ)) hmem 8 (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ) (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2031/16384 : ℝ))) hcmem 8 (499049251603/1000000000000 : ℝ) (499049251613/1000000000000 : ℝ) (499049251603/1000000000000 : ℝ) (499049251613/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2031/16384 : ℝ)) (15504643379/15625000000 : ℝ) (992297176259/1000000000000 : ℝ) (499049251603/1000000000000 : ℝ) (499049251613/1000000000000 : ℝ) (394994942071/500000000000 : ℝ) (789989884161/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0136_exp_lower
  have heNumeric : (513729714353/250000000000 : ℝ)/4 ≤ Real.exp (-5328463995163/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513729714353/250000000000 : ℝ)/4 ≤ Real.exp ((4061/32768 : ℝ)-(789989884161/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4061/32768 : ℝ) (2031/16384 : ℝ) (789989884161/1000000000000 : ℝ) (513729714353/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0137; no trusted numerical premise.
theorem cover8_leaf0137_exp_radius : (249516121538402263/250000000000000000 : ℝ) ≤ Real.exp ((-4063/262144 : ℝ)/8) ∧ Real.exp ((-4063/262144 : ℝ)/8) ≤ (998064486153609053/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4063/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0137_exp_lower : (920114346858088573/1000000000000000000 : ℝ) ≤ Real.exp ((-2664234451177/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664234451177/4000000000000 : ℝ)/8) ≤ (460057173429044287/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664234451177/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0137_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054917596927/1000000000000 : ℝ) ≤ 4*Real.exp (2031/16384 : ℝ)*Real.exp (-mu (radius 8 (4063/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054917596927/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4063/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0137_exp_radius
  have hrNumeric : (984620378149/1000000000000 : ℝ) ≤ Real.exp (-4063/262144 : ℝ) ∧ Real.exp (-4063/262144 : ℝ) ≤ (19692407563/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984620378149/1000000000000 : ℝ) ≤ (radius 8 (4063/32768 : ℝ)) ∧ (radius 8 (4063/32768 : ℝ)) ≤ (19692407563/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4063/32768 : ℝ)) (984620378149/1000000000000 : ℝ) (19692407563/20000000000 : ℝ) (87353750537/500000000000 : ℝ) (174707501081/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4063/32768 : ℝ)) (984620378149/1000000000000 : ℝ) (19692407563/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4063/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984620378149/1000000000000 : ℝ) (19692407563/20000000000 : ℝ) (496155094537/500000000000 : ℝ) (39692407563/40000000000 : ℝ) (992280392907/1000000000000 : ℝ) (992280392909/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4063/32768 : ℝ)) 1 (496155094537/500000000000 : ℝ) (39692407563/40000000000 : ℝ) (992280392907/1000000000000 : ℝ) (992280392909/1000000000000 : ℝ) (99229529099/100000000000 : ℝ) (62018455687/62500000000 : ℝ) (496147645439/500000000000 : ℝ) (992295290881/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4063/32768 : ℝ)) 2 (99229529099/100000000000 : ℝ) (62018455687/62500000000 : ℝ) (496147645439/500000000000 : ℝ) (992295290881/1000000000000 : ℝ) (496147645467/500000000000 : ℝ) (992295290937/1000000000000 : ℝ) (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4063/32768 : ℝ)) 3 (496147645467/500000000000 : ℝ) (992295290937/1000000000000 : ℝ) (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ) (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ) (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4063/32768 : ℝ)) 4 (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ) (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ) (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ) (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4063/32768 : ℝ)) 5 (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ) (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ) (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ) (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4063/32768 : ℝ)) 6 (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ) (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ) (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ) (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4063/32768 : ℝ)) 7 (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ) (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ) (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ) (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4063/32768 : ℝ))) (87353750537/500000000000 : ℝ) (174707501081/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4063/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87353750537/500000000000 : ℝ) (174707501081/1000000000000 : ℝ) (587353750537/1000000000000 : ℝ) (587353750541/1000000000000 : ℝ) (52247532997/125000000000 : ℝ) (208990131993/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4063/32768 : ℝ))) 1 (587353750537/1000000000000 : ℝ) (587353750541/1000000000000 : ℝ) (52247532997/125000000000 : ℝ) (208990131993/500000000000 : ℝ) (62833375907/125000000000 : ℝ) (15708343977/31250000000 : ℝ) (247740931063/500000000000 : ℝ) (99096372427/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4063/32768 : ℝ))) 2 (62833375907/125000000000 : ℝ) (15708343977/31250000000 : ℝ) (247740931063/500000000000 : ℝ) (99096372427/200000000000 : ℝ) (499074434691/1000000000000 : ℝ) (4990744347/10000000000 : ℝ) (499061504009/1000000000000 : ℝ) (499061504019/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4063/32768 : ℝ))) 3 (499074434691/1000000000000 : ℝ) (4990744347/10000000000 : ℝ) (499061504009/1000000000000 : ℝ) (499061504019/1000000000000 : ℝ) (9981359387/20000000000 : ℝ) (6238349617/12500000000 : ℝ) (124766992327/250000000000 : ℝ) (249533984659/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4063/32768 : ℝ))) 4 (9981359387/20000000000 : ℝ) (6238349617/12500000000 : ℝ) (124766992327/250000000000 : ℝ) (249533984659/500000000000 : ℝ) (499067969329/1000000000000 : ℝ) (499067969339/1000000000000 : ℝ) (31191748083/62500000000 : ℝ) (499067969339/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4063/32768 : ℝ))) 5 (499067969329/1000000000000 : ℝ) (499067969339/1000000000000 : ℝ) (31191748083/62500000000 : ℝ) (499067969339/1000000000000 : ℝ) (31191748083/62500000000 : ℝ) (499067969339/1000000000000 : ℝ) (31191748083/62500000000 : ℝ) (499067969339/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4063/32768 : ℝ))) 6 (31191748083/62500000000 : ℝ) (499067969339/1000000000000 : ℝ) (31191748083/62500000000 : ℝ) (499067969339/1000000000000 : ℝ) (31191748083/62500000000 : ℝ) (499067969339/1000000000000 : ℝ) (31191748083/62500000000 : ℝ) (499067969339/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4063/32768 : ℝ))) 7 (31191748083/62500000000 : ℝ) (499067969339/1000000000000 : ℝ) (31191748083/62500000000 : ℝ) (499067969339/1000000000000 : ℝ) (31191748083/62500000000 : ℝ) (499067969339/1000000000000 : ℝ) (31191748083/62500000000 : ℝ) (499067969339/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4063/32768 : ℝ)) hmem 8 (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ) (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4063/32768 : ℝ))) hcmem 8 (31191748083/62500000000 : ℝ) (499067969339/1000000000000 : ℝ) (31191748083/62500000000 : ℝ) (499067969339/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4063/32768 : ℝ)) (992295290933/1000000000000 : ℝ) (992295290937/1000000000000 : ℝ) (31191748083/62500000000 : ℝ) (499067969339/1000000000000 : ℝ) (197505253779/250000000000 : ℝ) (395010507569/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0137_exp_lower
  have heNumeric : (2054917596927/1000000000000 : ℝ)/4 ≤ Real.exp (-2664234451177/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054917596927/1000000000000 : ℝ)/4 ≤ Real.exp ((2031/16384 : ℝ)-(395010507569/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2031/16384 : ℝ) (4063/32768 : ℝ) (395010507569/500000000000 : ℝ) (2054917596927/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0138; no trusted numerical premise.
theorem cover8_leaf0138_exp_radius : (998064010239489237/1000000000000000000 : ℝ) ≤ Real.exp ((-127/8192 : ℝ)/8) ∧ Real.exp ((-127/8192 : ℝ)/8) ≤ (499032005119744619/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-127/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0138_exp_lower : (46005713845429883/50000000000000000 : ℝ) ≤ Real.exp ((-5328473767801/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328473767801/8000000000000 : ℝ)/8) ≤ (920114276908597661/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328473767801/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0138_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027458173583/500000000000 : ℝ) ≤ 4*Real.exp (4063/32768 : ℝ)*Real.exp (-mu (radius 8 (127/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (1027458173583/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (127/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0138_exp_radius
  have hrNumeric : (61538538883/62500000000 : ℝ) ≤ Real.exp (-127/8192 : ℝ) ∧ Real.exp (-127/8192 : ℝ) ≤ (984616622129/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61538538883/62500000000 : ℝ) ≤ (radius 8 (127/1024 : ℝ)) ∧ (radius 8 (127/1024 : ℝ)) ≤ (984616622129/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (127/1024 : ℝ)) (61538538883/62500000000 : ℝ) (984616622129/1000000000000 : ℝ) (174728668017/1000000000000 : ℝ) (21841083503/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (127/1024 : ℝ)) (61538538883/62500000000 : ℝ) (984616622129/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (127/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61538538883/62500000000 : ℝ) (984616622129/1000000000000 : ℝ) (124038538883/125000000000 : ℝ) (198461662213/200000000000 : ℝ) (198455700057/200000000000 : ℝ) (496139250143/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (127/1024 : ℝ)) 1 (124038538883/125000000000 : ℝ) (198461662213/200000000000 : ℝ) (198455700057/200000000000 : ℝ) (496139250143/500000000000 : ℝ) (496146702837/500000000000 : ℝ) (248073351419/250000000000 : ℝ) (496146702781/500000000000 : ℝ) (248073351391/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (127/1024 : ℝ)) 2 (496146702837/500000000000 : ℝ) (248073351419/250000000000 : ℝ) (496146702781/500000000000 : ℝ) (248073351391/250000000000 : ℝ) (496146702809/500000000000 : ℝ) (49614670281/50000000000 : ℝ) (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (127/1024 : ℝ)) 3 (496146702809/500000000000 : ℝ) (49614670281/50000000000 : ℝ) (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ) (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ) (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (127/1024 : ℝ)) 4 (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ) (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ) (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ) (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (127/1024 : ℝ)) 5 (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ) (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ) (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ) (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (127/1024 : ℝ)) 6 (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ) (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ) (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ) (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (127/1024 : ℝ)) 7 (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ) (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ) (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ) (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (127/1024 : ℝ))) (174728668017/1000000000000 : ℝ) (21841083503/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (127/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174728668017/1000000000000 : ℝ) (21841083503/125000000000 : ℝ) (73420541751/125000000000 : ℝ) (146841083503/250000000000 : ℝ) (83601116743/200000000000 : ℝ) (104501395931/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (127/1024 : ℝ))) 1 (73420541751/125000000000 : ℝ) (146841083503/250000000000 : ℝ) (83601116743/200000000000 : ℝ) (104501395931/250000000000 : ℝ) (502684958861/1000000000000 : ℝ) (125671239717/250000000000 : ℝ) (61937666661/125000000000 : ℝ) (30968833331/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (127/1024 : ℝ))) 2 (502684958861/1000000000000 : ℝ) (125671239717/250000000000 : ℝ) (61937666661/125000000000 : ℝ) (30968833331/62500000000 : ℝ) (249546573037/500000000000 : ℝ) (249546573041/500000000000 : ℝ) (249540110673/500000000000 : ℝ) (99816044271/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (127/1024 : ℝ))) 3 (249546573037/500000000000 : ℝ) (249546573041/500000000000 : ℝ) (249540110673/500000000000 : ℝ) (99816044271/200000000000 : ℝ) (49908668371/100000000000 : ℝ) (499086683719/1000000000000 : ℝ) (124771670917/250000000000 : ℝ) (499086683677/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (127/1024 : ℝ))) 4 (49908668371/100000000000 : ℝ) (499086683719/1000000000000 : ℝ) (124771670917/250000000000 : ℝ) (499086683677/1000000000000 : ℝ) (499086683689/1000000000000 : ℝ) (249543341849/500000000000 : ℝ) (62385835461/125000000000 : ℝ) (249543341849/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (127/1024 : ℝ))) 5 (499086683689/1000000000000 : ℝ) (249543341849/500000000000 : ℝ) (62385835461/125000000000 : ℝ) (249543341849/500000000000 : ℝ) (62385835461/125000000000 : ℝ) (249543341849/500000000000 : ℝ) (62385835461/125000000000 : ℝ) (249543341849/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (127/1024 : ℝ))) 6 (62385835461/125000000000 : ℝ) (249543341849/500000000000 : ℝ) (62385835461/125000000000 : ℝ) (249543341849/500000000000 : ℝ) (62385835461/125000000000 : ℝ) (249543341849/500000000000 : ℝ) (62385835461/125000000000 : ℝ) (249543341849/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (127/1024 : ℝ))) 7 (62385835461/125000000000 : ℝ) (249543341849/500000000000 : ℝ) (62385835461/125000000000 : ℝ) (249543341849/500000000000 : ℝ) (62385835461/125000000000 : ℝ) (249543341849/500000000000 : ℝ) (62385835461/125000000000 : ℝ) (249543341849/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (127/1024 : ℝ)) hmem 8 (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ) (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (127/1024 : ℝ))) hcmem 8 (62385835461/125000000000 : ℝ) (249543341849/500000000000 : ℝ) (62385835461/125000000000 : ℝ) (249543341849/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (127/1024 : ℝ)) (992293405617/1000000000000 : ℝ) (49614670281/50000000000 : ℝ) (62385835461/125000000000 : ℝ) (249543341849/500000000000 : ℝ) (395026070439/500000000000 : ℝ) (790052140897/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0138_exp_lower
  have heNumeric : (1027458173583/500000000000 : ℝ)/4 ≤ Real.exp (-5328473767801/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027458173583/500000000000 : ℝ)/4 ≤ Real.exp ((4063/32768 : ℝ)-(790052140897/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4063/32768 : ℝ) (127/1024 : ℝ) (790052140897/1000000000000 : ℝ) (1027458173583/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0139; no trusted numerical premise.
theorem cover8_leaf0139_exp_radius : (998063534325596357/1000000000000000000 : ℝ) ≤ Real.exp ((-4065/262144 : ℝ)/8) ∧ Real.exp ((-4065/262144 : ℝ)/8) ≤ (499031767162798179/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4065/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0139_exp_lower : (184022841511460263/200000000000000000 : ℝ) ≤ Real.exp ((-133211964791/200000000000 : ℝ)/8) ∧ Real.exp ((-133211964791/200000000000 : ℝ)/8) ≤ (230028551889325329/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-133211964791/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0139_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054915108093/1000000000000 : ℝ) ≤ 4*Real.exp (127/1024 : ℝ)*Real.exp (-mu (radius 8 (4065/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054915108093/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4065/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0139_exp_radius
  have hrNumeric : (984612866121/1000000000000 : ℝ) ≤ Real.exp (-4065/262144 : ℝ) ∧ Real.exp (-4065/262144 : ℝ) ≤ (492306433061/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984612866121/1000000000000 : ℝ) ≤ (radius 8 (4065/32768 : ℝ)) ∧ (radius 8 (4065/32768 : ℝ)) ≤ (492306433061/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4065/32768 : ℝ)) (984612866121/1000000000000 : ℝ) (492306433061/500000000000 : ℝ) (174749832237/1000000000000 : ℝ) (43687458061/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4065/32768 : ℝ)) (984612866121/1000000000000 : ℝ) (492306433061/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4065/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984612866121/1000000000000 : ℝ) (492306433061/500000000000 : ℝ) (49615321653/50000000000 : ℝ) (992306433061/1000000000000 : ℝ) (198455321533/200000000000 : ℝ) (992276607667/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4065/32768 : ℝ)) 1 (49615321653/50000000000 : ℝ) (992306433061/1000000000000 : ℝ) (198455321533/200000000000 : ℝ) (992276607667/1000000000000 : ℝ) (496145760181/500000000000 : ℝ) (248072880091/250000000000 : ℝ) (3969166081/4000000000 : ℝ) (248072880063/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4065/32768 : ℝ)) 2 (496145760181/500000000000 : ℝ) (248072880091/250000000000 : ℝ) (3969166081/4000000000 : ℝ) (248072880063/250000000000 : ℝ) (496145760153/500000000000 : ℝ) (248072880077/250000000000 : ℝ) (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4065/32768 : ℝ)) 3 (496145760153/500000000000 : ℝ) (248072880077/250000000000 : ℝ) (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ) (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ) (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4065/32768 : ℝ)) 4 (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ) (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ) (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ) (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4065/32768 : ℝ)) 5 (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ) (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ) (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ) (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4065/32768 : ℝ)) 6 (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ) (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ) (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ) (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4065/32768 : ℝ)) 7 (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ) (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ) (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ) (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4065/32768 : ℝ))) (174749832237/1000000000000 : ℝ) (43687458061/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4065/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174749832237/1000000000000 : ℝ) (43687458061/250000000000 : ℝ) (293687458059/500000000000 : ℝ) (293687458061/500000000000 : ℝ) (418030898663/1000000000000 : ℝ) (26126931167/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4065/32768 : ℝ))) 1 (293687458059/500000000000 : ℝ) (293687458061/500000000000 : ℝ) (418030898663/1000000000000 : ℝ) (26126931167/62500000000 : ℝ) (50270290739/100000000000 : ℝ) (502702907397/1000000000000 : ℝ) (495520800811/1000000000000 : ℝ) (495520800819/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4065/32768 : ℝ))) 2 (50270290739/100000000000 : ℝ) (502702907397/1000000000000 : ℝ) (495520800811/1000000000000 : ℝ) (495520800819/1000000000000 : ℝ) (4991118541/10000000000 : ℝ) (124777963527/250000000000 : ℝ) (249549467661/500000000000 : ℝ) (49909893533/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4065/32768 : ℝ))) 3 (4991118541/10000000000 : ℝ) (124777963527/250000000000 : ℝ) (249549467661/500000000000 : ℝ) (49909893533/100000000000 : ℝ) (499105394711/1000000000000 : ℝ) (499105394719/1000000000000 : ℝ) (499105394669/1000000000000 : ℝ) (249552697339/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4065/32768 : ℝ))) 4 (499105394711/1000000000000 : ℝ) (499105394719/1000000000000 : ℝ) (499105394669/1000000000000 : ℝ) (249552697339/500000000000 : ℝ) (49910539469/100000000000 : ℝ) (499105394699/1000000000000 : ℝ) (499105394689/1000000000000 : ℝ) (499105394699/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4065/32768 : ℝ))) 5 (49910539469/100000000000 : ℝ) (499105394699/1000000000000 : ℝ) (499105394689/1000000000000 : ℝ) (499105394699/1000000000000 : ℝ) (499105394689/1000000000000 : ℝ) (499105394699/1000000000000 : ℝ) (499105394689/1000000000000 : ℝ) (499105394699/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4065/32768 : ℝ))) 6 (499105394689/1000000000000 : ℝ) (499105394699/1000000000000 : ℝ) (499105394689/1000000000000 : ℝ) (499105394699/1000000000000 : ℝ) (499105394689/1000000000000 : ℝ) (499105394699/1000000000000 : ℝ) (499105394689/1000000000000 : ℝ) (499105394699/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4065/32768 : ℝ))) 7 (499105394689/1000000000000 : ℝ) (499105394699/1000000000000 : ℝ) (499105394689/1000000000000 : ℝ) (499105394699/1000000000000 : ℝ) (499105394689/1000000000000 : ℝ) (499105394699/1000000000000 : ℝ) (499105394689/1000000000000 : ℝ) (499105394699/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4065/32768 : ℝ)) hmem 8 (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ) (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4065/32768 : ℝ))) hcmem 8 (499105394689/1000000000000 : ℝ) (499105394699/1000000000000 : ℝ) (499105394689/1000000000000 : ℝ) (499105394699/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4065/32768 : ℝ)) (198458304061/200000000000 : ℝ) (248072880077/250000000000 : ℝ) (499105394689/1000000000000 : ℝ) (499105394699/1000000000000 : ℝ) (197520815359/250000000000 : ℝ) (158016652291/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0139_exp_lower
  have heNumeric : (2054915108093/1000000000000 : ℝ)/4 ≤ Real.exp (-133211964791/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054915108093/1000000000000 : ℝ)/4 ≤ Real.exp ((127/1024 : ℝ)-(158016652291/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (127/1024 : ℝ) (4065/32768 : ℝ) (158016652291/200000000000 : ℝ) (2054915108093/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0140; no trusted numerical premise.
theorem cover8_leaf0140_exp_radius : (998063058411930409/1000000000000000000 : ℝ) ≤ Real.exp ((-2033/131072 : ℝ)/8) ∧ Real.exp ((-2033/131072 : ℝ)/8) ≤ (99806305841193041/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2033/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0140_exp_lower : (460057069402157207/500000000000000000 : ℝ) ≤ Real.exp ((-5328483373863/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328483373863/8000000000000 : ℝ)/8) ≤ (184022827760862883/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328483373863/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0140_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054913879711/1000000000000 : ℝ) ≤ 4*Real.exp (4065/32768 : ℝ)*Real.exp (-mu (radius 8 (2033/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054913879711/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2033/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0140_exp_radius
  have hrNumeric : (61538069383/62500000000 : ℝ) ≤ Real.exp (-2033/131072 : ℝ) ∧ Real.exp (-2033/131072 : ℝ) ≤ (984609110129/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61538069383/62500000000 : ℝ) ≤ (radius 8 (2033/16384 : ℝ)) ∧ (radius 8 (2033/16384 : ℝ)) ≤ (984609110129/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2033/16384 : ℝ)) (61538069383/62500000000 : ℝ) (984609110129/1000000000000 : ℝ) (87385496867/500000000000 : ℝ) (174770993741/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2033/16384 : ℝ)) (61538069383/62500000000 : ℝ) (984609110129/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2033/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61538069383/62500000000 : ℝ) (984609110129/1000000000000 : ℝ) (124038069383/125000000000 : ℝ) (198460911013/200000000000 : ℝ) (19845494301/20000000000 : ℝ) (992274715051/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2033/16384 : ℝ)) 1 (124038069383/125000000000 : ℝ) (198460911013/200000000000 : ℝ) (19845494301/20000000000 : ℝ) (992274715051/1000000000000 : ℝ) (992289635057/1000000000000 : ℝ) (496144817529/500000000000 : ℝ) (7752262773/7812500000 : ℝ) (496144817473/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2033/16384 : ℝ)) 2 (992289635057/1000000000000 : ℝ) (496144817529/500000000000 : ℝ) (7752262773/7812500000 : ℝ) (496144817473/500000000000 : ℝ) (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ) (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2033/16384 : ℝ)) 3 (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ) (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ) (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ) (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2033/16384 : ℝ)) 4 (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ) (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ) (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ) (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2033/16384 : ℝ)) 5 (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ) (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ) (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ) (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2033/16384 : ℝ)) 6 (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ) (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ) (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ) (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2033/16384 : ℝ)) 7 (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ) (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ) (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ) (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2033/16384 : ℝ))) (87385496867/500000000000 : ℝ) (174770993741/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2033/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87385496867/500000000000 : ℝ) (174770993741/1000000000000 : ℝ) (587385496867/1000000000000 : ℝ) (587385496871/1000000000000 : ℝ) (418056208821/1000000000000 : ℝ) (41805620883/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2033/16384 : ℝ))) 1 (587385496867/1000000000000 : ℝ) (587385496871/1000000000000 : ℝ) (418056208821/1000000000000 : ℝ) (41805620883/100000000000 : ℝ) (125680213211/250000000000 : ℝ) (502720852851/1000000000000 : ℝ) (495540264697/1000000000000 : ℝ) (99108052941/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2033/16384 : ℝ))) 2 (125680213211/250000000000 : ℝ) (502720852851/1000000000000 : ℝ) (495540264697/1000000000000 : ℝ) (99108052941/200000000000 : ℝ) (49913055877/100000000000 : ℝ) (249565279389/500000000000 : ℝ) (249558822969/500000000000 : ℝ) (249558822973/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2033/16384 : ℝ))) 3 (49913055877/100000000000 : ℝ) (249565279389/500000000000 : ℝ) (249558822969/500000000000 : ℝ) (249558822973/500000000000 : ℝ) (249562051177/500000000000 : ℝ) (249562051181/500000000000 : ℝ) (62390512789/125000000000 : ℝ) (499124102321/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2033/16384 : ℝ))) 4 (249562051177/500000000000 : ℝ) (249562051181/500000000000 : ℝ) (62390512789/125000000000 : ℝ) (499124102321/1000000000000 : ℝ) (499124102333/1000000000000 : ℝ) (249562051171/500000000000 : ℝ) (124781025583/250000000000 : ℝ) (249562051171/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2033/16384 : ℝ))) 5 (499124102333/1000000000000 : ℝ) (249562051171/500000000000 : ℝ) (124781025583/250000000000 : ℝ) (249562051171/500000000000 : ℝ) (124781025583/250000000000 : ℝ) (249562051171/500000000000 : ℝ) (124781025583/250000000000 : ℝ) (249562051171/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2033/16384 : ℝ))) 6 (124781025583/250000000000 : ℝ) (249562051171/500000000000 : ℝ) (124781025583/250000000000 : ℝ) (249562051171/500000000000 : ℝ) (124781025583/250000000000 : ℝ) (249562051171/500000000000 : ℝ) (124781025583/250000000000 : ℝ) (249562051171/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2033/16384 : ℝ))) 7 (124781025583/250000000000 : ℝ) (249562051171/500000000000 : ℝ) (124781025583/250000000000 : ℝ) (249562051171/500000000000 : ℝ) (124781025583/250000000000 : ℝ) (249562051171/500000000000 : ℝ) (124781025583/250000000000 : ℝ) (249562051171/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2033/16384 : ℝ)) hmem 8 (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ) (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2033/16384 : ℝ))) hcmem 8 (124781025583/250000000000 : ℝ) (249562051171/500000000000 : ℝ) (124781025583/250000000000 : ℝ) (249562051171/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2033/16384 : ℝ)) (198457927/200000000 : ℝ) (496144817501/500000000000 : ℝ) (124781025583/250000000000 : ℝ) (249562051171/500000000000 : ℝ) (790114376793/1000000000000 : ℝ) (790114376811/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0140_exp_lower
  have heNumeric : (2054913879711/1000000000000 : ℝ)/4 ≤ Real.exp (-5328483373863/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054913879711/1000000000000 : ℝ)/4 ≤ Real.exp ((4065/32768 : ℝ)-(790114376811/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4065/32768 : ℝ) (2033/16384 : ℝ) (790114376811/1000000000000 : ℝ) (2054913879711/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0141; no trusted numerical premise.
theorem cover8_leaf0141_exp_radius : (199612516499698279/200000000000000000 : ℝ) ≤ Real.exp ((-4067/262144 : ℝ)/8) ∧ Real.exp ((-4067/262144 : ℝ)/8) ≤ (249515645624622849/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4067/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0141_exp_lower : (920114070649291783/1000000000000000000 : ℝ) ≤ Real.exp ((-2664244057247/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664244057247/4000000000000 : ℝ)/8) ≤ (115014258831161473/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664244057247/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0141_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054912662013/1000000000000 : ℝ) ≤ 4*Real.exp (2033/16384 : ℝ)*Real.exp (-mu (radius 8 (4067/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054912662013/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4067/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0141_exp_radius
  have hrNumeric : (984605354149/1000000000000 : ℝ) ≤ Real.exp (-4067/262144 : ℝ) ∧ Real.exp (-4067/262144 : ℝ) ≤ (19692107083/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984605354149/1000000000000 : ℝ) ≤ (radius 8 (4067/32768 : ℝ)) ∧ (radius 8 (4067/32768 : ℝ)) ≤ (19692107083/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4067/32768 : ℝ)) (984605354149/1000000000000 : ℝ) (19692107083/20000000000 : ℝ) (17479215251/100000000000 : ℝ) (43698038129/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4067/32768 : ℝ)) (984605354149/1000000000000 : ℝ) (19692107083/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4067/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984605354149/1000000000000 : ℝ) (19692107083/20000000000 : ℝ) (496151338537/500000000000 : ℝ) (39692107083/40000000000 : ℝ) (992272822437/1000000000000 : ℝ) (992272822439/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4067/32768 : ℝ)) 1 (496151338537/500000000000 : ℝ) (39692107083/40000000000 : ℝ) (992272822437/1000000000000 : ℝ) (992272822439/1000000000000 : ℝ) (198457549951/200000000000 : ℝ) (992287749757/1000000000000 : ℝ) (992287749643/1000000000000 : ℝ) (198457549929/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4067/32768 : ℝ)) 2 (198457549951/200000000000 : ℝ) (992287749757/1000000000000 : ℝ) (992287749643/1000000000000 : ℝ) (198457549929/200000000000 : ℝ) (992287749699/1000000000000 : ℝ) (992287749701/1000000000000 : ℝ) (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4067/32768 : ℝ)) 3 (992287749699/1000000000000 : ℝ) (992287749701/1000000000000 : ℝ) (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ) (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ) (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4067/32768 : ℝ)) 4 (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ) (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ) (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ) (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4067/32768 : ℝ)) 5 (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ) (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ) (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ) (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4067/32768 : ℝ)) 6 (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ) (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ) (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ) (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4067/32768 : ℝ)) 7 (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ) (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ) (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ) (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4067/32768 : ℝ))) (17479215251/100000000000 : ℝ) (43698038129/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4067/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17479215251/100000000000 : ℝ) (43698038129/250000000000 : ℝ) (117479215251/200000000000 : ℝ) (293698038129/500000000000 : ℝ) (418081514193/1000000000000 : ℝ) (418081514201/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4067/32768 : ℝ))) 1 (117479215251/200000000000 : ℝ) (293698038129/500000000000 : ℝ) (418081514193/1000000000000 : ℝ) (418081514201/1000000000000 : ℝ) (62842349403/125000000000 : ℝ) (50273879523/100000000000 : ℝ) (495559724949/1000000000000 : ℝ) (123889931239/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4067/32768 : ℝ))) 2 (62842349403/125000000000 : ℝ) (50273879523/100000000000 : ℝ) (495559724949/1000000000000 : ℝ) (123889931239/250000000000 : ℝ) (249574630043/500000000000 : ℝ) (499149260093/1000000000000 : ℝ) (124784088299/250000000000 : ℝ) (124784088301/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4067/32768 : ℝ))) 3 (249574630043/500000000000 : ℝ) (499149260093/1000000000000 : ℝ) (124784088299/250000000000 : ℝ) (124784088301/250000000000 : ℝ) (499142806641/1000000000000 : ℝ) (499142806649/1000000000000 : ℝ) (499142806599/1000000000000 : ℝ) (499142806607/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4067/32768 : ℝ))) 4 (499142806641/1000000000000 : ℝ) (499142806649/1000000000000 : ℝ) (499142806599/1000000000000 : ℝ) (499142806607/1000000000000 : ℝ) (24957140331/50000000000 : ℝ) (124785701657/250000000000 : ℝ) (499142806619/1000000000000 : ℝ) (124785701657/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4067/32768 : ℝ))) 5 (24957140331/50000000000 : ℝ) (124785701657/250000000000 : ℝ) (499142806619/1000000000000 : ℝ) (124785701657/250000000000 : ℝ) (499142806619/1000000000000 : ℝ) (124785701657/250000000000 : ℝ) (499142806619/1000000000000 : ℝ) (124785701657/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4067/32768 : ℝ))) 6 (499142806619/1000000000000 : ℝ) (124785701657/250000000000 : ℝ) (499142806619/1000000000000 : ℝ) (124785701657/250000000000 : ℝ) (499142806619/1000000000000 : ℝ) (124785701657/250000000000 : ℝ) (499142806619/1000000000000 : ℝ) (124785701657/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4067/32768 : ℝ))) 7 (499142806619/1000000000000 : ℝ) (124785701657/250000000000 : ℝ) (499142806619/1000000000000 : ℝ) (124785701657/250000000000 : ℝ) (499142806619/1000000000000 : ℝ) (124785701657/250000000000 : ℝ) (499142806619/1000000000000 : ℝ) (124785701657/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4067/32768 : ℝ)) hmem 8 (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ) (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4067/32768 : ℝ))) hcmem 8 (499142806619/1000000000000 : ℝ) (124785701657/250000000000 : ℝ) (499142806619/1000000000000 : ℝ) (124785701657/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4067/32768 : ℝ)) (496143874849/500000000000 : ℝ) (992287749701/1000000000000 : ℝ) (499142806619/1000000000000 : ℝ) (124785701657/250000000000 : ℝ) (790145486951/1000000000000 : ℝ) (98768185871/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0141_exp_lower
  have heNumeric : (2054912662013/1000000000000 : ℝ)/4 ≤ Real.exp (-2664244057247/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054912662013/1000000000000 : ℝ)/4 ≤ Real.exp ((2033/16384 : ℝ)-(98768185871/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2033/16384 : ℝ) (4067/32768 : ℝ) (98768185871/125000000000 : ℝ) (2054912662013/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0142; no trusted numerical premise.
theorem cover8_leaf0142_exp_radius : (499031053292639657/500000000000000000 : ℝ) ≤ Real.exp ((-1017/65536 : ℝ)/8) ∧ Real.exp ((-1017/65536 : ℝ)/8) ≤ (199612421317055863/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1017/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0142_exp_lower : (920114003093038387/1000000000000000000 : ℝ) ≤ Real.exp ((-5328492813477/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328492813477/8000000000000 : ℝ)/8) ≤ (230028500773259597/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328492813477/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0142_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054911455013/1000000000000 : ℝ) ≤ 4*Real.exp (4067/32768 : ℝ)*Real.exp (-mu (radius 8 (1017/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2054911455013/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1017/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0142_exp_radius
  have hrNumeric : (196920319637/200000000000 : ℝ) ≤ Real.exp (-1017/65536 : ℝ) ∧ Real.exp (-1017/65536 : ℝ) ≤ (492300799093/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196920319637/200000000000 : ℝ) ≤ (radius 8 (1017/8192 : ℝ)) ∧ (radius 8 (1017/8192 : ℝ)) ≤ (492300799093/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1017/8192 : ℝ)) (196920319637/200000000000 : ℝ) (492300799093/500000000000 : ℝ) (174813308559/1000000000000 : ℝ) (87406654283/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1017/8192 : ℝ)) (196920319637/200000000000 : ℝ) (492300799093/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1017/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196920319637/200000000000 : ℝ) (492300799093/500000000000 : ℝ) (248075199773/250000000000 : ℝ) (992300799093/1000000000000 : ℝ) (992270929829/1000000000000 : ℝ) (992270929831/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1017/8192 : ℝ)) 1 (248075199773/250000000000 : ℝ) (992300799093/1000000000000 : ℝ) (992270929829/1000000000000 : ℝ) (992270929831/1000000000000 : ℝ) (49614293223/50000000000 : ℝ) (496142932231/500000000000 : ℝ) (248071466087/250000000000 : ℝ) (19845717287/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1017/8192 : ℝ)) 2 (49614293223/50000000000 : ℝ) (496142932231/500000000000 : ℝ) (248071466087/250000000000 : ℝ) (19845717287/20000000000 : ℝ) (248071466101/250000000000 : ℝ) (496142932203/500000000000 : ℝ) (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1017/8192 : ℝ)) 3 (248071466101/250000000000 : ℝ) (496142932203/500000000000 : ℝ) (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ) (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ) (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1017/8192 : ℝ)) 4 (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ) (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ) (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ) (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1017/8192 : ℝ)) 5 (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ) (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ) (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ) (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1017/8192 : ℝ)) 6 (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ) (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ) (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ) (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1017/8192 : ℝ)) 7 (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ) (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ) (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ) (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1017/8192 : ℝ))) (174813308559/1000000000000 : ℝ) (87406654283/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1017/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174813308559/1000000000000 : ℝ) (87406654283/500000000000 : ℝ) (587406654279/1000000000000 : ℝ) (587406654283/1000000000000 : ℝ) (104526703693/250000000000 : ℝ) (418106814781/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1017/8192 : ℝ))) 1 (587406654279/1000000000000 : ℝ) (587406654283/1000000000000 : ℝ) (104526703693/250000000000 : ℝ) (418106814781/1000000000000 : ℝ) (20110269381/40000000000 : ℝ) (125689183633/250000000000 : ℝ) (12389479539/25000000000 : ℝ) (967928089/1953125000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1017/8192 : ℝ))) 2 (20110269381/40000000000 : ℝ) (125689183633/250000000000 : ℝ) (12389479539/25000000000 : ℝ) (967928089/1953125000 : ℝ) (249583979021/500000000000 : ℝ) (9983359161/20000000000 : ℝ) (499155057091/1000000000000 : ℝ) (499155057099/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1017/8192 : ℝ))) 3 (249583979021/500000000000 : ℝ) (9983359161/20000000000 : ℝ) (499155057091/1000000000000 : ℝ) (499155057099/1000000000000 : ℝ) (249580753783/500000000000 : ℝ) (19966460303/40000000000 : ℝ) (124790376881/250000000000 : ℝ) (499161507533/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1017/8192 : ℝ))) 4 (249580753783/500000000000 : ℝ) (19966460303/40000000000 : ℝ) (124790376881/250000000000 : ℝ) (499161507533/1000000000000 : ℝ) (99832301509/200000000000 : ℝ) (249580753777/500000000000 : ℝ) (62395188443/125000000000 : ℝ) (249580753777/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1017/8192 : ℝ))) 5 (99832301509/200000000000 : ℝ) (249580753777/500000000000 : ℝ) (62395188443/125000000000 : ℝ) (249580753777/500000000000 : ℝ) (62395188443/125000000000 : ℝ) (249580753777/500000000000 : ℝ) (62395188443/125000000000 : ℝ) (249580753777/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1017/8192 : ℝ))) 6 (62395188443/125000000000 : ℝ) (249580753777/500000000000 : ℝ) (62395188443/125000000000 : ℝ) (249580753777/500000000000 : ℝ) (62395188443/125000000000 : ℝ) (249580753777/500000000000 : ℝ) (62395188443/125000000000 : ℝ) (249580753777/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1017/8192 : ℝ))) 7 (62395188443/125000000000 : ℝ) (249580753777/500000000000 : ℝ) (62395188443/125000000000 : ℝ) (249580753777/500000000000 : ℝ) (62395188443/125000000000 : ℝ) (249580753777/500000000000 : ℝ) (62395188443/125000000000 : ℝ) (249580753777/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1017/8192 : ℝ)) hmem 8 (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ) (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1017/8192 : ℝ))) hcmem 8 (62395188443/125000000000 : ℝ) (249580753777/500000000000 : ℝ) (62395188443/125000000000 : ℝ) (249580753777/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1017/8192 : ℝ)) (992285864403/1000000000000 : ℝ) (496142932203/500000000000 : ℝ) (62395188443/125000000000 : ℝ) (249580753777/500000000000 : ℝ) (7901765919/10000000000 : ℝ) (790176591919/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0142_exp_lower
  have heNumeric : (2054911455013/1000000000000 : ℝ)/4 ≤ Real.exp (-5328492813477/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054911455013/1000000000000 : ℝ)/4 ≤ Real.exp ((4067/32768 : ℝ)-(790176591919/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4067/32768 : ℝ) (1017/8192 : ℝ) (790176591919/1000000000000 : ℝ) (2054911455013/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0143; no trusted numerical premise.
theorem cover8_leaf0143_exp_radius : (998061630672294167/1000000000000000000 : ℝ) ≤ Real.exp ((-4069/262144 : ℝ)/8) ∧ Real.exp ((-4069/262144 : ℝ)/8) ≤ (124757703834036771/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4069/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0143_exp_lower : (115014242016742987/125000000000000000 : ℝ) ≤ Real.exp ((-1332124367731/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332124367731/2000000000000 : ℝ)/8) ≤ (920113936133943897/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332124367731/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0143_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054910258683/1000000000000 : ℝ) ≤ 4*Real.exp (1017/8192 : ℝ)*Real.exp (-mu (radius 8 (4069/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054910258683/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4069/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0143_exp_radius
  have hrNumeric : (196919568447/200000000000 : ℝ) ≤ Real.exp (-4069/262144 : ℝ) ∧ Real.exp (-4069/262144 : ℝ) ≤ (246149460559/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196919568447/200000000000 : ℝ) ≤ (radius 8 (4069/32768 : ℝ)) ∧ (radius 8 (4069/32768 : ℝ)) ≤ (246149460559/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4069/32768 : ℝ)) (196919568447/200000000000 : ℝ) (246149460559/250000000000 : ℝ) (174834461889/1000000000000 : ℝ) (21854307737/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4069/32768 : ℝ)) (196919568447/200000000000 : ℝ) (246149460559/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4069/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196919568447/200000000000 : ℝ) (246149460559/250000000000 : ℝ) (992298921117/1000000000000 : ℝ) (496149460559/500000000000 : ℝ) (124033629653/125000000000 : ℝ) (496134518613/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4069/32768 : ℝ)) 1 (992298921117/1000000000000 : ℝ) (496149460559/500000000000 : ℝ) (124033629653/125000000000 : ℝ) (496134518613/500000000000 : ℝ) (99228397917/100000000000 : ℝ) (248070994793/250000000000 : ℝ) (496141989529/500000000000 : ℝ) (49614198953/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4069/32768 : ℝ)) 2 (99228397917/100000000000 : ℝ) (248070994793/250000000000 : ℝ) (496141989529/500000000000 : ℝ) (49614198953/50000000000 : ℝ) (496141989557/500000000000 : ℝ) (248070994779/250000000000 : ℝ) (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4069/32768 : ℝ)) 3 (496141989557/500000000000 : ℝ) (248070994779/250000000000 : ℝ) (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ) (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ) (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4069/32768 : ℝ)) 4 (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ) (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ) (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ) (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4069/32768 : ℝ)) 5 (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ) (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ) (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ) (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4069/32768 : ℝ)) 6 (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ) (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ) (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ) (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4069/32768 : ℝ)) 7 (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ) (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ) (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ) (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4069/32768 : ℝ))) (174834461889/1000000000000 : ℝ) (21854307737/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4069/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174834461889/1000000000000 : ℝ) (21854307737/125000000000 : ℝ) (18356788467/31250000000 : ℝ) (146854307737/250000000000 : ℝ) (418132110569/1000000000000 : ℝ) (209066055289/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4069/32768 : ℝ))) 1 (18356788467/31250000000 : ℝ) (146854307737/250000000000 : ℝ) (418132110569/1000000000000 : ℝ) (209066055289/500000000000 : ℝ) (125693667689/250000000000 : ℝ) (502774670763/1000000000000 : ℝ) (495598634541/1000000000000 : ℝ) (495598634549/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4069/32768 : ℝ))) 2 (125693667689/250000000000 : ℝ) (502774670763/1000000000000 : ℝ) (495598634541/1000000000000 : ℝ) (495598634549/1000000000000 : ℝ) (62398331581/125000000000 : ℝ) (31199165791/62500000000 : ℝ) (7799589963/15625000000 : ℝ) (12479343941/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4069/32768 : ℝ))) 3 (62398331581/125000000000 : ℝ) (31199165791/62500000000 : ℝ) (7799589963/15625000000 : ℝ) (12479343941/25000000000 : ℝ) (24959010257/50000000000 : ℝ) (124795051287/250000000000 : ℝ) (249590102549/500000000000 : ℝ) (499180205107/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4069/32768 : ℝ))) 4 (24959010257/50000000000 : ℝ) (124795051287/250000000000 : ℝ) (249590102549/500000000000 : ℝ) (499180205107/1000000000000 : ℝ) (499180205119/1000000000000 : ℝ) (62397525641/125000000000 : ℝ) (249590102559/500000000000 : ℝ) (62397525641/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4069/32768 : ℝ))) 5 (499180205119/1000000000000 : ℝ) (62397525641/125000000000 : ℝ) (249590102559/500000000000 : ℝ) (62397525641/125000000000 : ℝ) (249590102559/500000000000 : ℝ) (62397525641/125000000000 : ℝ) (249590102559/500000000000 : ℝ) (62397525641/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4069/32768 : ℝ))) 6 (249590102559/500000000000 : ℝ) (62397525641/125000000000 : ℝ) (249590102559/500000000000 : ℝ) (62397525641/125000000000 : ℝ) (249590102559/500000000000 : ℝ) (62397525641/125000000000 : ℝ) (249590102559/500000000000 : ℝ) (62397525641/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4069/32768 : ℝ))) 7 (249590102559/500000000000 : ℝ) (62397525641/125000000000 : ℝ) (249590102559/500000000000 : ℝ) (62397525641/125000000000 : ℝ) (249590102559/500000000000 : ℝ) (62397525641/125000000000 : ℝ) (249590102559/500000000000 : ℝ) (62397525641/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4069/32768 : ℝ)) hmem 8 (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ) (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4069/32768 : ℝ))) hcmem 8 (249590102559/500000000000 : ℝ) (62397525641/125000000000 : ℝ) (249590102559/500000000000 : ℝ) (62397525641/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4069/32768 : ℝ)) (992283979113/1000000000000 : ℝ) (248070994779/250000000000 : ℝ) (249590102559/500000000000 : ℝ) (62397525641/125000000000 : ℝ) (790207691659/1000000000000 : ℝ) (395103845839/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0143_exp_lower
  have heNumeric : (2054910258683/1000000000000 : ℝ)/4 ≤ Real.exp (-1332124367731/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054910258683/1000000000000 : ℝ)/4 ≤ Real.exp ((1017/8192 : ℝ)-(395103845839/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1017/8192 : ℝ) (4069/32768 : ℝ) (395103845839/500000000000 : ℝ) (2054910258683/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0144; no trusted numerical premise.
theorem cover8_leaf0144_exp_radius : (62378822172470997/62500000000000000 : ℝ) ≤ Real.exp ((-2035/131072 : ℝ)/8) ∧ Real.exp ((-2035/131072 : ℝ)/8) ≤ (998061154759535953/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2035/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0144_exp_lower : (18402277395467767/20000000000000000 : ℝ) ≤ Real.exp ((-5328502086739/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328502086739/8000000000000 : ℝ)/8) ≤ (920113869773388351/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328502086739/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0144_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256863634131/125000000000 : ℝ) ≤ 4*Real.exp (4069/32768 : ℝ)*Real.exp (-mu (radius 8 (2035/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (256863634131/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2035/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0144_exp_radius
  have hrNumeric : (9845940863/10000000000 : ℝ) ≤ Real.exp (-2035/131072 : ℝ) ∧ Real.exp (-2035/131072 : ℝ) ≤ (984594086301/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (9845940863/10000000000 : ℝ) ≤ (radius 8 (2035/16384 : ℝ)) ∧ (radius 8 (2035/16384 : ℝ)) ≤ (984594086301/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2035/16384 : ℝ)) (9845940863/10000000000 : ℝ) (984594086301/1000000000000 : ℝ) (34971122499/200000000000 : ℝ) (174855612501/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2035/16384 : ℝ)) (9845940863/10000000000 : ℝ) (984594086301/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2035/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (9845940863/10000000000 : ℝ) (984594086301/1000000000000 : ℝ) (19845940863/20000000000 : ℝ) (992297043151/1000000000000 : ℝ) (992267144623/1000000000000 : ℝ) (7938137157/8000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2035/16384 : ℝ)) 1 (19845940863/20000000000 : ℝ) (992297043151/1000000000000 : ℝ) (992267144623/1000000000000 : ℝ) (7938137157/8000000000 : ℝ) (496141046943/500000000000 : ℝ) (15504407717/15625000000 : ℝ) (992282093773/1000000000000 : ℝ) (62017630861/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2035/16384 : ℝ)) 2 (496141046943/500000000000 : ℝ) (15504407717/15625000000 : ℝ) (992282093773/1000000000000 : ℝ) (62017630861/62500000000 : ℝ) (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ) (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2035/16384 : ℝ)) 3 (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ) (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ) (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ) (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2035/16384 : ℝ)) 4 (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ) (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ) (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ) (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2035/16384 : ℝ)) 5 (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ) (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ) (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ) (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2035/16384 : ℝ)) 6 (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ) (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ) (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ) (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2035/16384 : ℝ)) 7 (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ) (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ) (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ) (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2035/16384 : ℝ))) (34971122499/200000000000 : ℝ) (174855612501/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2035/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (34971122499/200000000000 : ℝ) (174855612501/1000000000000 : ℝ) (587427806247/1000000000000 : ℝ) (587427806251/1000000000000 : ℝ) (209078700789/500000000000 : ℝ) (209078700793/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2035/16384 : ℝ))) 1 (587427806247/1000000000000 : ℝ) (587427806251/1000000000000 : ℝ) (209078700789/500000000000 : ℝ) (209078700793/500000000000 : ℝ) (62849075489/125000000000 : ℝ) (502792603919/1000000000000 : ℝ) (247809041943/500000000000 : ℝ) (495618083893/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2035/16384 : ℝ))) 2 (62849075489/125000000000 : ℝ) (502792603919/1000000000000 : ℝ) (247809041943/500000000000 : ℝ) (495618083893/1000000000000 : ℝ) (499205343899/1000000000000 : ℝ) (249602671953/500000000000 : ℝ) (499192454813/1000000000000 : ℝ) (499192454821/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2035/16384 : ℝ))) 3 (499205343899/1000000000000 : ℝ) (249602671953/500000000000 : ℝ) (499192454813/1000000000000 : ℝ) (499192454821/1000000000000 : ℝ) (124799724839/250000000000 : ℝ) (124799724841/250000000000 : ℝ) (249599449657/500000000000 : ℝ) (249599449661/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2035/16384 : ℝ))) 4 (124799724839/250000000000 : ℝ) (124799724841/250000000000 : ℝ) (249599449657/500000000000 : ℝ) (249599449661/500000000000 : ℝ) (99839779867/200000000000 : ℝ) (499198899343/1000000000000 : ℝ) (249599449667/500000000000 : ℝ) (499198899343/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2035/16384 : ℝ))) 5 (99839779867/200000000000 : ℝ) (499198899343/1000000000000 : ℝ) (249599449667/500000000000 : ℝ) (499198899343/1000000000000 : ℝ) (249599449667/500000000000 : ℝ) (499198899343/1000000000000 : ℝ) (249599449667/500000000000 : ℝ) (499198899343/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2035/16384 : ℝ))) 6 (249599449667/500000000000 : ℝ) (499198899343/1000000000000 : ℝ) (249599449667/500000000000 : ℝ) (499198899343/1000000000000 : ℝ) (249599449667/500000000000 : ℝ) (499198899343/1000000000000 : ℝ) (249599449667/500000000000 : ℝ) (499198899343/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2035/16384 : ℝ))) 7 (249599449667/500000000000 : ℝ) (499198899343/1000000000000 : ℝ) (249599449667/500000000000 : ℝ) (499198899343/1000000000000 : ℝ) (249599449667/500000000000 : ℝ) (499198899343/1000000000000 : ℝ) (249599449667/500000000000 : ℝ) (499198899343/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2035/16384 : ℝ)) hmem 8 (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ) (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2035/16384 : ℝ))) hcmem 8 (249599449667/500000000000 : ℝ) (499198899343/1000000000000 : ℝ) (249599449667/500000000000 : ℝ) (499198899343/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2035/16384 : ℝ)) (992282093829/1000000000000 : ℝ) (124035261729/125000000000 : ℝ) (249599449667/500000000000 : ℝ) (499198899343/1000000000000 : ℝ) (98779848277/125000000000 : ℝ) (790238786233/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0144_exp_lower
  have heNumeric : (256863634131/125000000000 : ℝ)/4 ≤ Real.exp (-5328502086739/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256863634131/125000000000 : ℝ)/4 ≤ Real.exp ((4069/32768 : ℝ)-(790238786233/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4069/32768 : ℝ) (2035/16384 : ℝ) (790238786233/1000000000000 : ℝ) (256863634131/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0145; no trusted numerical premise.
theorem cover8_leaf0145_exp_radius : (99806067884700467/100000000000000000 : ℝ) ≤ Real.exp ((-4071/262144 : ℝ)/8) ∧ Real.exp ((-4071/262144 : ℝ)/8) ≤ (998060678847004671/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4071/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0145_exp_lower : (920113804009186349/1000000000000000000 : ℝ) ≤ Real.exp ((-2664253330537/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664253330537/4000000000000 : ℝ)/8) ≤ (18402276080183727/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664253330537/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0145_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726974517/250000000000 : ℝ) ≤ 4*Real.exp (2035/16384 : ℝ)*Real.exp (-mu (radius 8 (4071/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513726974517/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4071/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0145_exp_radius
  have hrNumeric : (984590330379/1000000000000 : ℝ) ≤ Real.exp (-4071/262144 : ℝ) ∧ Real.exp (-4071/262144 : ℝ) ≤ (49229516519/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984590330379/1000000000000 : ℝ) ≤ (radius 8 (4071/32768 : ℝ)) ∧ (radius 8 (4071/32768 : ℝ)) ≤ (49229516519/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4071/32768 : ℝ)) (984590330379/1000000000000 : ℝ) (49229516519/50000000000 : ℝ) (174876760383/1000000000000 : ℝ) (17487676039/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4071/32768 : ℝ)) (984590330379/1000000000000 : ℝ) (49229516519/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4071/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984590330379/1000000000000 : ℝ) (49229516519/50000000000 : ℝ) (992295165189/1000000000000 : ℝ) (99229516519/100000000000 : ℝ) (496132626013/500000000000 : ℝ) (992265252027/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4071/32768 : ℝ)) 1 (992295165189/1000000000000 : ℝ) (99229516519/100000000000 : ℝ) (496132626013/500000000000 : ℝ) (992265252027/1000000000000 : ℝ) (992280208607/1000000000000 : ℝ) (992280208609/1000000000000 : ℝ) (496140104247/500000000000 : ℝ) (62017513031/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4071/32768 : ℝ)) 2 (992280208607/1000000000000 : ℝ) (992280208609/1000000000000 : ℝ) (496140104247/500000000000 : ℝ) (62017513031/62500000000 : ℝ) (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ) (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4071/32768 : ℝ)) 3 (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ) (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ) (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ) (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4071/32768 : ℝ)) 4 (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ) (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ) (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ) (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4071/32768 : ℝ)) 5 (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ) (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ) (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ) (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4071/32768 : ℝ)) 6 (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ) (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ) (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ) (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4071/32768 : ℝ)) 7 (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ) (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ) (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ) (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4071/32768 : ℝ))) (174876760383/1000000000000 : ℝ) (17487676039/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4071/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (174876760383/1000000000000 : ℝ) (17487676039/100000000000 : ℝ) (587438380191/1000000000000 : ℝ) (117487676039/200000000000 : ℝ) (6534104497/15625000000 : ℝ) (209091343909/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4071/32768 : ℝ))) 1 (587438380191/1000000000000 : ℝ) (117487676039/200000000000 : ℝ) (6534104497/15625000000 : ℝ) (209091343909/500000000000 : ℝ) (502810533999/1000000000000 : ℝ) (502810534007/1000000000000 : ℝ) (495637529601/1000000000000 : ℝ) (49563752961/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4071/32768 : ℝ))) 2 (502810533999/1000000000000 : ℝ) (502810534007/1000000000000 : ℝ) (495637529601/1000000000000 : ℝ) (49563752961/100000000000 : ℝ) (2496120159/5000000000 : ℝ) (499224031809/1000000000000 : ℝ) (249605574321/500000000000 : ℝ) (499211148651/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4071/32768 : ℝ))) 3 (2496120159/5000000000 : ℝ) (499224031809/1000000000000 : ℝ) (249605574321/500000000000 : ℝ) (499211148651/1000000000000 : ℝ) (499217590221/1000000000000 : ℝ) (49921759023/100000000000 : ℝ) (499217590179/1000000000000 : ℝ) (499217590189/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4071/32768 : ℝ))) 4 (499217590221/1000000000000 : ℝ) (49921759023/100000000000 : ℝ) (499217590179/1000000000000 : ℝ) (499217590189/1000000000000 : ℝ) (2496087951/5000000000 : ℝ) (49921759021/100000000000 : ℝ) (499217590199/1000000000000 : ℝ) (49921759021/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4071/32768 : ℝ))) 5 (2496087951/5000000000 : ℝ) (49921759021/100000000000 : ℝ) (499217590199/1000000000000 : ℝ) (49921759021/100000000000 : ℝ) (499217590199/1000000000000 : ℝ) (49921759021/100000000000 : ℝ) (499217590199/1000000000000 : ℝ) (49921759021/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4071/32768 : ℝ))) 6 (499217590199/1000000000000 : ℝ) (49921759021/100000000000 : ℝ) (499217590199/1000000000000 : ℝ) (49921759021/100000000000 : ℝ) (499217590199/1000000000000 : ℝ) (49921759021/100000000000 : ℝ) (499217590199/1000000000000 : ℝ) (49921759021/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4071/32768 : ℝ))) 7 (499217590199/1000000000000 : ℝ) (49921759021/100000000000 : ℝ) (499217590199/1000000000000 : ℝ) (49921759021/100000000000 : ℝ) (499217590199/1000000000000 : ℝ) (49921759021/100000000000 : ℝ) (499217590199/1000000000000 : ℝ) (49921759021/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4071/32768 : ℝ)) hmem 8 (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ) (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4071/32768 : ℝ))) hcmem 8 (499217590199/1000000000000 : ℝ) (49921759021/100000000000 : ℝ) (499217590199/1000000000000 : ℝ) (49921759021/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4071/32768 : ℝ)) (19845604171/20000000000 : ℝ) (992280208553/1000000000000 : ℝ) (499217590199/1000000000000 : ℝ) (49921759021/100000000000 : ℝ) (395134937791/500000000000 : ℝ) (790269875603/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0145_exp_lower
  have heNumeric : (513726974517/250000000000 : ℝ)/4 ≤ Real.exp (-2664253330537/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726974517/250000000000 : ℝ)/4 ≤ Real.exp ((2035/16384 : ℝ)-(790269875603/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2035/16384 : ℝ) (4071/32768 : ℝ) (790269875603/1000000000000 : ℝ) (513726974517/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0146; no trusted numerical premise.
theorem cover8_leaf0146_exp_radius : (6237876268341877/6250000000000000 : ℝ) ≤ Real.exp ((-509/32768 : ℝ)/8) ∧ Real.exp ((-509/32768 : ℝ)/8) ≤ (998060202934700321/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-509/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0146_exp_lower : (57507108677633929/62500000000000000 : ℝ) ≤ Real.exp ((-5328511193873/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328511193873/8000000000000 : ℝ)/8) ≤ (184022747768428573/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328511193873/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0146_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453366879/500000000000 : ℝ) ≤ 4*Real.exp (4071/32768 : ℝ)*Real.exp (-mu (radius 8 (509/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453366879/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (509/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0146_exp_radius
  have hrNumeric : (123073321809/125000000000 : ℝ) ≤ Real.exp (-509/32768 : ℝ) ∧ Real.exp (-509/32768 : ℝ) ≤ (984586574473/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123073321809/125000000000 : ℝ) ≤ (radius 8 (509/4096 : ℝ)) ∧ (radius 8 (509/4096 : ℝ)) ≤ (984586574473/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (509/4096 : ℝ)) (123073321809/125000000000 : ℝ) (984586574473/1000000000000 : ℝ) (87448952777/500000000000 : ℝ) (174897905561/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (509/4096 : ℝ)) (123073321809/125000000000 : ℝ) (984586574473/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (509/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123073321809/125000000000 : ℝ) (984586574473/1000000000000 : ℝ) (248073321809/250000000000 : ℝ) (992293287237/1000000000000 : ℝ) (124032919929/125000000000 : ℝ) (992263359433/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (509/4096 : ℝ)) 1 (248073321809/250000000000 : ℝ) (992293287237/1000000000000 : ℝ) (124032919929/125000000000 : ℝ) (992263359433/1000000000000 : ℝ) (496139161667/500000000000 : ℝ) (198455664667/200000000000 : ℝ) (992278323221/1000000000000 : ℝ) (992278323223/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (509/4096 : ℝ)) 2 (496139161667/500000000000 : ℝ) (198455664667/200000000000 : ℝ) (992278323221/1000000000000 : ℝ) (992278323223/1000000000000 : ℝ) (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ) (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (509/4096 : ℝ)) 3 (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ) (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ) (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ) (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (509/4096 : ℝ)) 4 (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ) (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ) (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ) (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (509/4096 : ℝ)) 5 (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ) (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ) (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ) (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (509/4096 : ℝ)) 6 (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ) (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ) (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ) (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (509/4096 : ℝ)) 7 (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ) (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ) (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ) (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (509/4096 : ℝ))) (87448952777/500000000000 : ℝ) (174897905561/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (509/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87448952777/500000000000 : ℝ) (174897905561/1000000000000 : ℝ) (587448952777/1000000000000 : ℝ) (587448952781/1000000000000 : ℝ) (418207969261/1000000000000 : ℝ) (418207969271/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (509/4096 : ℝ))) 1 (587448952777/1000000000000 : ℝ) (587448952781/1000000000000 : ℝ) (418207969261/1000000000000 : ℝ) (418207969271/1000000000000 : ℝ) (502828461019/1000000000000 : ℝ) (251414230513/500000000000 : ℝ) (49565697169/100000000000 : ℝ) (495656971699/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (509/4096 : ℝ))) 2 (502828461019/1000000000000 : ℝ) (251414230513/500000000000 : ℝ) (49565697169/100000000000 : ℝ) (495656971699/1000000000000 : ℝ) (249621358177/500000000000 : ℝ) (499242716363/1000000000000 : ℝ) (6240372989/12500000000 : ℝ) (499229839129/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (509/4096 : ℝ))) 3 (249621358177/500000000000 : ℝ) (499242716363/1000000000000 : ℝ) (6240372989/12500000000 : ℝ) (499229839129/1000000000000 : ℝ) (499236277737/1000000000000 : ℝ) (249618138873/500000000000 : ℝ) (99847255539/200000000000 : ℝ) (99847255541/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (509/4096 : ℝ))) 4 (499236277737/1000000000000 : ℝ) (249618138873/500000000000 : ℝ) (99847255539/200000000000 : ℝ) (99847255541/200000000000 : ℝ) (124809069429/250000000000 : ℝ) (249618138863/500000000000 : ℝ) (99847255543/200000000000 : ℝ) (249618138863/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (509/4096 : ℝ))) 5 (124809069429/250000000000 : ℝ) (249618138863/500000000000 : ℝ) (99847255543/200000000000 : ℝ) (249618138863/500000000000 : ℝ) (99847255543/200000000000 : ℝ) (249618138863/500000000000 : ℝ) (99847255543/200000000000 : ℝ) (249618138863/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (509/4096 : ℝ))) 6 (99847255543/200000000000 : ℝ) (249618138863/500000000000 : ℝ) (99847255543/200000000000 : ℝ) (249618138863/500000000000 : ℝ) (99847255543/200000000000 : ℝ) (249618138863/500000000000 : ℝ) (99847255543/200000000000 : ℝ) (249618138863/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (509/4096 : ℝ))) 7 (99847255543/200000000000 : ℝ) (249618138863/500000000000 : ℝ) (99847255543/200000000000 : ℝ) (249618138863/500000000000 : ℝ) (99847255543/200000000000 : ℝ) (249618138863/500000000000 : ℝ) (99847255543/200000000000 : ℝ) (249618138863/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (509/4096 : ℝ)) hmem 8 (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ) (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (509/4096 : ℝ))) hcmem 8 (99847255543/200000000000 : ℝ) (249618138863/500000000000 : ℝ) (99847255543/200000000000 : ℝ) (249618138863/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (509/4096 : ℝ)) (992278323277/1000000000000 : ℝ) (992278323279/1000000000000 : ℝ) (99847255543/200000000000 : ℝ) (249618138863/500000000000 : ℝ) (790300959761/1000000000000 : ℝ) (790300959781/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0146_exp_lower
  have heNumeric : (1027453366879/500000000000 : ℝ)/4 ≤ Real.exp (-5328511193873/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453366879/500000000000 : ℝ)/4 ≤ Real.exp ((4071/32768 : ℝ)-(790300959781/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4071/32768 : ℝ) (509/4096 : ℝ) (790300959781/1000000000000 : ℝ) (1027453366879/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0147; no trusted numerical premise.
theorem cover8_leaf0147_exp_radius : (124757465877827863/125000000000000000 : ℝ) ≤ Real.exp ((-4073/262144 : ℝ)/8) ∧ Real.exp ((-4073/262144 : ℝ)/8) ≤ (199611945404524581/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4073/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0147_exp_lower : (230028418567891921/250000000000000000 : ℝ) ≤ Real.exp ((-83258057581/125000000000 : ℝ)/8) ∧ Real.exp ((-83258057581/125000000000 : ℝ)/8) ≤ (184022734854313537/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-83258057581/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0147_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410981116021/200000000000 : ℝ) ≤ 4*Real.exp (509/4096 : ℝ)*Real.exp (-mu (radius 8 (4073/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (410981116021/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4073/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0147_exp_radius
  have hrNumeric : (984582818579/1000000000000 : ℝ) ≤ Real.exp (-4073/262144 : ℝ) ∧ Real.exp (-4073/262144 : ℝ) ≤ (49229140929/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984582818579/1000000000000 : ℝ) ≤ (radius 8 (4073/32768 : ℝ)) ∧ (radius 8 (4073/32768 : ℝ)) ≤ (49229140929/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4073/32768 : ℝ)) (984582818579/1000000000000 : ℝ) (49229140929/50000000000 : ℝ) (17491904801/100000000000 : ℝ) (174919048017/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4073/32768 : ℝ)) (984582818579/1000000000000 : ℝ) (49229140929/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4073/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984582818579/1000000000000 : ℝ) (49229140929/50000000000 : ℝ) (992291409289/1000000000000 : ℝ) (99229140929/100000000000 : ℝ) (992261466841/1000000000000 : ℝ) (992261466843/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4073/32768 : ℝ)) 1 (992291409289/1000000000000 : ℝ) (99229140929/100000000000 : ℝ) (992261466841/1000000000000 : ℝ) (992261466843/1000000000000 : ℝ) (198455287613/200000000000 : ℝ) (992276438067/1000000000000 : ℝ) (15504319343/15625000000 : ℝ) (496138218977/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4073/32768 : ℝ)) 2 (198455287613/200000000000 : ℝ) (992276438067/1000000000000 : ℝ) (15504319343/15625000000 : ℝ) (496138218977/500000000000 : ℝ) (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ) (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4073/32768 : ℝ)) 3 (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ) (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ) (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ) (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4073/32768 : ℝ)) 4 (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ) (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ) (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ) (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4073/32768 : ℝ)) 5 (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ) (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ) (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ) (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4073/32768 : ℝ)) 6 (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ) (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ) (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ) (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4073/32768 : ℝ)) 7 (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ) (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ) (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ) (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4073/32768 : ℝ))) (17491904801/100000000000 : ℝ) (174919048017/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4073/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17491904801/100000000000 : ℝ) (174919048017/1000000000000 : ℝ) (117491904801/200000000000 : ℝ) (587459524009/1000000000000 : ℝ) (20911662297/50000000000 : ℝ) (418233245949/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4073/32768 : ℝ))) 1 (117491904801/200000000000 : ℝ) (587459524009/1000000000000 : ℝ) (20911662297/50000000000 : ℝ) (418233245949/1000000000000 : ℝ) (125711596243/250000000000 : ℝ) (502846384979/1000000000000 : ℝ) (495676410153/1000000000000 : ℝ) (495676410161/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4073/32768 : ℝ))) 2 (125711596243/250000000000 : ℝ) (502846384979/1000000000000 : ℝ) (495676410153/1000000000000 : ℝ) (495676410161/1000000000000 : ℝ) (249630698781/500000000000 : ℝ) (49926139757/100000000000 : ℝ) (62406065781/125000000000 : ℝ) (499248526257/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4073/32768 : ℝ))) 3 (249630698781/500000000000 : ℝ) (49926139757/100000000000 : ℝ) (62406065781/125000000000 : ℝ) (499248526257/1000000000000 : ℝ) (99850992381/200000000000 : ℝ) (249627480957/500000000000 : ℝ) (499254961863/1000000000000 : ℝ) (499254961873/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4073/32768 : ℝ))) 4 (99850992381/200000000000 : ℝ) (249627480957/500000000000 : ℝ) (499254961863/1000000000000 : ℝ) (499254961873/1000000000000 : ℝ) (124813740471/250000000000 : ℝ) (249627480947/500000000000 : ℝ) (499254961883/1000000000000 : ℝ) (249627480947/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4073/32768 : ℝ))) 5 (124813740471/250000000000 : ℝ) (249627480947/500000000000 : ℝ) (499254961883/1000000000000 : ℝ) (249627480947/500000000000 : ℝ) (499254961883/1000000000000 : ℝ) (249627480947/500000000000 : ℝ) (499254961883/1000000000000 : ℝ) (249627480947/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4073/32768 : ℝ))) 6 (499254961883/1000000000000 : ℝ) (249627480947/500000000000 : ℝ) (499254961883/1000000000000 : ℝ) (249627480947/500000000000 : ℝ) (499254961883/1000000000000 : ℝ) (249627480947/500000000000 : ℝ) (499254961883/1000000000000 : ℝ) (249627480947/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4073/32768 : ℝ))) 7 (499254961883/1000000000000 : ℝ) (249627480947/500000000000 : ℝ) (499254961883/1000000000000 : ℝ) (249627480947/500000000000 : ℝ) (499254961883/1000000000000 : ℝ) (249627480947/500000000000 : ℝ) (499254961883/1000000000000 : ℝ) (249627480947/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4073/32768 : ℝ)) hmem 8 (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ) (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4073/32768 : ℝ))) hcmem 8 (499254961883/1000000000000 : ℝ) (249627480947/500000000000 : ℝ) (499254961883/1000000000000 : ℝ) (249627480947/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4073/32768 : ℝ)) (124034554751/125000000000 : ℝ) (992276438011/1000000000000 : ℝ) (499254961883/1000000000000 : ℝ) (249627480947/500000000000 : ℝ) (790332038753/1000000000000 : ℝ) (790332038773/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0147_exp_lower
  have heNumeric : (410981116021/200000000000 : ℝ)/4 ≤ Real.exp (-83258057581/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410981116021/200000000000 : ℝ)/4 ≤ Real.exp ((509/4096 : ℝ)-(790332038773/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (509/4096 : ℝ) (4073/32768 : ℝ) (790332038773/1000000000000 : ℝ) (410981116021/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0148; no trusted numerical premise.
theorem cover8_leaf0148_exp_radius : (998059251110772419/1000000000000000000 : ℝ) ≤ Real.exp ((-2037/131072 : ℝ)/8) ∧ Real.exp ((-2037/131072 : ℝ)/8) ≤ (49902962555538621/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2037/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0148_exp_lower : (46005680514896037/50000000000000000 : ℝ) ≤ Real.exp ((-213140805399/320000000000 : ℝ)/8) ∧ Real.exp ((-213140805399/320000000000 : ℝ)/8) ≤ (920113610297920741/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-213140805399/320000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0148_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452218559/500000000000 : ℝ) ≤ 4*Real.exp (4073/32768 : ℝ)*Real.exp (-mu (radius 8 (2037/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452218559/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2037/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0148_exp_radius
  have hrNumeric : (984579062701/1000000000000 : ℝ) ≤ Real.exp (-2037/131072 : ℝ) ∧ Real.exp (-2037/131072 : ℝ) ≤ (492289531351/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984579062701/1000000000000 : ℝ) ≤ (radius 8 (2037/16384 : ℝ)) ∧ (radius 8 (2037/16384 : ℝ)) ≤ (492289531351/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2037/16384 : ℝ)) (984579062701/1000000000000 : ℝ) (492289531351/500000000000 : ℝ) (87470093873/500000000000 : ℝ) (174940187753/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2037/16384 : ℝ)) (984579062701/1000000000000 : ℝ) (492289531351/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2037/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984579062701/1000000000000 : ℝ) (492289531351/500000000000 : ℝ) (19845790627/20000000000 : ℝ) (992289531351/1000000000000 : ℝ) (198451914851/200000000000 : ℝ) (62016223391/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2037/16384 : ℝ)) 1 (19845790627/20000000000 : ℝ) (992289531351/1000000000000 : ℝ) (198451914851/200000000000 : ℝ) (62016223391/62500000000 : ℝ) (496137276401/500000000000 : ℝ) (248068638201/250000000000 : ℝ) (992274552689/1000000000000 : ℝ) (992274552691/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2037/16384 : ℝ)) 2 (496137276401/500000000000 : ℝ) (248068638201/250000000000 : ℝ) (992274552689/1000000000000 : ℝ) (992274552691/1000000000000 : ℝ) (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ) (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2037/16384 : ℝ)) 3 (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ) (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ) (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ) (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2037/16384 : ℝ)) 4 (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ) (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ) (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ) (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2037/16384 : ℝ)) 5 (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ) (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ) (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ) (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2037/16384 : ℝ)) 6 (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ) (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ) (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ) (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2037/16384 : ℝ)) 7 (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ) (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ) (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ) (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2037/16384 : ℝ))) (87470093873/500000000000 : ℝ) (174940187753/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2037/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87470093873/500000000000 : ℝ) (174940187753/1000000000000 : ℝ) (587470093873/1000000000000 : ℝ) (587470093877/1000000000000 : ℝ) (5228231473/12500000000 : ℝ) (418258517849/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2037/16384 : ℝ))) 1 (587470093873/1000000000000 : ℝ) (587470093877/1000000000000 : ℝ) (5228231473/12500000000 : ℝ) (418258517849/1000000000000 : ℝ) (7857254779/15625000000 : ℝ) (502864305863/1000000000000 : ℝ) (123923961247/250000000000 : ℝ) (123923961249/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2037/16384 : ℝ))) 2 (7857254779/15625000000 : ℝ) (502864305863/1000000000000 : ℝ) (123923961247/250000000000 : ℝ) (123923961249/250000000000 : ℝ) (249640037711/500000000000 : ℝ) (49928007543/100000000000 : ℝ) (62408401253/125000000000 : ℝ) (31204200627/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2037/16384 : ℝ))) 3 (249640037711/500000000000 : ℝ) (49928007543/100000000000 : ℝ) (62408401253/125000000000 : ℝ) (31204200627/62500000000 : ℝ) (499273642723/1000000000000 : ℝ) (499273642731/1000000000000 : ℝ) (499273642681/1000000000000 : ℝ) (49927364269/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2037/16384 : ℝ))) 4 (499273642723/1000000000000 : ℝ) (499273642731/1000000000000 : ℝ) (499273642681/1000000000000 : ℝ) (49927364269/100000000000 : ℝ) (249636821351/500000000000 : ℝ) (499273642711/1000000000000 : ℝ) (499273642701/1000000000000 : ℝ) (499273642711/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2037/16384 : ℝ))) 5 (249636821351/500000000000 : ℝ) (499273642711/1000000000000 : ℝ) (499273642701/1000000000000 : ℝ) (499273642711/1000000000000 : ℝ) (499273642701/1000000000000 : ℝ) (499273642711/1000000000000 : ℝ) (499273642701/1000000000000 : ℝ) (499273642711/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2037/16384 : ℝ))) 6 (499273642701/1000000000000 : ℝ) (499273642711/1000000000000 : ℝ) (499273642701/1000000000000 : ℝ) (499273642711/1000000000000 : ℝ) (499273642701/1000000000000 : ℝ) (499273642711/1000000000000 : ℝ) (499273642701/1000000000000 : ℝ) (499273642711/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2037/16384 : ℝ))) 7 (499273642701/1000000000000 : ℝ) (499273642711/1000000000000 : ℝ) (499273642701/1000000000000 : ℝ) (499273642711/1000000000000 : ℝ) (499273642701/1000000000000 : ℝ) (499273642711/1000000000000 : ℝ) (499273642701/1000000000000 : ℝ) (499273642711/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2037/16384 : ℝ)) hmem 8 (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ) (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2037/16384 : ℝ))) hcmem 8 (499273642701/1000000000000 : ℝ) (499273642711/1000000000000 : ℝ) (499273642701/1000000000000 : ℝ) (499273642711/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2037/16384 : ℝ)) (198454910549/200000000000 : ℝ) (248068638187/250000000000 : ℝ) (499273642701/1000000000000 : ℝ) (499273642711/1000000000000 : ℝ) (197590778139/250000000000 : ℝ) (31614524503/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0148_exp_lower
  have heNumeric : (1027452218559/500000000000 : ℝ)/4 ≤ Real.exp (-213140805399/320000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452218559/500000000000 : ℝ)/4 ≤ Real.exp ((4073/32768 : ℝ)-(31614524503/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4073/32768 : ℝ) (2037/16384 : ℝ) (31614524503/40000000000 : ℝ) (1027452218559/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0149; no trusted numerical premise.
theorem cover8_leaf0149_exp_radius : (249514693799787217/250000000000000000 : ℝ) ≤ Real.exp ((-4075/262144 : ℝ)/8) ∧ Real.exp ((-4075/262144 : ℝ)/8) ≤ (998058775199148869/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4075/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0149_exp_lower : (460056773460025883/500000000000000000 : ℝ) ≤ Real.exp ((-2664262271663/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664262271663/4000000000000 : ℝ)/8) ≤ (920113546920051767/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664262271663/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0149_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (82196132191/40000000000 : ℝ) ≤ 4*Real.exp (2037/16384 : ℝ)*Real.exp (-mu (radius 8 (4075/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (82196132191/40000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4075/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0149_exp_radius
  have hrNumeric : (984575306837/1000000000000 : ℝ) ≤ Real.exp (-4075/262144 : ℝ) ∧ Real.exp (-4075/262144 : ℝ) ≤ (492287653419/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984575306837/1000000000000 : ℝ) ≤ (radius 8 (4075/32768 : ℝ)) ∧ (radius 8 (4075/32768 : ℝ)) ≤ (492287653419/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4075/32768 : ℝ)) (984575306837/1000000000000 : ℝ) (492287653419/500000000000 : ℝ) (5467541399/31250000000 : ℝ) (6998452991/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4075/32768 : ℝ)) (984575306837/1000000000000 : ℝ) (492287653419/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4075/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984575306837/1000000000000 : ℝ) (492287653419/500000000000 : ℝ) (496143826709/500000000000 : ℝ) (992287653419/1000000000000 : ℝ) (992257681671/1000000000000 : ℝ) (992257681673/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4075/32768 : ℝ)) 1 (496143826709/500000000000 : ℝ) (992287653419/1000000000000 : ℝ) (992257681671/1000000000000 : ℝ) (992257681673/1000000000000 : ℝ) (124034083443/125000000000 : ℝ) (496136333773/500000000000 : ℝ) (992272667431/1000000000000 : ℝ) (992272667433/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4075/32768 : ℝ)) 2 (124034083443/125000000000 : ℝ) (496136333773/500000000000 : ℝ) (992272667431/1000000000000 : ℝ) (992272667433/1000000000000 : ℝ) (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ) (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4075/32768 : ℝ)) 3 (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ) (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ) (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ) (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4075/32768 : ℝ)) 4 (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ) (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ) (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ) (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4075/32768 : ℝ)) 5 (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ) (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ) (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ) (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4075/32768 : ℝ)) 6 (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ) (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ) (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ) (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4075/32768 : ℝ)) 7 (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ) (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ) (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ) (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4075/32768 : ℝ))) (5467541399/31250000000 : ℝ) (6998452991/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4075/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5467541399/31250000000 : ℝ) (6998452991/40000000000 : ℝ) (36717541399/62500000000 : ℝ) (146870165597/250000000000 : ℝ) (418283784969/1000000000000 : ℝ) (209141892489/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4075/32768 : ℝ))) 1 (36717541399/62500000000 : ℝ) (146870165597/250000000000 : ℝ) (418283784969/1000000000000 : ℝ) (209141892489/500000000000 : ℝ) (125720555919/250000000000 : ℝ) (502882223683/1000000000000 : ℝ) (2478576381/5000000000 : ℝ) (30982204763/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4075/32768 : ℝ))) 2 (125720555919/250000000000 : ℝ) (502882223683/1000000000000 : ℝ) (2478576381/5000000000 : ℝ) (30982204763/62500000000 : ℝ) (249649374969/500000000000 : ℝ) (249649374973/500000000000 : ℝ) (499285890453/1000000000000 : ℝ) (499285890461/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4075/32768 : ℝ))) 3 (249649374969/500000000000 : ℝ) (249649374973/500000000000 : ℝ) (499285890453/1000000000000 : ℝ) (499285890461/1000000000000 : ℝ) (99858464039/200000000000 : ℝ) (124823080051/250000000000 : ℝ) (249646160077/500000000000 : ℝ) (499292320163/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4075/32768 : ℝ))) 4 (99858464039/200000000000 : ℝ) (124823080051/250000000000 : ℝ) (249646160077/500000000000 : ℝ) (499292320163/1000000000000 : ℝ) (249646160087/500000000000 : ℝ) (62411540023/125000000000 : ℝ) (249646160087/500000000000 : ℝ) (62411540023/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4075/32768 : ℝ))) 5 (249646160087/500000000000 : ℝ) (62411540023/125000000000 : ℝ) (249646160087/500000000000 : ℝ) (62411540023/125000000000 : ℝ) (249646160087/500000000000 : ℝ) (62411540023/125000000000 : ℝ) (249646160087/500000000000 : ℝ) (62411540023/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4075/32768 : ℝ))) 6 (249646160087/500000000000 : ℝ) (62411540023/125000000000 : ℝ) (249646160087/500000000000 : ℝ) (62411540023/125000000000 : ℝ) (249646160087/500000000000 : ℝ) (62411540023/125000000000 : ℝ) (249646160087/500000000000 : ℝ) (62411540023/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4075/32768 : ℝ))) 7 (249646160087/500000000000 : ℝ) (62411540023/125000000000 : ℝ) (249646160087/500000000000 : ℝ) (62411540023/125000000000 : ℝ) (249646160087/500000000000 : ℝ) (62411540023/125000000000 : ℝ) (249646160087/500000000000 : ℝ) (62411540023/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4075/32768 : ℝ)) hmem 8 (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ) (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4075/32768 : ℝ))) hcmem 8 (249646160087/500000000000 : ℝ) (62411540023/125000000000 : ℝ) (249646160087/500000000000 : ℝ) (62411540023/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4075/32768 : ℝ)) (992272667487/1000000000000 : ℝ) (99227266749/100000000000 : ℝ) (249646160087/500000000000 : ℝ) (62411540023/125000000000 : ℝ) (395197090589/500000000000 : ℝ) (790394181197/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0149_exp_lower
  have heNumeric : (82196132191/40000000000 : ℝ)/4 ≤ Real.exp (-2664262271663/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (82196132191/40000000000 : ℝ)/4 ≤ Real.exp ((2037/16384 : ℝ)-(790394181197/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2037/16384 : ℝ) (4075/32768 : ℝ) (790394181197/1000000000000 : ℝ) (82196132191/40000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0125_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0125_certificate
#check SmaleRate.Proofs.cover8_leaf0126_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0126_certificate
#check SmaleRate.Proofs.cover8_leaf0127_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0127_certificate
#check SmaleRate.Proofs.cover8_leaf0128_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0128_certificate
#check SmaleRate.Proofs.cover8_leaf0129_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0129_certificate
#check SmaleRate.Proofs.cover8_leaf0130_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0130_certificate
#check SmaleRate.Proofs.cover8_leaf0131_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0131_certificate
#check SmaleRate.Proofs.cover8_leaf0132_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0132_certificate
#check SmaleRate.Proofs.cover8_leaf0133_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0133_certificate
#check SmaleRate.Proofs.cover8_leaf0134_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0134_certificate
#check SmaleRate.Proofs.cover8_leaf0135_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0135_certificate
#check SmaleRate.Proofs.cover8_leaf0136_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0136_certificate
#check SmaleRate.Proofs.cover8_leaf0137_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0137_certificate
#check SmaleRate.Proofs.cover8_leaf0138_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0138_certificate
#check SmaleRate.Proofs.cover8_leaf0139_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0139_certificate
#check SmaleRate.Proofs.cover8_leaf0140_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0140_certificate
#check SmaleRate.Proofs.cover8_leaf0141_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0141_certificate
#check SmaleRate.Proofs.cover8_leaf0142_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0142_certificate
#check SmaleRate.Proofs.cover8_leaf0143_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0143_certificate
#check SmaleRate.Proofs.cover8_leaf0144_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0144_certificate
#check SmaleRate.Proofs.cover8_leaf0145_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0145_certificate
#check SmaleRate.Proofs.cover8_leaf0146_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0146_certificate
#check SmaleRate.Proofs.cover8_leaf0147_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0147_certificate
#check SmaleRate.Proofs.cover8_leaf0148_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0148_certificate
#check SmaleRate.Proofs.cover8_leaf0149_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0149_certificate
