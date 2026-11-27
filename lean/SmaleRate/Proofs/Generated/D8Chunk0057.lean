/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1425; no trusted numerical premise.
theorem cover8_leaf1425_exp_radius : (249495509354592257/250000000000000000 : ℝ) ≤ Real.exp ((-16945/1048576 : ℝ)/8) ∧ Real.exp ((-16945/1048576 : ℝ)/8) ≤ (997982037418369029/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16945/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1425_exp_lower : (920113581199026363/1000000000000000000 : ℝ) ≤ Real.exp ((-1332130539749/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332130539749/2000000000000 : ℝ)/8) ≤ (230028395299756591/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332130539749/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1425_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451958611/500000000000 : ℝ) ≤ 4*Real.exp (1059/8192 : ℝ)*Real.exp (-mu (radius 8 (16945/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451958611/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16945/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1425_exp_radius
  have hrNumeric : (983969861169/1000000000000 : ℝ) ≤ Real.exp (-16945/1048576 : ℝ) ∧ Real.exp (-16945/1048576 : ℝ) ≤ (98396986117/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983969861169/1000000000000 : ℝ) ≤ (radius 8 (16945/131072 : ℝ)) ∧ (radius 8 (16945/131072 : ℝ)) ≤ (98396986117/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16945/131072 : ℝ)) (983969861169/1000000000000 : ℝ) (98396986117/100000000000 : ℝ) (44583708003/250000000000 : ℝ) (178334832019/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16945/131072 : ℝ)) (983969861169/1000000000000 : ℝ) (98396986117/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16945/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983969861169/1000000000000 : ℝ) (98396986117/100000000000 : ℝ) (123998116323/125000000000 : ℝ) (198396986117/200000000000 : ℝ) (991952549857/1000000000000 : ℝ) (991952549859/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16945/131072 : ℝ)) 1 (123998116323/125000000000 : ℝ) (198396986117/200000000000 : ℝ) (991952549857/1000000000000 : ℝ) (991952549859/1000000000000 : ℝ) (49598437011/50000000000 : ℝ) (495984370111/500000000000 : ℝ) (123996092511/125000000000 : ℝ) (99196874009/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16945/131072 : ℝ)) 2 (49598437011/50000000000 : ℝ) (495984370111/500000000000 : ℝ) (123996092511/125000000000 : ℝ) (99196874009/100000000000 : ℝ) (495984370077/500000000000 : ℝ) (247992185039/250000000000 : ℝ) (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16945/131072 : ℝ)) 3 (495984370077/500000000000 : ℝ) (247992185039/250000000000 : ℝ) (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ) (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ) (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16945/131072 : ℝ)) 4 (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ) (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ) (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ) (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16945/131072 : ℝ)) 5 (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ) (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ) (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ) (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16945/131072 : ℝ)) 6 (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ) (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ) (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ) (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16945/131072 : ℝ)) 7 (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ) (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ) (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ) (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16945/131072 : ℝ))) (44583708003/250000000000 : ℝ) (178334832019/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16945/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44583708003/250000000000 : ℝ) (178334832019/1000000000000 : ℝ) (294583708003/500000000000 : ℝ) (58916741601/100000000000 : ℝ) (1689188359/4000000000 : ℝ) (2639356811/6250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16945/131072 : ℝ))) 1 (294583708003/500000000000 : ℝ) (58916741601/100000000000 : ℝ) (1689188359/4000000000 : ℝ) (2639356811/6250000000 : ℝ) (252866126439/500000000000 : ℝ) (101146450577/200000000000 : ℝ) (498802250551/1000000000000 : ℝ) (498802250559/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16945/131072 : ℝ))) 2 (252866126439/500000000000 : ℝ) (101146450577/200000000000 : ℝ) (498802250551/1000000000000 : ℝ) (498802250559/1000000000000 : ℝ) (251133625857/500000000000 : ℝ) (251133625861/500000000000 : ℝ) (100451059907/200000000000 : ℝ) (62781912443/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16945/131072 : ℝ))) 3 (251133625857/500000000000 : ℝ) (251133625861/500000000000 : ℝ) (100451059907/200000000000 : ℝ) (62781912443/125000000000 : ℝ) (62782659453/125000000000 : ℝ) (502261275633/1000000000000 : ℝ) (125565318897/250000000000 : ℝ) (251130637799/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16945/131072 : ℝ))) 4 (62782659453/125000000000 : ℝ) (502261275633/1000000000000 : ℝ) (125565318897/250000000000 : ℝ) (251130637799/500000000000 : ℝ) (251130637803/500000000000 : ℝ) (15695664863/31250000000 : ℝ) (100452255121/200000000000 : ℝ) (15695664863/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16945/131072 : ℝ))) 5 (251130637803/500000000000 : ℝ) (15695664863/31250000000 : ℝ) (100452255121/200000000000 : ℝ) (15695664863/31250000000 : ℝ) (100452255121/200000000000 : ℝ) (15695664863/31250000000 : ℝ) (100452255121/200000000000 : ℝ) (15695664863/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16945/131072 : ℝ))) 6 (100452255121/200000000000 : ℝ) (15695664863/31250000000 : ℝ) (100452255121/200000000000 : ℝ) (15695664863/31250000000 : ℝ) (100452255121/200000000000 : ℝ) (15695664863/31250000000 : ℝ) (100452255121/200000000000 : ℝ) (15695664863/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16945/131072 : ℝ))) 7 (100452255121/200000000000 : ℝ) (15695664863/31250000000 : ℝ) (100452255121/200000000000 : ℝ) (15695664863/31250000000 : ℝ) (100452255121/200000000000 : ℝ) (15695664863/31250000000 : ℝ) (100452255121/200000000000 : ℝ) (15695664863/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16945/131072 : ℝ)) hmem 8 (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ) (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16945/131072 : ℝ))) hcmem 8 (100452255121/200000000000 : ℝ) (15695664863/31250000000 : ℝ) (100452255121/200000000000 : ℝ) (15695664863/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16945/131072 : ℝ)) (991968740153/1000000000000 : ℝ) (247992185039/250000000000 : ℝ) (100452255121/200000000000 : ℝ) (15695664863/31250000000 : ℝ) (795337730791/1000000000000 : ℝ) (198834432703/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1425_exp_lower
  have heNumeric : (1027451958611/500000000000 : ℝ)/4 ≤ Real.exp (-1332130539749/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451958611/500000000000 : ℝ)/4 ≤ Real.exp ((1059/8192 : ℝ)-(198834432703/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1059/8192 : ℝ) (16945/131072 : ℝ) (198834432703/250000000000 : ℝ) (1027451958611/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1426; no trusted numerical premise.
theorem cover8_leaf1426_exp_radius : (498990959224823227/500000000000000000 : ℝ) ≤ Real.exp ((-8473/524288 : ℝ)/8) ∧ Real.exp ((-8473/524288 : ℝ)/8) ≤ (199596383689929291/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8473/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1426_exp_lower : (920113588666844333/1000000000000000000 : ℝ) ≤ Real.exp ((-21314086558239/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314086558239/32000000000000 : ℝ)/8) ≤ (460056794333422167/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314086558239/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1426_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980810129/200000000000 : ℝ) ≤ 4*Real.exp (16945/131072 : ℝ)*Real.exp (-mu (radius 8 (8473/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (410980810129/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8473/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1426_exp_radius
  have hrNumeric : (983968922783/1000000000000 : ℝ) ≤ Real.exp (-8473/524288 : ℝ) ∧ Real.exp (-8473/524288 : ℝ) ≤ (30749028837/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983968922783/1000000000000 : ℝ) ≤ (radius 8 (8473/65536 : ℝ)) ∧ (radius 8 (8473/65536 : ℝ)) ≤ (30749028837/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8473/65536 : ℝ)) (983968922783/1000000000000 : ℝ) (30749028837/31250000000 : ℝ) (178340009519/1000000000000 : ℝ) (7133600381/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8473/65536 : ℝ)) (983968922783/1000000000000 : ℝ) (30749028837/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8473/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983968922783/1000000000000 : ℝ) (30749028837/31250000000 : ℝ) (991984461391/1000000000000 : ℝ) (61999028837/62500000000 : ℝ) (495976038429/500000000000 : ℝ) (991952076859/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8473/65536 : ℝ)) 1 (991984461391/1000000000000 : ℝ) (61999028837/62500000000 : ℝ) (495976038429/500000000000 : ℝ) (991952076859/1000000000000 : ℝ) (247992067281/250000000000 : ℝ) (495984134563/500000000000 : ℝ) (15499504203/15625000000 : ℝ) (495984134497/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8473/65536 : ℝ)) 2 (247992067281/250000000000 : ℝ) (495984134563/500000000000 : ℝ) (15499504203/15625000000 : ℝ) (495984134497/500000000000 : ℝ) (495984134529/500000000000 : ℝ) (49598413453/50000000000 : ℝ) (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8473/65536 : ℝ)) 3 (495984134529/500000000000 : ℝ) (49598413453/50000000000 : ℝ) (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ) (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ) (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8473/65536 : ℝ)) 4 (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ) (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ) (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ) (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8473/65536 : ℝ)) 5 (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ) (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ) (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ) (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8473/65536 : ℝ)) 6 (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ) (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ) (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ) (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8473/65536 : ℝ)) 7 (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ) (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ) (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ) (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8473/65536 : ℝ))) (178340009519/1000000000000 : ℝ) (7133600381/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8473/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178340009519/1000000000000 : ℝ) (7133600381/40000000000 : ℝ) (589170004759/1000000000000 : ℝ) (589170004763/1000000000000 : ℝ) (422303219877/1000000000000 : ℝ) (84460643977/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8473/65536 : ℝ))) 1 (589170004759/1000000000000 : ℝ) (589170004763/1000000000000 : ℝ) (422303219877/1000000000000 : ℝ) (84460643977/200000000000 : ℝ) (252868306159/500000000000 : ℝ) (126434153081/250000000000 : ℝ) (31175435421/62500000000 : ℝ) (498806966743/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8473/65536 : ℝ))) 2 (252868306159/500000000000 : ℝ) (126434153081/250000000000 : ℝ) (31175435421/62500000000 : ℝ) (498806966743/1000000000000 : ℝ) (502271789527/1000000000000 : ℝ) (251135894767/500000000000 : ℝ) (251129919343/500000000000 : ℝ) (251129919347/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8473/65536 : ℝ))) 3 (502271789527/1000000000000 : ℝ) (251135894767/500000000000 : ℝ) (251129919343/500000000000 : ℝ) (251129919347/500000000000 : ℝ) (251132907053/500000000000 : ℝ) (251132907057/500000000000 : ℝ) (50226581407/100000000000 : ℝ) (502265814079/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8473/65536 : ℝ))) 4 (251132907053/500000000000 : ℝ) (251132907057/500000000000 : ℝ) (50226581407/100000000000 : ℝ) (502265814079/1000000000000 : ℝ) (62783226761/125000000000 : ℝ) (502265814097/1000000000000 : ℝ) (502265814087/1000000000000 : ℝ) (502265814097/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8473/65536 : ℝ))) 5 (62783226761/125000000000 : ℝ) (502265814097/1000000000000 : ℝ) (502265814087/1000000000000 : ℝ) (502265814097/1000000000000 : ℝ) (502265814087/1000000000000 : ℝ) (502265814097/1000000000000 : ℝ) (502265814087/1000000000000 : ℝ) (502265814097/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8473/65536 : ℝ))) 6 (502265814087/1000000000000 : ℝ) (502265814097/1000000000000 : ℝ) (502265814087/1000000000000 : ℝ) (502265814097/1000000000000 : ℝ) (502265814087/1000000000000 : ℝ) (502265814097/1000000000000 : ℝ) (502265814087/1000000000000 : ℝ) (502265814097/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8473/65536 : ℝ))) 7 (502265814087/1000000000000 : ℝ) (502265814097/1000000000000 : ℝ) (502265814087/1000000000000 : ℝ) (502265814097/1000000000000 : ℝ) (502265814087/1000000000000 : ℝ) (502265814097/1000000000000 : ℝ) (502265814087/1000000000000 : ℝ) (502265814097/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8473/65536 : ℝ)) hmem 8 (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ) (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8473/65536 : ℝ))) hcmem 8 (502265814087/1000000000000 : ℝ) (502265814097/1000000000000 : ℝ) (502265814087/1000000000000 : ℝ) (502265814097/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8473/65536 : ℝ)) (991968269057/1000000000000 : ℝ) (49598413453/50000000000 : ℝ) (502265814087/1000000000000 : ℝ) (502265814097/1000000000000 : ℝ) (397672647629/500000000000 : ℝ) (795345295277/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1426_exp_lower
  have heNumeric : (410980810129/200000000000 : ℝ)/4 ≤ Real.exp (-21314086558239/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980810129/200000000000 : ℝ)/4 ≤ Real.exp ((16945/131072 : ℝ)-(795345295277/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16945/131072 : ℝ) (8473/65536 : ℝ) (795345295277/1000000000000 : ℝ) (410980810129/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1427; no trusted numerical premise.
theorem cover8_leaf1427_exp_radius : (997981799480938063/1000000000000000000 : ℝ) ≤ Real.exp ((-16947/1048576 : ℝ)/8) ∧ Real.exp ((-16947/1048576 : ℝ)/8) ≤ (62373862467558629/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16947/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1427_exp_lower : (460056798084295777/500000000000000000 : ℝ) ≤ Real.exp ((-10657042235527/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657042235527/16000000000000 : ℝ)/8) ≤ (184022719233718311/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657042235527/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1427_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726046169/250000000000 : ℝ) ≤ 4*Real.exp (8473/65536 : ℝ)*Real.exp (-mu (radius 8 (16947/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513726046169/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16947/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1427_exp_radius
  have hrNumeric : (983967984397/1000000000000 : ℝ) ≤ Real.exp (-16947/1048576 : ℝ) ∧ Real.exp (-16947/1048576 : ℝ) ≤ (491983992199/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983967984397/1000000000000 : ℝ) ≤ (radius 8 (16947/131072 : ℝ)) ∧ (radius 8 (16947/131072 : ℝ)) ≤ (491983992199/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16947/131072 : ℝ)) (983967984397/1000000000000 : ℝ) (491983992199/500000000000 : ℝ) (17834518687/100000000000 : ℝ) (44586296719/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16947/131072 : ℝ)) (983967984397/1000000000000 : ℝ) (491983992199/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16947/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983967984397/1000000000000 : ℝ) (491983992199/500000000000 : ℝ) (495991996099/500000000000 : ℝ) (991983992199/1000000000000 : ℝ) (495975801929/500000000000 : ℝ) (991951603859/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16947/131072 : ℝ)) 1 (495991996099/500000000000 : ℝ) (991983992199/1000000000000 : ℝ) (495975801929/500000000000 : ℝ) (991951603859/1000000000000 : ℝ) (247991949507/250000000000 : ℝ) (991967798029/1000000000000 : ℝ) (198393559579/200000000000 : ℝ) (991967797897/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16947/131072 : ℝ)) 2 (247991949507/250000000000 : ℝ) (991967798029/1000000000000 : ℝ) (198393559579/200000000000 : ℝ) (991967797897/1000000000000 : ℝ) (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ) (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16947/131072 : ℝ)) 3 (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ) (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ) (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ) (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16947/131072 : ℝ)) 4 (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ) (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ) (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ) (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16947/131072 : ℝ)) 5 (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ) (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ) (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ) (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16947/131072 : ℝ)) 6 (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ) (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ) (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ) (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16947/131072 : ℝ)) 7 (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ) (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ) (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ) (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16947/131072 : ℝ))) (17834518687/100000000000 : ℝ) (44586296719/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16947/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17834518687/100000000000 : ℝ) (44586296719/250000000000 : ℝ) (117834518687/200000000000 : ℝ) (294586296719/500000000000 : ℝ) (42230934973/100000000000 : ℝ) (211154674869/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16947/131072 : ℝ))) 1 (117834518687/200000000000 : ℝ) (294586296719/500000000000 : ℝ) (42230934973/100000000000 : ℝ) (211154674869/500000000000 : ℝ) (252870485791/500000000000 : ℝ) (126435242897/250000000000 : ℝ) (249405841357/500000000000 : ℝ) (498811682721/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16947/131072 : ℝ))) 2 (252870485791/500000000000 : ℝ) (126435242897/250000000000 : ℝ) (249405841357/500000000000 : ℝ) (498811682721/1000000000000 : ℝ) (125569081787/250000000000 : ℝ) (100455265431/200000000000 : ℝ) (251132188823/500000000000 : ℝ) (502264377653/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16947/131072 : ℝ))) 3 (125569081787/250000000000 : ℝ) (100455265431/200000000000 : ℝ) (251132188823/500000000000 : ℝ) (502264377653/1000000000000 : ℝ) (502270352397/1000000000000 : ℝ) (125567588101/250000000000 : ℝ) (502270352361/1000000000000 : ℝ) (502270352369/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16947/131072 : ℝ))) 4 (502270352397/1000000000000 : ℝ) (125567588101/250000000000 : ℝ) (502270352361/1000000000000 : ℝ) (502270352369/1000000000000 : ℝ) (502270352379/1000000000000 : ℝ) (502270352387/1000000000000 : ℝ) (251135176189/500000000000 : ℝ) (502270352387/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16947/131072 : ℝ))) 5 (502270352379/1000000000000 : ℝ) (502270352387/1000000000000 : ℝ) (251135176189/500000000000 : ℝ) (502270352387/1000000000000 : ℝ) (251135176189/500000000000 : ℝ) (502270352387/1000000000000 : ℝ) (251135176189/500000000000 : ℝ) (502270352387/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16947/131072 : ℝ))) 6 (251135176189/500000000000 : ℝ) (502270352387/1000000000000 : ℝ) (251135176189/500000000000 : ℝ) (502270352387/1000000000000 : ℝ) (251135176189/500000000000 : ℝ) (502270352387/1000000000000 : ℝ) (251135176189/500000000000 : ℝ) (502270352387/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16947/131072 : ℝ))) 7 (251135176189/500000000000 : ℝ) (502270352387/1000000000000 : ℝ) (251135176189/500000000000 : ℝ) (502270352387/1000000000000 : ℝ) (251135176189/500000000000 : ℝ) (502270352387/1000000000000 : ℝ) (251135176189/500000000000 : ℝ) (502270352387/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16947/131072 : ℝ)) hmem 8 (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ) (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16947/131072 : ℝ))) hcmem 8 (251135176189/500000000000 : ℝ) (502270352387/1000000000000 : ℝ) (251135176189/500000000000 : ℝ) (502270352387/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16947/131072 : ℝ)) (991967797961/1000000000000 : ℝ) (991967797963/1000000000000 : ℝ) (251135176189/500000000000 : ℝ) (502270352387/1000000000000 : ℝ) (79535285943/100000000000 : ℝ) (795352859447/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1427_exp_lower
  have heNumeric : (513726046169/250000000000 : ℝ)/4 ≤ Real.exp (-10657042235527/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726046169/250000000000 : ℝ)/4 ≤ Real.exp ((8473/65536 : ℝ)-(795352859447/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8473/65536 : ℝ) (16947/131072 : ℝ) (795352859447/1000000000000 : ℝ) (513726046169/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1428; no trusted numerical premise.
theorem cover8_leaf1428_exp_radius : (997981680512243853/1000000000000000000 : ℝ) ≤ Real.exp ((-4237/262144 : ℝ)/8) ∧ Real.exp ((-4237/262144 : ℝ)/8) ≤ (498990840256121927/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4237/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1428_exp_lower : (920113603705878223/1000000000000000000 : ℝ) ≤ Real.exp ((-21314082373981/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314082373981/32000000000000 : ℝ)/8) ≤ (57507100231617389/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314082373981/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1428_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904319341/1000000000000 : ℝ) ≤ 4*Real.exp (16947/131072 : ℝ)*Real.exp (-mu (radius 8 (4237/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904319341/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4237/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1428_exp_radius
  have hrNumeric : (983967046013/1000000000000 : ℝ) ≤ Real.exp (-4237/262144 : ℝ) ∧ Real.exp (-4237/262144 : ℝ) ≤ (491983523007/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983967046013/1000000000000 : ℝ) ≤ (radius 8 (4237/32768 : ℝ)) ∧ (radius 8 (4237/32768 : ℝ)) ≤ (491983523007/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4237/32768 : ℝ)) (983967046013/1000000000000 : ℝ) (491983523007/500000000000 : ℝ) (89175182027/500000000000 : ℝ) (178350364061/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4237/32768 : ℝ)) (983967046013/1000000000000 : ℝ) (491983523007/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4237/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983967046013/1000000000000 : ℝ) (491983523007/500000000000 : ℝ) (495991761503/500000000000 : ℝ) (991983523007/1000000000000 : ℝ) (991951130859/1000000000000 : ℝ) (49597556543/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4237/32768 : ℝ)) 1 (495991761503/500000000000 : ℝ) (991983523007/1000000000000 : ℝ) (991951130859/1000000000000 : ℝ) (49597556543/50000000000 : ℝ) (247991831733/250000000000 : ℝ) (495983663467/500000000000 : ℝ) (2479918317/2500000000 : ℝ) (495983663401/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4237/32768 : ℝ)) 2 (247991831733/250000000000 : ℝ) (495983663467/500000000000 : ℝ) (2479918317/2500000000 : ℝ) (495983663401/500000000000 : ℝ) (495983663433/500000000000 : ℝ) (247991831717/250000000000 : ℝ) (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4237/32768 : ℝ)) 3 (495983663433/500000000000 : ℝ) (247991831717/250000000000 : ℝ) (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ) (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ) (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4237/32768 : ℝ)) 4 (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ) (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ) (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ) (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4237/32768 : ℝ)) 5 (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ) (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ) (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ) (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4237/32768 : ℝ)) 6 (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ) (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ) (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ) (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4237/32768 : ℝ)) 7 (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ) (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ) (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ) (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4237/32768 : ℝ))) (89175182027/500000000000 : ℝ) (178350364061/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4237/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89175182027/500000000000 : ℝ) (178350364061/1000000000000 : ℝ) (589175182027/1000000000000 : ℝ) (589175182031/1000000000000 : ℝ) (422315479297/1000000000000 : ℝ) (211157739653/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4237/32768 : ℝ))) 1 (589175182027/1000000000000 : ℝ) (589175182031/1000000000000 : ℝ) (422315479297/1000000000000 : ℝ) (211157739653/500000000000 : ℝ) (252872665331/500000000000 : ℝ) (505745330669/1000000000000 : ℝ) (19952655939/40000000000 : ℝ) (498816398483/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4237/32768 : ℝ))) 2 (252872665331/500000000000 : ℝ) (505745330669/1000000000000 : ℝ) (19952655939/40000000000 : ℝ) (498816398483/1000000000000 : ℝ) (62785108071/125000000000 : ℝ) (7848138509/15625000000 : ℝ) (125567229101/250000000000 : ℝ) (502268916413/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4237/32768 : ℝ))) 3 (62785108071/125000000000 : ℝ) (7848138509/15625000000 : ℝ) (125567229101/250000000000 : ℝ) (502268916413/1000000000000 : ℝ) (251137445243/500000000000 : ℝ) (100454978099/200000000000 : ℝ) (10045497809/20000000000 : ℝ) (502274890459/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4237/32768 : ℝ))) 4 (251137445243/500000000000 : ℝ) (100454978099/200000000000 : ℝ) (10045497809/20000000000 : ℝ) (502274890459/1000000000000 : ℝ) (125568722617/250000000000 : ℝ) (502274890477/1000000000000 : ℝ) (502274890467/1000000000000 : ℝ) (502274890477/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4237/32768 : ℝ))) 5 (125568722617/250000000000 : ℝ) (502274890477/1000000000000 : ℝ) (502274890467/1000000000000 : ℝ) (502274890477/1000000000000 : ℝ) (502274890467/1000000000000 : ℝ) (502274890477/1000000000000 : ℝ) (502274890467/1000000000000 : ℝ) (502274890477/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4237/32768 : ℝ))) 6 (502274890467/1000000000000 : ℝ) (502274890477/1000000000000 : ℝ) (502274890467/1000000000000 : ℝ) (502274890477/1000000000000 : ℝ) (502274890467/1000000000000 : ℝ) (502274890477/1000000000000 : ℝ) (502274890467/1000000000000 : ℝ) (502274890477/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4237/32768 : ℝ))) 7 (502274890467/1000000000000 : ℝ) (502274890477/1000000000000 : ℝ) (502274890467/1000000000000 : ℝ) (502274890477/1000000000000 : ℝ) (502274890467/1000000000000 : ℝ) (502274890477/1000000000000 : ℝ) (502274890467/1000000000000 : ℝ) (502274890477/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4237/32768 : ℝ)) hmem 8 (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ) (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4237/32768 : ℝ))) hcmem 8 (502274890467/1000000000000 : ℝ) (502274890477/1000000000000 : ℝ) (502274890467/1000000000000 : ℝ) (502274890477/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4237/32768 : ℝ)) (198393465373/200000000000 : ℝ) (247991831717/250000000000 : ℝ) (502274890467/1000000000000 : ℝ) (502274890477/1000000000000 : ℝ) (795360423289/1000000000000 : ℝ) (198840105827/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1428_exp_lower
  have heNumeric : (2054904319341/1000000000000 : ℝ)/4 ≤ Real.exp (-21314082373981/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904319341/1000000000000 : ℝ)/4 ≤ Real.exp ((16947/131072 : ℝ)-(198840105827/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16947/131072 : ℝ) (4237/32768 : ℝ) (198840105827/250000000000 : ℝ) (2054904319341/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1429; no trusted numerical premise.
theorem cover8_leaf1429_exp_radius : (498990780771781913/500000000000000000 : ℝ) ≤ Real.exp ((-16949/1048576 : ℝ)/8) ∧ Real.exp ((-16949/1048576 : ℝ)/8) ≤ (997981561543563827/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16949/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1429_exp_lower : (460056805638719593/500000000000000000 : ℝ) ≤ Real.exp ((-5328520066843/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328520066843/8000000000000 : ℝ)/8) ≤ (920113611277439187/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328520066843/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1429_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452227309/500000000000 : ℝ) ≤ 4*Real.exp (4237/32768 : ℝ)*Real.exp (-mu (radius 8 (16949/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452227309/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16949/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1429_exp_radius
  have hrNumeric : (983966107629/1000000000000 : ℝ) ≤ Real.exp (-16949/1048576 : ℝ) ∧ Real.exp (-16949/1048576 : ℝ) ≤ (98396610763/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983966107629/1000000000000 : ℝ) ≤ (radius 8 (16949/131072 : ℝ)) ∧ (radius 8 (16949/131072 : ℝ)) ≤ (98396610763/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16949/131072 : ℝ)) (983966107629/1000000000000 : ℝ) (98396610763/100000000000 : ℝ) (44588885271/250000000000 : ℝ) (17835554109/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16949/131072 : ℝ)) (983966107629/1000000000000 : ℝ) (98396610763/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16949/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983966107629/1000000000000 : ℝ) (98396610763/100000000000 : ℝ) (495991526907/500000000000 : ℝ) (198396610763/200000000000 : ℝ) (49597532893/50000000000 : ℝ) (991950657861/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16949/131072 : ℝ)) 1 (495991526907/500000000000 : ℝ) (198396610763/200000000000 : ℝ) (49597532893/50000000000 : ℝ) (991950657861/1000000000000 : ℝ) (991966855837/1000000000000 : ℝ) (495983427919/500000000000 : ℝ) (123995856963/125000000000 : ℝ) (495983427853/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16949/131072 : ℝ)) 2 (991966855837/1000000000000 : ℝ) (495983427919/500000000000 : ℝ) (123995856963/125000000000 : ℝ) (495983427853/500000000000 : ℝ) (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ) (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16949/131072 : ℝ)) 3 (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ) (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ) (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ) (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16949/131072 : ℝ)) 4 (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ) (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ) (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ) (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16949/131072 : ℝ)) 5 (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ) (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ) (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ) (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16949/131072 : ℝ)) 6 (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ) (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ) (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ) (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16949/131072 : ℝ)) 7 (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ) (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ) (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ) (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16949/131072 : ℝ))) (44588885271/250000000000 : ℝ) (17835554109/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16949/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44588885271/250000000000 : ℝ) (17835554109/100000000000 : ℝ) (294588885271/500000000000 : ℝ) (117835554109/200000000000 : ℝ) (26395100537/62500000000 : ℝ) (2111608043/5000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16949/131072 : ℝ))) 1 (294588885271/500000000000 : ℝ) (117835554109/200000000000 : ℝ) (26395100537/62500000000 : ℝ) (2111608043/5000000000 : ℝ) (505749689567/1000000000000 : ℝ) (505749689573/1000000000000 : ℝ) (498821114029/1000000000000 : ℝ) (124705278509/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16949/131072 : ℝ))) 2 (505749689567/1000000000000 : ℝ) (505749689573/1000000000000 : ℝ) (498821114029/1000000000000 : ℝ) (124705278509/250000000000 : ℝ) (251142700899/500000000000 : ℝ) (100457080361/200000000000 : ℝ) (125568363743/250000000000 : ℝ) (502273454979/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16949/131072 : ℝ))) 3 (251142700899/500000000000 : ℝ) (100457080361/200000000000 : ℝ) (125568363743/250000000000 : ℝ) (502273454979/1000000000000 : ℝ) (100455885677/200000000000 : ℝ) (62784928549/125000000000 : ℝ) (502279428349/1000000000000 : ℝ) (502279428357/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16949/131072 : ℝ))) 4 (100455885677/200000000000 : ℝ) (62784928549/125000000000 : ℝ) (502279428349/1000000000000 : ℝ) (502279428357/1000000000000 : ℝ) (502279428367/1000000000000 : ℝ) (4018235427/8000000000 : ℝ) (251139714183/500000000000 : ℝ) (4018235427/8000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16949/131072 : ℝ))) 5 (502279428367/1000000000000 : ℝ) (4018235427/8000000000 : ℝ) (251139714183/500000000000 : ℝ) (4018235427/8000000000 : ℝ) (251139714183/500000000000 : ℝ) (4018235427/8000000000 : ℝ) (251139714183/500000000000 : ℝ) (4018235427/8000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16949/131072 : ℝ))) 6 (251139714183/500000000000 : ℝ) (4018235427/8000000000 : ℝ) (251139714183/500000000000 : ℝ) (4018235427/8000000000 : ℝ) (251139714183/500000000000 : ℝ) (4018235427/8000000000 : ℝ) (251139714183/500000000000 : ℝ) (4018235427/8000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16949/131072 : ℝ))) 7 (251139714183/500000000000 : ℝ) (4018235427/8000000000 : ℝ) (251139714183/500000000000 : ℝ) (4018235427/8000000000 : ℝ) (251139714183/500000000000 : ℝ) (4018235427/8000000000 : ℝ) (251139714183/500000000000 : ℝ) (4018235427/8000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16949/131072 : ℝ)) hmem 8 (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ) (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16949/131072 : ℝ))) hcmem 8 (251139714183/500000000000 : ℝ) (4018235427/8000000000 : ℝ) (251139714183/500000000000 : ℝ) (4018235427/8000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16949/131072 : ℝ)) (99196685577/100000000000 : ℝ) (247991713943/250000000000 : ℝ) (251139714183/500000000000 : ℝ) (4018235427/8000000000 : ℝ) (397683993427/500000000000 : ℝ) (795367986871/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1429_exp_lower
  have heNumeric : (1027452227309/500000000000 : ℝ)/4 ≤ Real.exp (-5328520066843/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452227309/500000000000 : ℝ)/4 ≤ Real.exp ((4237/32768 : ℝ)-(795367986871/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4237/32768 : ℝ) (16949/131072 : ℝ) (795367986871/1000000000000 : ℝ) (1027452227309/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1430; no trusted numerical premise.
theorem cover8_leaf1430_exp_radius : (49899072128744899/50000000000000000 : ℝ) ≤ Real.exp ((-8475/524288 : ℝ)/8) ∧ Real.exp ((-8475/524288 : ℝ)/8) ≤ (997981442574897981/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8475/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1430_exp_lower : (920113618883734501/1000000000000000000 : ℝ) ≤ Real.exp ((-21314078151099/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314078151099/32000000000000 : ℝ)/8) ≤ (460056809441867251/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314078151099/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1430_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726147629/250000000000 : ℝ) ≤ 4*Real.exp (16949/131072 : ℝ)*Real.exp (-mu (radius 8 (8475/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513726147629/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8475/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1430_exp_radius
  have hrNumeric : (491982584623/500000000000 : ℝ) ≤ Real.exp (-8475/524288 : ℝ) ∧ Real.exp (-8475/524288 : ℝ) ≤ (983965169247/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491982584623/500000000000 : ℝ) ≤ (radius 8 (8475/65536 : ℝ)) ∧ (radius 8 (8475/65536 : ℝ)) ≤ (983965169247/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8475/65536 : ℝ)) (491982584623/500000000000 : ℝ) (983965169247/1000000000000 : ℝ) (178360717953/1000000000000 : ℝ) (178360717959/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8475/65536 : ℝ)) (491982584623/500000000000 : ℝ) (983965169247/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8475/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491982584623/500000000000 : ℝ) (983965169247/1000000000000 : ℝ) (991982584623/1000000000000 : ℝ) (61998911539/62500000000 : ℝ) (991950184861/1000000000000 : ℝ) (495975092431/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8475/65536 : ℝ)) 1 (991982584623/1000000000000 : ℝ) (61998911539/62500000000 : ℝ) (991950184861/1000000000000 : ℝ) (495975092431/500000000000 : ℝ) (495983192371/500000000000 : ℝ) (991966384743/1000000000000 : ℝ) (991966384609/1000000000000 : ℝ) (991966384611/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8475/65536 : ℝ)) 2 (495983192371/500000000000 : ℝ) (991966384743/1000000000000 : ℝ) (991966384609/1000000000000 : ℝ) (991966384611/1000000000000 : ℝ) (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ) (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8475/65536 : ℝ)) 3 (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ) (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ) (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ) (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8475/65536 : ℝ)) 4 (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ) (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ) (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ) (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8475/65536 : ℝ)) 5 (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ) (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ) (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ) (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8475/65536 : ℝ)) 6 (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ) (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ) (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ) (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8475/65536 : ℝ)) 7 (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ) (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ) (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ) (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8475/65536 : ℝ))) (178360717953/1000000000000 : ℝ) (178360717959/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8475/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178360717953/1000000000000 : ℝ) (178360717959/1000000000000 : ℝ) (9205943109/15625000000 : ℝ) (29459017949/50000000000 : ℝ) (422327737607/1000000000000 : ℝ) (84465547523/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8475/65536 : ℝ))) 1 (9205943109/15625000000 : ℝ) (29459017949/50000000000 : ℝ) (422327737607/1000000000000 : ℝ) (84465547523/200000000000 : ℝ) (505754048291/1000000000000 : ℝ) (252877024149/500000000000 : ℝ) (124706457343/250000000000 : ℝ) (498825829379/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8475/65536 : ℝ))) 2 (505754048291/1000000000000 : ℝ) (252877024149/500000000000 : ℝ) (124706457343/250000000000 : ℝ) (498825829379/1000000000000 : ℝ) (502289938831/1000000000000 : ℝ) (502289938839/1000000000000 : ℝ) (502277993343/1000000000000 : ℝ) (502277993351/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8475/65536 : ℝ))) 3 (502289938831/1000000000000 : ℝ) (502289938839/1000000000000 : ℝ) (502277993343/1000000000000 : ℝ) (502277993351/1000000000000 : ℝ) (502283966087/1000000000000 : ℝ) (100456793219/200000000000 : ℝ) (502283966051/1000000000000 : ℝ) (25114198303/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8475/65536 : ℝ))) 4 (502283966087/1000000000000 : ℝ) (100456793219/200000000000 : ℝ) (502283966051/1000000000000 : ℝ) (25114198303/50000000000 : ℝ) (502283966069/1000000000000 : ℝ) (251141983039/500000000000 : ℝ) (125570991517/250000000000 : ℝ) (251141983039/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8475/65536 : ℝ))) 5 (502283966069/1000000000000 : ℝ) (251141983039/500000000000 : ℝ) (125570991517/250000000000 : ℝ) (251141983039/500000000000 : ℝ) (125570991517/250000000000 : ℝ) (251141983039/500000000000 : ℝ) (125570991517/250000000000 : ℝ) (251141983039/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8475/65536 : ℝ))) 6 (125570991517/250000000000 : ℝ) (251141983039/500000000000 : ℝ) (125570991517/250000000000 : ℝ) (251141983039/500000000000 : ℝ) (125570991517/250000000000 : ℝ) (251141983039/500000000000 : ℝ) (125570991517/250000000000 : ℝ) (251141983039/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8475/65536 : ℝ))) 7 (125570991517/250000000000 : ℝ) (251141983039/500000000000 : ℝ) (125570991517/250000000000 : ℝ) (251141983039/500000000000 : ℝ) (125570991517/250000000000 : ℝ) (251141983039/500000000000 : ℝ) (125570991517/250000000000 : ℝ) (251141983039/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8475/65536 : ℝ)) hmem 8 (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ) (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8475/65536 : ℝ))) hcmem 8 (125570991517/250000000000 : ℝ) (251141983039/500000000000 : ℝ) (125570991517/250000000000 : ℝ) (251141983039/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8475/65536 : ℝ)) (39678655387/40000000000 : ℝ) (991966384677/1000000000000 : ℝ) (125570991517/250000000000 : ℝ) (251141983039/500000000000 : ℝ) (397687775057/500000000000 : ℝ) (198843887533/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1430_exp_lower
  have heNumeric : (513726147629/250000000000 : ℝ)/4 ≤ Real.exp (-21314078151099/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726147629/250000000000 : ℝ)/4 ≤ Real.exp ((16949/131072 : ℝ)-(198843887533/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16949/131072 : ℝ) (8475/65536 : ℝ) (198843887533/250000000000 : ℝ) (513726147629/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1431; no trusted numerical premise.
theorem cover8_leaf1431_exp_radius : (997981323606246317/1000000000000000000 : ℝ) ≤ Real.exp ((-16951/1048576 : ℝ)/8) ∧ Real.exp ((-16951/1048576 : ℝ)/8) ≤ (498990661803123159/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16951/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1431_exp_lower : (920113626525684281/1000000000000000000 : ℝ) ≤ Real.exp ((-10657038012453/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657038012453/16000000000000 : ℝ)/8) ≤ (460056813262842141/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657038012453/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1431_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904727051/1000000000000 : ℝ) ≤ 4*Real.exp (8475/65536 : ℝ)*Real.exp (-mu (radius 8 (16951/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904727051/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16951/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1431_exp_radius
  have hrNumeric : (196792846173/200000000000 : ℝ) ≤ Real.exp (-16951/1048576 : ℝ) ∧ Real.exp (-16951/1048576 : ℝ) ≤ (491982115433/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196792846173/200000000000 : ℝ) ≤ (radius 8 (16951/131072 : ℝ)) ∧ (radius 8 (16951/131072 : ℝ)) ≤ (491982115433/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16951/131072 : ℝ)) (196792846173/200000000000 : ℝ) (491982115433/500000000000 : ℝ) (35673178931/200000000000 : ℝ) (89182947331/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16951/131072 : ℝ)) (196792846173/200000000000 : ℝ) (491982115433/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16951/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196792846173/200000000000 : ℝ) (491982115433/500000000000 : ℝ) (123997764429/125000000000 : ℝ) (991982115433/1000000000000 : ℝ) (495974855931/500000000000 : ℝ) (123993713983/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16951/131072 : ℝ)) 1 (123997764429/125000000000 : ℝ) (991982115433/1000000000000 : ℝ) (495974855931/500000000000 : ℝ) (123993713983/125000000000 : ℝ) (991965913647/1000000000000 : ℝ) (991965913649/1000000000000 : ℝ) (495982956757/500000000000 : ℝ) (991965913517/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16951/131072 : ℝ)) 2 (991965913647/1000000000000 : ℝ) (991965913649/1000000000000 : ℝ) (495982956757/500000000000 : ℝ) (991965913517/1000000000000 : ℝ) (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ) (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16951/131072 : ℝ)) 3 (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ) (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ) (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ) (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16951/131072 : ℝ)) 4 (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ) (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ) (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ) (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16951/131072 : ℝ)) 5 (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ) (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ) (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ) (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16951/131072 : ℝ)) 6 (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ) (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ) (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ) (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16951/131072 : ℝ)) 7 (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ) (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ) (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ) (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16951/131072 : ℝ))) (35673178931/200000000000 : ℝ) (89182947331/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16951/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35673178931/200000000000 : ℝ) (89182947331/500000000000 : ℝ) (589182947327/1000000000000 : ℝ) (589182947331/1000000000000 : ℝ) (13197933323/31250000000 : ℝ) (211166933173/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16951/131072 : ℝ))) 1 (589182947327/1000000000000 : ℝ) (589182947331/1000000000000 : ℝ) (13197933323/31250000000 : ℝ) (211166933173/500000000000 : ℝ) (505758406831/1000000000000 : ℝ) (505758406839/1000000000000 : ℝ) (498830544497/1000000000000 : ℝ) (249415272253/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16951/131072 : ℝ))) 2 (505758406831/1000000000000 : ℝ) (505758406839/1000000000000 : ℝ) (498830544497/1000000000000 : ℝ) (249415272253/500000000000 : ℝ) (31393404729/62500000000 : ℝ) (502294475673/1000000000000 : ℝ) (502282531513/1000000000000 : ℝ) (251141265761/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16951/131072 : ℝ))) 3 (31393404729/62500000000 : ℝ) (502294475673/1000000000000 : ℝ) (502282531513/1000000000000 : ℝ) (251141265761/500000000000 : ℝ) (125572125897/250000000000 : ℝ) (251144251799/500000000000 : ℝ) (1962064467/3906250000 : ℝ) (251144251781/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16951/131072 : ℝ))) 4 (125572125897/250000000000 : ℝ) (251144251799/500000000000 : ℝ) (1962064467/3906250000 : ℝ) (251144251781/500000000000 : ℝ) (50228850357/100000000000 : ℝ) (25114425179/50000000000 : ℝ) (502288503569/1000000000000 : ℝ) (25114425179/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16951/131072 : ℝ))) 5 (50228850357/100000000000 : ℝ) (25114425179/50000000000 : ℝ) (502288503569/1000000000000 : ℝ) (25114425179/50000000000 : ℝ) (502288503569/1000000000000 : ℝ) (25114425179/50000000000 : ℝ) (502288503569/1000000000000 : ℝ) (25114425179/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16951/131072 : ℝ))) 6 (502288503569/1000000000000 : ℝ) (25114425179/50000000000 : ℝ) (502288503569/1000000000000 : ℝ) (25114425179/50000000000 : ℝ) (502288503569/1000000000000 : ℝ) (25114425179/50000000000 : ℝ) (502288503569/1000000000000 : ℝ) (25114425179/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16951/131072 : ℝ))) 7 (502288503569/1000000000000 : ℝ) (25114425179/50000000000 : ℝ) (502288503569/1000000000000 : ℝ) (25114425179/50000000000 : ℝ) (502288503569/1000000000000 : ℝ) (25114425179/50000000000 : ℝ) (502288503569/1000000000000 : ℝ) (25114425179/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16951/131072 : ℝ)) hmem 8 (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ) (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16951/131072 : ℝ))) hcmem 8 (502288503569/1000000000000 : ℝ) (25114425179/50000000000 : ℝ) (502288503569/1000000000000 : ℝ) (25114425179/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16951/131072 : ℝ)) (49598295679/50000000000 : ℝ) (991965913583/1000000000000 : ℝ) (502288503569/1000000000000 : ℝ) (25114425179/50000000000 : ℝ) (397691556531/500000000000 : ℝ) (795383113083/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1431_exp_lower
  have heNumeric : (2054904727051/1000000000000 : ℝ)/4 ≤ Real.exp (-10657038012453/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904727051/1000000000000 : ℝ)/4 ≤ Real.exp ((8475/65536 : ℝ)-(795383113083/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8475/65536 : ℝ) (16951/131072 : ℝ) (795383113083/1000000000000 : ℝ) (2054904727051/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1432; no trusted numerical premise.
theorem cover8_leaf1432_exp_radius : (249495301159402209/250000000000000000 : ℝ) ≤ Real.exp ((-2119/131072 : ℝ)/8) ∧ Real.exp ((-2119/131072 : ℝ)/8) ≤ (997981204637608837/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2119/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1432_exp_lower : (184022726840312663/200000000000000000 : ℝ) ≤ Real.exp ((-21314073889273/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314073889273/32000000000000 : ℝ)/8) ≤ (230028408550390829/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314073889273/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1432_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904864193/1000000000000 : ℝ) ≤ 4*Real.exp (16951/131072 : ℝ)*Real.exp (-mu (radius 8 (2119/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904864193/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2119/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1432_exp_radius
  have hrNumeric : (245990823121/250000000000 : ℝ) ≤ Real.exp (-2119/131072 : ℝ) ∧ Real.exp (-2119/131072 : ℝ) ≤ (196792658497/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245990823121/250000000000 : ℝ) ≤ (radius 8 (2119/16384 : ℝ)) ∧ (radius 8 (2119/16384 : ℝ)) ≤ (196792658497/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2119/16384 : ℝ)) (245990823121/250000000000 : ℝ) (196792658497/200000000000 : ℝ) (89185535601/500000000000 : ℝ) (178371071209/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2119/16384 : ℝ)) (245990823121/250000000000 : ℝ) (196792658497/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2119/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245990823121/250000000000 : ℝ) (196792658497/200000000000 : ℝ) (495990823121/500000000000 : ℝ) (991981646243/1000000000000 : ℝ) (61996827429/62500000000 : ℝ) (495974619433/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2119/16384 : ℝ)) 1 (495990823121/500000000000 : ℝ) (991981646243/1000000000000 : ℝ) (61996827429/62500000000 : ℝ) (495974619433/500000000000 : ℝ) (991965442553/1000000000000 : ℝ) (198393088511/200000000000 : ℝ) (49598272121/50000000000 : ℝ) (991965442423/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2119/16384 : ℝ)) 2 (991965442553/1000000000000 : ℝ) (198393088511/200000000000 : ℝ) (49598272121/50000000000 : ℝ) (991965442423/1000000000000 : ℝ) (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ) (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2119/16384 : ℝ)) 3 (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ) (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ) (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ) (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2119/16384 : ℝ)) 4 (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ) (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ) (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ) (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2119/16384 : ℝ)) 5 (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ) (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ) (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ) (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2119/16384 : ℝ)) 6 (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ) (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ) (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ) (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2119/16384 : ℝ)) 7 (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ) (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ) (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ) (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2119/16384 : ℝ))) (89185535601/500000000000 : ℝ) (178371071209/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2119/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89185535601/500000000000 : ℝ) (178371071209/1000000000000 : ℝ) (589185535601/1000000000000 : ℝ) (117837107121/200000000000 : ℝ) (422339994793/1000000000000 : ℝ) (211169997401/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2119/16384 : ℝ))) 1 (589185535601/1000000000000 : ℝ) (117837107121/200000000000 : ℝ) (422339994793/1000000000000 : ℝ) (211169997401/500000000000 : ℝ) (505762765197/1000000000000 : ℝ) (126440691301/250000000000 : ℝ) (498835259417/1000000000000 : ℝ) (19953410377/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2119/16384 : ℝ))) 2 (505762765197/1000000000000 : ℝ) (126440691301/250000000000 : ℝ) (498835259417/1000000000000 : ℝ) (19953410377/40000000000 : ℝ) (502299012307/1000000000000 : ℝ) (100459802463/200000000000 : ℝ) (502287069493/1000000000000 : ℝ) (251143534751/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2119/16384 : ℝ))) 3 (502299012307/1000000000000 : ℝ) (100459802463/200000000000 : ℝ) (502287069493/1000000000000 : ℝ) (251143534751/500000000000 : ℝ) (5022930409/10000000000 : ℝ) (502293040909/1000000000000 : ℝ) (15696657527/31250000000 : ℝ) (251146520437/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2119/16384 : ℝ))) 4 (5022930409/10000000000 : ℝ) (502293040909/1000000000000 : ℝ) (15696657527/31250000000 : ℝ) (251146520437/500000000000 : ℝ) (251146520441/500000000000 : ℝ) (125573260223/250000000000 : ℝ) (502293040881/1000000000000 : ℝ) (125573260223/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2119/16384 : ℝ))) 5 (251146520441/500000000000 : ℝ) (125573260223/250000000000 : ℝ) (502293040881/1000000000000 : ℝ) (125573260223/250000000000 : ℝ) (502293040881/1000000000000 : ℝ) (125573260223/250000000000 : ℝ) (502293040881/1000000000000 : ℝ) (125573260223/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2119/16384 : ℝ))) 6 (502293040881/1000000000000 : ℝ) (125573260223/250000000000 : ℝ) (502293040881/1000000000000 : ℝ) (125573260223/250000000000 : ℝ) (502293040881/1000000000000 : ℝ) (125573260223/250000000000 : ℝ) (502293040881/1000000000000 : ℝ) (125573260223/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2119/16384 : ℝ))) 7 (502293040881/1000000000000 : ℝ) (125573260223/250000000000 : ℝ) (502293040881/1000000000000 : ℝ) (125573260223/250000000000 : ℝ) (502293040881/1000000000000 : ℝ) (125573260223/250000000000 : ℝ) (502293040881/1000000000000 : ℝ) (125573260223/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2119/16384 : ℝ)) hmem 8 (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ) (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2119/16384 : ℝ))) hcmem 8 (502293040881/1000000000000 : ℝ) (125573260223/250000000000 : ℝ) (502293040881/1000000000000 : ℝ) (125573260223/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2119/16384 : ℝ)) (495982721243/500000000000 : ℝ) (991965442489/1000000000000 : ℝ) (502293040881/1000000000000 : ℝ) (125573260223/250000000000 : ℝ) (397695337859/500000000000 : ℝ) (795390675739/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1432_exp_lower
  have heNumeric : (2054904864193/1000000000000 : ℝ)/4 ≤ Real.exp (-21314073889273/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904864193/1000000000000 : ℝ)/4 ≤ Real.exp ((16951/131072 : ℝ)-(795390675739/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16951/131072 : ℝ) (2119/16384 : ℝ) (795390675739/1000000000000 : ℝ) (2054904864193/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1433; no trusted numerical premise.
theorem cover8_leaf1433_exp_radius : (997981085668985537/1000000000000000000 : ℝ) ≤ Real.exp ((-16953/1048576 : ℝ)/8) ∧ Real.exp ((-16953/1048576 : ℝ)/8) ≤ (498990542834492769/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16953/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1433_exp_lower : (36804545676510071/40000000000000000 : ℝ) ≤ Real.exp ((-2664258967977/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664258967977/4000000000000 : ℝ)/8) ≤ (28753551309773493/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664258967977/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1433_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410981000393/200000000000 : ℝ) ≤ 4*Real.exp (2119/16384 : ℝ)*Real.exp (-mu (radius 8 (16953/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (410981000393/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16953/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1433_exp_radius
  have hrNumeric : (122995294263/125000000000 : ℝ) ≤ Real.exp (-16953/1048576 : ℝ) ∧ Real.exp (-16953/1048576 : ℝ) ≤ (196792470821/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122995294263/125000000000 : ℝ) ≤ (radius 8 (16953/131072 : ℝ)) ∧ (radius 8 (16953/131072 : ℝ)) ≤ (196792470821/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16953/131072 : ℝ)) (122995294263/125000000000 : ℝ) (196792470821/200000000000 : ℝ) (178376247589/1000000000000 : ℝ) (44594061899/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16953/131072 : ℝ)) (122995294263/125000000000 : ℝ) (196792470821/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16953/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122995294263/125000000000 : ℝ) (196792470821/200000000000 : ℝ) (247995294263/250000000000 : ℝ) (991981177053/1000000000000 : ℝ) (495974382933/500000000000 : ℝ) (991948765867/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16953/131072 : ℝ)) 1 (247995294263/250000000000 : ℝ) (991981177053/1000000000000 : ℝ) (495974382933/500000000000 : ℝ) (991948765867/1000000000000 : ℝ) (991964971459/1000000000000 : ℝ) (49598248573/50000000000 : ℝ) (495982485663/500000000000 : ℝ) (15499452677/15625000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16953/131072 : ℝ)) 2 (991964971459/1000000000000 : ℝ) (49598248573/50000000000 : ℝ) (495982485663/500000000000 : ℝ) (15499452677/15625000000 : ℝ) (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ) (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16953/131072 : ℝ)) 3 (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ) (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ) (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ) (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16953/131072 : ℝ)) 4 (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ) (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ) (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ) (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16953/131072 : ℝ)) 5 (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ) (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ) (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ) (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16953/131072 : ℝ)) 6 (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ) (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ) (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ) (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16953/131072 : ℝ)) 7 (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ) (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ) (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ) (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16953/131072 : ℝ))) (178376247589/1000000000000 : ℝ) (44594061899/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16953/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178376247589/1000000000000 : ℝ) (44594061899/250000000000 : ℝ) (294594061897/500000000000 : ℝ) (294594061899/500000000000 : ℝ) (422346122971/1000000000000 : ℝ) (21117306149/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16953/131072 : ℝ))) 1 (294594061897/500000000000 : ℝ) (294594061899/500000000000 : ℝ) (422346122971/1000000000000 : ℝ) (21117306149/50000000000 : ℝ) (252883561691/500000000000 : ℝ) (505767123389/1000000000000 : ℝ) (124709993531/250000000000 : ℝ) (124709993533/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16953/131072 : ℝ))) 2 (252883561691/500000000000 : ℝ) (505767123389/1000000000000 : ℝ) (124709993531/250000000000 : ℝ) (124709993533/250000000000 : ℝ) (502303548753/1000000000000 : ℝ) (502303548761/1000000000000 : ℝ) (125572901819/250000000000 : ℝ) (100458321457/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16953/131072 : ℝ))) 3 (502303548753/1000000000000 : ℝ) (502303548761/1000000000000 : ℝ) (125572901819/250000000000 : ℝ) (100458321457/200000000000 : ℝ) (251148789007/500000000000 : ℝ) (502297578023/1000000000000 : ℝ) (502297577979/1000000000000 : ℝ) (125574394497/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16953/131072 : ℝ))) 4 (251148789007/500000000000 : ℝ) (502297578023/1000000000000 : ℝ) (502297577979/1000000000000 : ℝ) (125574394497/250000000000 : ℝ) (125574394499/250000000000 : ℝ) (251148789003/500000000000 : ℝ) (125574394499/250000000000 : ℝ) (251148789003/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16953/131072 : ℝ))) 5 (125574394499/250000000000 : ℝ) (251148789003/500000000000 : ℝ) (125574394499/250000000000 : ℝ) (251148789003/500000000000 : ℝ) (125574394499/250000000000 : ℝ) (251148789003/500000000000 : ℝ) (125574394499/250000000000 : ℝ) (251148789003/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16953/131072 : ℝ))) 6 (125574394499/250000000000 : ℝ) (251148789003/500000000000 : ℝ) (125574394499/250000000000 : ℝ) (251148789003/500000000000 : ℝ) (125574394499/250000000000 : ℝ) (251148789003/500000000000 : ℝ) (125574394499/250000000000 : ℝ) (251148789003/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16953/131072 : ℝ))) 7 (125574394499/250000000000 : ℝ) (251148789003/500000000000 : ℝ) (125574394499/250000000000 : ℝ) (251148789003/500000000000 : ℝ) (125574394499/250000000000 : ℝ) (251148789003/500000000000 : ℝ) (125574394499/250000000000 : ℝ) (251148789003/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16953/131072 : ℝ)) hmem 8 (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ) (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16953/131072 : ℝ))) hcmem 8 (125574394499/250000000000 : ℝ) (251148789003/500000000000 : ℝ) (125574394499/250000000000 : ℝ) (251148789003/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16953/131072 : ℝ)) (7749726339/7812500000 : ℝ) (495982485697/500000000000 : ℝ) (125574394499/250000000000 : ℝ) (251148789003/500000000000 : ℝ) (79539823807/100000000000 : ℝ) (99424779761/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1433_exp_lower
  have heNumeric : (410981000393/200000000000 : ℝ)/4 ≤ Real.exp (-2664258967977/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410981000393/200000000000 : ℝ)/4 ≤ Real.exp ((2119/16384 : ℝ)-(99424779761/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2119/16384 : ℝ) (16953/131072 : ℝ) (99424779761/125000000000 : ℝ) (410981000393/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1434; no trusted numerical premise.
theorem cover8_leaf1434_exp_radius : (997980966700376421/1000000000000000000 : ℝ) ≤ Real.exp ((-8477/524288 : ℝ)/8) ∧ Real.exp ((-8477/524288 : ℝ)/8) ≤ (498990483350188211/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8477/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1434_exp_lower : (920113649657524447/1000000000000000000 : ℝ) ≤ Real.exp ((-4262813917803/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262813917803/6400000000000 : ℝ)/8) ≤ (28753551551797639/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262813917803/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1434_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054905140337/1000000000000 : ℝ) ≤ 4*Real.exp (16953/131072 : ℝ)*Real.exp (-mu (radius 8 (8477/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054905140337/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8477/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1434_exp_radius
  have hrNumeric : (245990353931/250000000000 : ℝ) ≤ Real.exp (-8477/524288 : ℝ) ∧ Real.exp (-8477/524288 : ℝ) ≤ (39358456629/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245990353931/250000000000 : ℝ) ≤ (radius 8 (8477/65536 : ℝ)) ∧ (radius 8 (8477/65536 : ℝ)) ≤ (39358456629/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8477/65536 : ℝ)) (245990353931/250000000000 : ℝ) (39358456629/40000000000 : ℝ) (178381423821/1000000000000 : ℝ) (178381423827/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8477/65536 : ℝ)) (245990353931/250000000000 : ℝ) (39358456629/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8477/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245990353931/250000000000 : ℝ) (39358456629/40000000000 : ℝ) (495990353931/500000000000 : ℝ) (991980707863/1000000000000 : ℝ) (247987073217/250000000000 : ℝ) (991948292869/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8477/65536 : ℝ)) 1 (495990353931/500000000000 : ℝ) (991980707863/1000000000000 : ℝ) (247987073217/250000000000 : ℝ) (991948292869/1000000000000 : ℝ) (198392900073/200000000000 : ℝ) (495982250183/500000000000 : ℝ) (123995562529/125000000000 : ℝ) (495982250117/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8477/65536 : ℝ)) 2 (198392900073/200000000000 : ℝ) (495982250183/500000000000 : ℝ) (123995562529/125000000000 : ℝ) (495982250117/500000000000 : ℝ) (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ) (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8477/65536 : ℝ)) 3 (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ) (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ) (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ) (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8477/65536 : ℝ)) 4 (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ) (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ) (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ) (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8477/65536 : ℝ)) 5 (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ) (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ) (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ) (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8477/65536 : ℝ)) 6 (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ) (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ) (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ) (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8477/65536 : ℝ)) 7 (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ) (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ) (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ) (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8477/65536 : ℝ))) (178381423821/1000000000000 : ℝ) (178381423827/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8477/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178381423821/1000000000000 : ℝ) (178381423827/1000000000000 : ℝ) (58919071191/100000000000 : ℝ) (294595355957/500000000000 : ℝ) (422352250877/1000000000000 : ℝ) (84470450177/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8477/65536 : ℝ))) 1 (58919071191/100000000000 : ℝ) (294595355957/500000000000 : ℝ) (422352250877/1000000000000 : ℝ) (84470450177/200000000000 : ℝ) (505771481393/1000000000000 : ℝ) (2528857407/5000000000 : ℝ) (249422344313/500000000000 : ℝ) (249422344317/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8477/65536 : ℝ))) 2 (505771481393/1000000000000 : ℝ) (2528857407/5000000000 : ℝ) (249422344313/500000000000 : ℝ) (249422344317/500000000000 : ℝ) (502308085009/1000000000000 : ℝ) (502308085017/1000000000000 : ℝ) (50229614487/100000000000 : ℝ) (251148072439/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8477/65536 : ℝ))) 3 (502308085009/1000000000000 : ℝ) (502308085017/1000000000000 : ℝ) (50229614487/100000000000 : ℝ) (251148072439/500000000000 : ℝ) (502302114939/1000000000000 : ℝ) (125575528737/250000000000 : ℝ) (62787764363/125000000000 : ℝ) (502302114913/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8477/65536 : ℝ))) 4 (502302114939/1000000000000 : ℝ) (125575528737/250000000000 : ℝ) (62787764363/125000000000 : ℝ) (502302114913/1000000000000 : ℝ) (502302114921/1000000000000 : ℝ) (502302114931/1000000000000 : ℝ) (502302114921/1000000000000 : ℝ) (502302114931/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8477/65536 : ℝ))) 5 (502302114921/1000000000000 : ℝ) (502302114931/1000000000000 : ℝ) (502302114921/1000000000000 : ℝ) (502302114931/1000000000000 : ℝ) (502302114921/1000000000000 : ℝ) (502302114931/1000000000000 : ℝ) (502302114921/1000000000000 : ℝ) (502302114931/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8477/65536 : ℝ))) 6 (502302114921/1000000000000 : ℝ) (502302114931/1000000000000 : ℝ) (502302114921/1000000000000 : ℝ) (502302114931/1000000000000 : ℝ) (502302114921/1000000000000 : ℝ) (502302114931/1000000000000 : ℝ) (502302114921/1000000000000 : ℝ) (502302114931/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8477/65536 : ℝ))) 7 (502302114921/1000000000000 : ℝ) (502302114931/1000000000000 : ℝ) (502302114921/1000000000000 : ℝ) (502302114931/1000000000000 : ℝ) (502302114921/1000000000000 : ℝ) (502302114931/1000000000000 : ℝ) (502302114921/1000000000000 : ℝ) (502302114931/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8477/65536 : ℝ)) hmem 8 (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ) (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8477/65536 : ℝ))) hcmem 8 (502302114921/1000000000000 : ℝ) (502302114931/1000000000000 : ℝ) (502302114921/1000000000000 : ℝ) (502302114931/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8477/65536 : ℝ)) (495982250149/500000000000 : ℝ) (9919645003/10000000000 : ℝ) (502302114921/1000000000000 : ℝ) (502302114931/1000000000000 : ℝ) (795405800127/1000000000000 : ℝ) (159081160029/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1434_exp_lower
  have heNumeric : (2054905140337/1000000000000 : ℝ)/4 ≤ Real.exp (-4262813917803/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054905140337/1000000000000 : ℝ)/4 ≤ Real.exp ((16953/131072 : ℝ)-(159081160029/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16953/131072 : ℝ) (8477/65536 : ℝ) (159081160029/200000000000 : ℝ) (2054905140337/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1435; no trusted numerical premise.
theorem cover8_leaf1435_exp_radius : (498990423865890743/500000000000000000 : ℝ) ≤ Real.exp ((-16955/1048576 : ℝ)/8) ∧ Real.exp ((-16955/1048576 : ℝ)/8) ≤ (997980847731781487/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16955/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1435_exp_lower : (920113657438181617/1000000000000000000 : ℝ) ≤ Real.exp ((-2131406742423/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131406742423/3200000000000 : ℝ)/8) ≤ (460056828719090809/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131406742423/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1435_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054905279351/1000000000000 : ℝ) ≤ 4*Real.exp (8477/65536 : ℝ)*Real.exp (-mu (radius 8 (16955/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054905279351/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16955/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1435_exp_radius
  have hrNumeric : (491980238673/500000000000 : ℝ) ≤ Real.exp (-16955/1048576 : ℝ) ∧ Real.exp (-16955/1048576 : ℝ) ≤ (983960477347/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491980238673/500000000000 : ℝ) ≤ (radius 8 (16955/131072 : ℝ)) ∧ (radius 8 (16955/131072 : ℝ)) ≤ (983960477347/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16955/131072 : ℝ)) (491980238673/500000000000 : ℝ) (983960477347/1000000000000 : ℝ) (89193299943/500000000000 : ℝ) (178386599893/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16955/131072 : ℝ)) (491980238673/500000000000 : ℝ) (983960477347/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16955/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491980238673/500000000000 : ℝ) (983960477347/1000000000000 : ℝ) (991980238673/1000000000000 : ℝ) (495990119337/500000000000 : ℝ) (99194781987/100000000000 : ℝ) (30998369371/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16955/131072 : ℝ)) 1 (991980238673/1000000000000 : ℝ) (495990119337/500000000000 : ℝ) (99194781987/100000000000 : ℝ) (30998369371/31250000000 : ℝ) (991964029271/1000000000000 : ℝ) (991964029273/1000000000000 : ℝ) (991964029139/1000000000000 : ℝ) (991964029141/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16955/131072 : ℝ)) 2 (991964029271/1000000000000 : ℝ) (991964029273/1000000000000 : ℝ) (991964029139/1000000000000 : ℝ) (991964029141/1000000000000 : ℝ) (198392805841/200000000000 : ℝ) (991964029207/1000000000000 : ℝ) (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16955/131072 : ℝ)) 3 (198392805841/200000000000 : ℝ) (991964029207/1000000000000 : ℝ) (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ) (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ) (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16955/131072 : ℝ)) 4 (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ) (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ) (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ) (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16955/131072 : ℝ)) 5 (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ) (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ) (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ) (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16955/131072 : ℝ)) 6 (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ) (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ) (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ) (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16955/131072 : ℝ)) 7 (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ) (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ) (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ) (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16955/131072 : ℝ))) (89193299943/500000000000 : ℝ) (178386599893/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16955/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89193299943/500000000000 : ℝ) (178386599893/1000000000000 : ℝ) (589193299943/1000000000000 : ℝ) (589193299947/1000000000000 : ℝ) (206229677/488281250 : ℝ) (84471675701/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16955/131072 : ℝ))) 1 (589193299943/1000000000000 : ℝ) (589193299947/1000000000000 : ℝ) (206229677/488281250 : ℝ) (84471675701/200000000000 : ℝ) (505775839219/1000000000000 : ℝ) (252887919613/500000000000 : ℝ) (49884940291/100000000000 : ℝ) (249424701459/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16955/131072 : ℝ))) 2 (505775839219/1000000000000 : ℝ) (252887919613/500000000000 : ℝ) (49884940291/100000000000 : ℝ) (249424701459/500000000000 : ℝ) (62789077633/125000000000 : ℝ) (31394538817/62500000000 : ℝ) (502300682261/1000000000000 : ℝ) (50230068227/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16955/131072 : ℝ))) 3 (62789077633/125000000000 : ℝ) (31394538817/62500000000 : ℝ) (502300682261/1000000000000 : ℝ) (50230068227/100000000000 : ℝ) (251153325831/500000000000 : ℝ) (502306651671/1000000000000 : ℝ) (502306651627/1000000000000 : ℝ) (125576662909/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16955/131072 : ℝ))) 4 (251153325831/500000000000 : ℝ) (502306651671/1000000000000 : ℝ) (502306651627/1000000000000 : ℝ) (125576662909/250000000000 : ℝ) (125576662911/250000000000 : ℝ) (251153325827/500000000000 : ℝ) (125576662911/250000000000 : ℝ) (251153325827/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16955/131072 : ℝ))) 5 (125576662911/250000000000 : ℝ) (251153325827/500000000000 : ℝ) (125576662911/250000000000 : ℝ) (251153325827/500000000000 : ℝ) (125576662911/250000000000 : ℝ) (251153325827/500000000000 : ℝ) (125576662911/250000000000 : ℝ) (251153325827/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16955/131072 : ℝ))) 6 (125576662911/250000000000 : ℝ) (251153325827/500000000000 : ℝ) (125576662911/250000000000 : ℝ) (251153325827/500000000000 : ℝ) (125576662911/250000000000 : ℝ) (251153325827/500000000000 : ℝ) (125576662911/250000000000 : ℝ) (251153325827/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16955/131072 : ℝ))) 7 (125576662911/250000000000 : ℝ) (251153325827/500000000000 : ℝ) (125576662911/250000000000 : ℝ) (251153325827/500000000000 : ℝ) (125576662911/250000000000 : ℝ) (251153325827/500000000000 : ℝ) (125576662911/250000000000 : ℝ) (251153325827/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16955/131072 : ℝ)) hmem 8 (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ) (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16955/131072 : ℝ))) hcmem 8 (125576662911/250000000000 : ℝ) (251153325827/500000000000 : ℝ) (125576662911/250000000000 : ℝ) (251153325827/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16955/131072 : ℝ)) (247991007301/250000000000 : ℝ) (991964029207/1000000000000 : ℝ) (125576662911/250000000000 : ℝ) (251153325827/500000000000 : ℝ) (795413361871/1000000000000 : ℝ) (79541336189/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1435_exp_lower
  have heNumeric : (2054905279351/1000000000000 : ℝ)/4 ≤ Real.exp (-2131406742423/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054905279351/1000000000000 : ℝ)/4 ≤ Real.exp ((8477/65536 : ℝ)-(79541336189/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8477/65536 : ℝ) (16955/131072 : ℝ) (79541336189/100000000000 : ℝ) (2054905279351/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1436; no trusted numerical premise.
theorem cover8_leaf1436_exp_radius : (498990364381600367/500000000000000000 : ℝ) ≤ Real.exp ((-4239/262144 : ℝ)/8) ∧ Real.exp ((-4239/262144 : ℝ)/8) ≤ (199596145752640147/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4239/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1436_exp_lower : (920113665253688157/1000000000000000000 : ℝ) ≤ Real.exp ((-21314065249749/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314065249749/32000000000000 : ℝ)/8) ≤ (460056832626844079/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314065249749/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1436_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054905418987/1000000000000 : ℝ) ≤ 4*Real.exp (16955/131072 : ℝ)*Real.exp (-mu (radius 8 (4239/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054905418987/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4239/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1436_exp_radius
  have hrNumeric : (983959538969/1000000000000 : ℝ) ≤ Real.exp (-4239/262144 : ℝ) ∧ Real.exp (-4239/262144 : ℝ) ≤ (98395953897/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983959538969/1000000000000 : ℝ) ≤ (radius 8 (4239/32768 : ℝ)) ∧ (radius 8 (4239/32768 : ℝ)) ≤ (98395953897/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4239/32768 : ℝ)) (983959538969/1000000000000 : ℝ) (98395953897/100000000000 : ℝ) (178391775791/1000000000000 : ℝ) (178391775797/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4239/32768 : ℝ)) (983959538969/1000000000000 : ℝ) (98395953897/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4239/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983959538969/1000000000000 : ℝ) (98395953897/100000000000 : ℝ) (247994942371/250000000000 : ℝ) (198395953897/200000000000 : ℝ) (991947346873/1000000000000 : ℝ) (495973673437/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4239/32768 : ℝ)) 1 (247994942371/250000000000 : ℝ) (198395953897/200000000000 : ℝ) (991947346873/1000000000000 : ℝ) (495973673437/500000000000 : ℝ) (495981779089/500000000000 : ℝ) (49598177909/50000000000 : ℝ) (495981779023/500000000000 : ℝ) (30998861189/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4239/32768 : ℝ)) 2 (495981779089/500000000000 : ℝ) (49598177909/50000000000 : ℝ) (495981779023/500000000000 : ℝ) (30998861189/31250000000 : ℝ) (30998861191/31250000000 : ℝ) (495981779057/500000000000 : ℝ) (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4239/32768 : ℝ)) 3 (30998861191/31250000000 : ℝ) (495981779057/500000000000 : ℝ) (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ) (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ) (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4239/32768 : ℝ)) 4 (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ) (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ) (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ) (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4239/32768 : ℝ)) 5 (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ) (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ) (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ) (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4239/32768 : ℝ)) 6 (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ) (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ) (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ) (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4239/32768 : ℝ)) 7 (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ) (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ) (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ) (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4239/32768 : ℝ))) (178391775791/1000000000000 : ℝ) (178391775797/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4239/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178391775791/1000000000000 : ℝ) (178391775797/1000000000000 : ℝ) (117839177579/200000000000 : ℝ) (589195887899/1000000000000 : ℝ) (422364505837/1000000000000 : ℝ) (84472901169/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4239/32768 : ℝ))) 1 (117839177579/200000000000 : ℝ) (589195887899/1000000000000 : ℝ) (422364505837/1000000000000 : ℝ) (84472901169/200000000000 : ℝ) (252890098433/500000000000 : ℝ) (63222524609/125000000000 : ℝ) (62356764623/125000000000 : ℝ) (498854116991/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4239/32768 : ℝ))) 2 (252890098433/500000000000 : ℝ) (63222524609/125000000000 : ℝ) (62356764623/125000000000 : ℝ) (498854116991/1000000000000 : ℝ) (20092686277/40000000000 : ℝ) (125579289233/250000000000 : ℝ) (251152609729/500000000000 : ℝ) (251152609733/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4239/32768 : ℝ))) 3 (20092686277/40000000000 : ℝ) (125579289233/250000000000 : ℝ) (251152609729/500000000000 : ℝ) (251152609733/500000000000 : ℝ) (502311188191/1000000000000 : ℝ) (502311188199/1000000000000 : ℝ) (125577797039/250000000000 : ℝ) (125577797041/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4239/32768 : ℝ))) 4 (502311188191/1000000000000 : ℝ) (502311188199/1000000000000 : ℝ) (125577797039/250000000000 : ℝ) (125577797041/250000000000 : ℝ) (502311188173/1000000000000 : ℝ) (251155594091/500000000000 : ℝ) (502311188173/1000000000000 : ℝ) (251155594091/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4239/32768 : ℝ))) 5 (502311188173/1000000000000 : ℝ) (251155594091/500000000000 : ℝ) (502311188173/1000000000000 : ℝ) (251155594091/500000000000 : ℝ) (502311188173/1000000000000 : ℝ) (251155594091/500000000000 : ℝ) (502311188173/1000000000000 : ℝ) (251155594091/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4239/32768 : ℝ))) 6 (502311188173/1000000000000 : ℝ) (251155594091/500000000000 : ℝ) (502311188173/1000000000000 : ℝ) (251155594091/500000000000 : ℝ) (502311188173/1000000000000 : ℝ) (251155594091/500000000000 : ℝ) (502311188173/1000000000000 : ℝ) (251155594091/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4239/32768 : ℝ))) 7 (502311188173/1000000000000 : ℝ) (251155594091/500000000000 : ℝ) (502311188173/1000000000000 : ℝ) (251155594091/500000000000 : ℝ) (502311188173/1000000000000 : ℝ) (251155594091/500000000000 : ℝ) (502311188173/1000000000000 : ℝ) (251155594091/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4239/32768 : ℝ)) hmem 8 (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ) (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4239/32768 : ℝ))) hcmem 8 (502311188173/1000000000000 : ℝ) (251155594091/500000000000 : ℝ) (502311188173/1000000000000 : ℝ) (251155594091/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4239/32768 : ℝ)) (991963558111/1000000000000 : ℝ) (495981779057/500000000000 : ℝ) (502311188173/1000000000000 : ℝ) (251155594091/500000000000 : ℝ) (159084184663/200000000000 : ℝ) (198855230833/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1436_exp_lower
  have heNumeric : (2054905418987/1000000000000 : ℝ)/4 ≤ Real.exp (-21314065249749/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054905418987/1000000000000 : ℝ)/4 ≤ Real.exp ((16955/131072 : ℝ)-(198855230833/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16955/131072 : ℝ) (4239/32768 : ℝ) (198855230833/250000000000 : ℝ) (2054905418987/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1437; no trusted numerical premise.
theorem cover8_leaf1437_exp_radius : (249495152448658541/250000000000000000 : ℝ) ≤ Real.exp ((-16957/1048576 : ℝ)/8) ∧ Real.exp ((-16957/1048576 : ℝ)/8) ≤ (199596121958926833/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16957/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1437_exp_lower : (115014209137861741/125000000000000000 : ℝ) ≤ Real.exp ((-5328515766473/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328515766473/8000000000000 : ℝ)/8) ≤ (920113673102893929/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328515766473/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1437_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (82196222369/40000000000 : ℝ) ≤ 4*Real.exp (4239/32768 : ℝ)*Real.exp (-mu (radius 8 (16957/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (82196222369/40000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16957/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1437_exp_radius
  have hrNumeric : (61497412537/62500000000 : ℝ) ≤ Real.exp (-16957/1048576 : ℝ) ∧ Real.exp (-16957/1048576 : ℝ) ≤ (983958600593/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61497412537/62500000000 : ℝ) ≤ (radius 8 (16957/131072 : ℝ)) ∧ (radius 8 (16957/131072 : ℝ)) ≤ (983958600593/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16957/131072 : ℝ)) (61497412537/62500000000 : ℝ) (983958600593/1000000000000 : ℝ) (8919847577/50000000000 : ℝ) (178396951547/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16957/131072 : ℝ)) (61497412537/62500000000 : ℝ) (983958600593/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16957/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61497412537/62500000000 : ℝ) (983958600593/1000000000000 : ℝ) (123997412537/125000000000 : ℝ) (991979300297/1000000000000 : ℝ) (7935574991/8000000000 : ℝ) (991946873877/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16957/131072 : ℝ)) 1 (123997412537/125000000000 : ℝ) (991979300297/1000000000000 : ℝ) (7935574991/8000000000 : ℝ) (991946873877/1000000000000 : ℝ) (198392617417/200000000000 : ℝ) (991963087087/1000000000000 : ℝ) (991963086953/1000000000000 : ℝ) (198392617391/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16957/131072 : ℝ)) 2 (198392617417/200000000000 : ℝ) (991963087087/1000000000000 : ℝ) (991963086953/1000000000000 : ℝ) (198392617391/200000000000 : ℝ) (991963087019/1000000000000 : ℝ) (991963087021/1000000000000 : ℝ) (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16957/131072 : ℝ)) 3 (991963087019/1000000000000 : ℝ) (991963087021/1000000000000 : ℝ) (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ) (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ) (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16957/131072 : ℝ)) 4 (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ) (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ) (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ) (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16957/131072 : ℝ)) 5 (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ) (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ) (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ) (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16957/131072 : ℝ)) 6 (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ) (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ) (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ) (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16957/131072 : ℝ)) 7 (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ) (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ) (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ) (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16957/131072 : ℝ))) (8919847577/50000000000 : ℝ) (178396951547/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16957/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8919847577/50000000000 : ℝ) (178396951547/1000000000000 : ℝ) (58919847577/100000000000 : ℝ) (294599237887/500000000000 : ℝ) (52796329113/125000000000 : ℝ) (422370632913/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16957/131072 : ℝ))) 1 (58919847577/100000000000 : ℝ) (294599237887/500000000000 : ℝ) (52796329113/125000000000 : ℝ) (422370632913/1000000000000 : ℝ) (505784554337/1000000000000 : ℝ) (63223069293/125000000000 : ℝ) (9977176617/20000000000 : ℝ) (249429415429/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16957/131072 : ℝ))) 2 (505784554337/1000000000000 : ℝ) (63223069293/125000000000 : ℝ) (9977176617/20000000000 : ℝ) (249429415429/500000000000 : ℝ) (502321692593/1000000000000 : ℝ) (502321692601/1000000000000 : ℝ) (502309756463/1000000000000 : ℝ) (62788719559/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16957/131072 : ℝ))) 3 (502321692593/1000000000000 : ℝ) (502321692601/1000000000000 : ℝ) (502309756463/1000000000000 : ℝ) (62788719559/125000000000 : ℝ) (31394732783/62500000000 : ℝ) (502315724537/1000000000000 : ℝ) (125578931123/250000000000 : ℝ) (251157862251/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16957/131072 : ℝ))) 4 (31394732783/62500000000 : ℝ) (502315724537/1000000000000 : ℝ) (125578931123/250000000000 : ℝ) (251157862251/500000000000 : ℝ) (50231572451/100000000000 : ℝ) (12557893113/25000000000 : ℝ) (502315724509/1000000000000 : ℝ) (12557893113/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16957/131072 : ℝ))) 5 (50231572451/100000000000 : ℝ) (12557893113/25000000000 : ℝ) (502315724509/1000000000000 : ℝ) (12557893113/25000000000 : ℝ) (502315724509/1000000000000 : ℝ) (12557893113/25000000000 : ℝ) (502315724509/1000000000000 : ℝ) (12557893113/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16957/131072 : ℝ))) 6 (502315724509/1000000000000 : ℝ) (12557893113/25000000000 : ℝ) (502315724509/1000000000000 : ℝ) (12557893113/25000000000 : ℝ) (502315724509/1000000000000 : ℝ) (12557893113/25000000000 : ℝ) (502315724509/1000000000000 : ℝ) (12557893113/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16957/131072 : ℝ))) 7 (502315724509/1000000000000 : ℝ) (12557893113/25000000000 : ℝ) (502315724509/1000000000000 : ℝ) (12557893113/25000000000 : ℝ) (502315724509/1000000000000 : ℝ) (12557893113/25000000000 : ℝ) (502315724509/1000000000000 : ℝ) (12557893113/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16957/131072 : ℝ)) hmem 8 (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ) (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16957/131072 : ℝ))) hcmem 8 (502315724509/1000000000000 : ℝ) (12557893113/25000000000 : ℝ) (502315724509/1000000000000 : ℝ) (12557893113/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16957/131072 : ℝ)) (495981543509/500000000000 : ℝ) (991963087021/1000000000000 : ℝ) (502315724509/1000000000000 : ℝ) (12557893113/25000000000 : ℝ) (39771424223/50000000000 : ℝ) (795428484481/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1437_exp_lower
  have heNumeric : (82196222369/40000000000 : ℝ)/4 ≤ Real.exp (-5328515766473/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (82196222369/40000000000 : ℝ)/4 ≤ Real.exp ((4239/32768 : ℝ)-(795428484481/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4239/32768 : ℝ) (16957/131072 : ℝ) (795428484481/1000000000000 : ℝ) (82196222369/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1438; no trusted numerical premise.
theorem cover8_leaf1438_exp_radius : (62373780676630111/62500000000000000 : ℝ) ≤ Real.exp ((-8479/524288 : ℝ)/8) ∧ Real.exp ((-8479/524288 : ℝ)/8) ≤ (997980490826081777/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8479/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1438_exp_lower : (460056840494164621/500000000000000000 : ℝ) ≤ Real.exp ((-4262812174391/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262812174391/6400000000000 : ℝ)/8) ≤ (920113680988329243/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262812174391/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1438_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490570011/100000000000 : ℝ) ≤ 4*Real.exp (16957/131072 : ℝ)*Real.exp (-mu (radius 8 (8479/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (205490570011/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8479/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1438_exp_radius
  have hrNumeric : (983957662217/1000000000000 : ℝ) ≤ Real.exp (-8479/524288 : ℝ) ∧ Real.exp (-8479/524288 : ℝ) ≤ (491978831109/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983957662217/1000000000000 : ℝ) ≤ (radius 8 (8479/65536 : ℝ)) ∧ (radius 8 (8479/65536 : ℝ)) ≤ (491978831109/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8479/65536 : ℝ)) (983957662217/1000000000000 : ℝ) (491978831109/500000000000 : ℝ) (44600531781/250000000000 : ℝ) (17840212713/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8479/65536 : ℝ)) (983957662217/1000000000000 : ℝ) (491978831109/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8479/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983957662217/1000000000000 : ℝ) (491978831109/500000000000 : ℝ) (247994707777/250000000000 : ℝ) (991978831109/1000000000000 : ℝ) (991946400879/1000000000000 : ℝ) (12399330011/12500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8479/65536 : ℝ)) 1 (247994707777/250000000000 : ℝ) (991978831109/1000000000000 : ℝ) (991946400879/1000000000000 : ℝ) (12399330011/12500000000 : ℝ) (991962615993/1000000000000 : ℝ) (198392523199/200000000000 : ℝ) (49598130793/50000000000 : ℝ) (495981307931/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8479/65536 : ℝ)) 2 (991962615993/1000000000000 : ℝ) (198392523199/200000000000 : ℝ) (49598130793/50000000000 : ℝ) (495981307931/500000000000 : ℝ) (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ) (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8479/65536 : ℝ)) 3 (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ) (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ) (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ) (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8479/65536 : ℝ)) 4 (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ) (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ) (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ) (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8479/65536 : ℝ)) 5 (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ) (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ) (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ) (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8479/65536 : ℝ)) 6 (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ) (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ) (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ) (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8479/65536 : ℝ)) 7 (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ) (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ) (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ) (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8479/65536 : ℝ))) (44600531781/250000000000 : ℝ) (17840212713/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8479/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44600531781/250000000000 : ℝ) (17840212713/100000000000 : ℝ) (294600531781/500000000000 : ℝ) (117840212713/200000000000 : ℝ) (422376759687/1000000000000 : ℝ) (84475351939/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8479/65536 : ℝ))) 1 (294600531781/500000000000 : ℝ) (117840212713/200000000000 : ℝ) (422376759687/1000000000000 : ℝ) (84475351939/200000000000 : ℝ) (63223613953/125000000000 : ℝ) (50578891163/100000000000 : ℝ) (997727089/2000000000 : ℝ) (498863544507/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8479/65536 : ℝ))) 2 (63223613953/125000000000 : ℝ) (50578891163/100000000000 : ℝ) (997727089/2000000000 : ℝ) (498863544507/1000000000000 : ℝ) (251163114031/500000000000 : ℝ) (502326228069/1000000000000 : ℝ) (125578573317/250000000000 : ℝ) (20092571731/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8479/65536 : ℝ))) 3 (251163114031/500000000000 : ℝ) (502326228069/1000000000000 : ℝ) (125578573317/250000000000 : ℝ) (20092571731/40000000000 : ℝ) (100464052133/200000000000 : ℝ) (7848754073/15625000000 : ℝ) (502320260629/1000000000000 : ℝ) (502320260637/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8479/65536 : ℝ))) 4 (100464052133/200000000000 : ℝ) (7848754073/15625000000 : ℝ) (502320260629/1000000000000 : ℝ) (502320260637/1000000000000 : ℝ) (502320260647/1000000000000 : ℝ) (100464052131/200000000000 : ℝ) (251160130323/500000000000 : ℝ) (100464052131/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8479/65536 : ℝ))) 5 (502320260647/1000000000000 : ℝ) (100464052131/200000000000 : ℝ) (251160130323/500000000000 : ℝ) (100464052131/200000000000 : ℝ) (251160130323/500000000000 : ℝ) (100464052131/200000000000 : ℝ) (251160130323/500000000000 : ℝ) (100464052131/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8479/65536 : ℝ))) 6 (251160130323/500000000000 : ℝ) (100464052131/200000000000 : ℝ) (251160130323/500000000000 : ℝ) (100464052131/200000000000 : ℝ) (251160130323/500000000000 : ℝ) (100464052131/200000000000 : ℝ) (251160130323/500000000000 : ℝ) (100464052131/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8479/65536 : ℝ))) 7 (251160130323/500000000000 : ℝ) (100464052131/200000000000 : ℝ) (251160130323/500000000000 : ℝ) (100464052131/200000000000 : ℝ) (251160130323/500000000000 : ℝ) (100464052131/200000000000 : ℝ) (251160130323/500000000000 : ℝ) (100464052131/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8479/65536 : ℝ)) hmem 8 (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ) (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8479/65536 : ℝ))) hcmem 8 (251160130323/500000000000 : ℝ) (100464052131/200000000000 : ℝ) (251160130323/500000000000 : ℝ) (100464052131/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8479/65536 : ℝ)) (495981307963/500000000000 : ℝ) (991962615929/1000000000000 : ℝ) (251160130323/500000000000 : ℝ) (100464052131/200000000000 : ℝ) (795436045297/1000000000000 : ℝ) (159087209063/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1438_exp_lower
  have heNumeric : (205490570011/100000000000 : ℝ)/4 ≤ Real.exp (-4262812174391/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490570011/100000000000 : ℝ)/4 ≤ Real.exp ((16957/131072 : ℝ)-(159087209063/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16957/131072 : ℝ) (8479/65536 : ℝ) (159087209063/200000000000 : ℝ) (205490570011/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1439; no trusted numerical premise.
theorem cover8_leaf1439_exp_radius : (99798037185754357/100000000000000000 : ℝ) ≤ Real.exp ((-16959/1048576 : ℝ)/8) ∧ Real.exp ((-16959/1048576 : ℝ)/8) ≤ (997980371857543571/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16959/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1439_exp_lower : (460056844453616879/500000000000000000 : ℝ) ≤ Real.exp ((-10657029334353/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657029334353/16000000000000 : ℝ)/8) ≤ (920113688907233759/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657029334353/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1439_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452920797/500000000000 : ℝ) ≤ 4*Real.exp (8479/65536 : ℝ)*Real.exp (-mu (radius 8 (16959/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452920797/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16959/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1439_exp_radius
  have hrNumeric : (491978361921/500000000000 : ℝ) ≤ Real.exp (-16959/1048576 : ℝ) ∧ Real.exp (-16959/1048576 : ℝ) ≤ (983956723843/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491978361921/500000000000 : ℝ) ≤ (radius 8 (16959/131072 : ℝ)) ∧ (radius 8 (16959/131072 : ℝ)) ≤ (983956723843/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16959/131072 : ℝ)) (491978361921/500000000000 : ℝ) (983956723843/1000000000000 : ℝ) (22300912819/125000000000 : ℝ) (178407302559/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16959/131072 : ℝ)) (491978361921/500000000000 : ℝ) (983956723843/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16959/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491978361921/500000000000 : ℝ) (983956723843/1000000000000 : ℝ) (991978361921/1000000000000 : ℝ) (495989180961/500000000000 : ℝ) (495972963941/500000000000 : ℝ) (991945927883/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16959/131072 : ℝ)) 1 (991978361921/1000000000000 : ℝ) (495989180961/500000000000 : ℝ) (495972963941/500000000000 : ℝ) (991945927883/1000000000000 : ℝ) (991962144901/1000000000000 : ℝ) (991962144903/1000000000000 : ℝ) (242178258/244140625 : ℝ) (99196214477/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16959/131072 : ℝ)) 2 (991962144901/1000000000000 : ℝ) (991962144903/1000000000000 : ℝ) (242178258/244140625 : ℝ) (99196214477/100000000000 : ℝ) (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ) (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16959/131072 : ℝ)) 3 (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ) (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ) (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ) (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16959/131072 : ℝ)) 4 (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ) (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ) (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ) (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16959/131072 : ℝ)) 5 (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ) (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ) (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ) (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16959/131072 : ℝ)) 6 (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ) (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ) (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ) (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16959/131072 : ℝ)) 7 (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ) (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ) (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ) (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16959/131072 : ℝ))) (22300912819/125000000000 : ℝ) (178407302559/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16959/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22300912819/125000000000 : ℝ) (178407302559/1000000000000 : ℝ) (147300912819/250000000000 : ℝ) (7365045641/12500000000 : ℝ) (105595721549/250000000000 : ℝ) (211191443103/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16959/131072 : ℝ))) 1 (147300912819/250000000000 : ℝ) (7365045641/12500000000 : ℝ) (105595721549/250000000000 : ℝ) (211191443103/500000000000 : ℝ) (493938739/976562500 : ℝ) (505793268743/1000000000000 : ℝ) (498868257943/1000000000000 : ℝ) (498868257951/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16959/131072 : ℝ))) 2 (493938739/976562500 : ℝ) (505793268743/1000000000000 : ℝ) (498868257943/1000000000000 : ℝ) (498868257951/1000000000000 : ℝ) (502330763339/1000000000000 : ℝ) (502330763347/1000000000000 : ℝ) (502318829881/1000000000000 : ℝ) (50231882989/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16959/131072 : ℝ))) 3 (502330763339/1000000000000 : ℝ) (502330763347/1000000000000 : ℝ) (502318829881/1000000000000 : ℝ) (50231882989/100000000000 : ℝ) (50232479661/100000000000 : ℝ) (502324796619/1000000000000 : ℝ) (251162398287/500000000000 : ℝ) (62790599573/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16959/131072 : ℝ))) 4 (50232479661/100000000000 : ℝ) (502324796619/1000000000000 : ℝ) (251162398287/500000000000 : ℝ) (62790599573/125000000000 : ℝ) (31395299787/62500000000 : ℝ) (251162398301/500000000000 : ℝ) (502324796591/1000000000000 : ℝ) (251162398301/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16959/131072 : ℝ))) 5 (31395299787/62500000000 : ℝ) (251162398301/500000000000 : ℝ) (502324796591/1000000000000 : ℝ) (251162398301/500000000000 : ℝ) (502324796591/1000000000000 : ℝ) (251162398301/500000000000 : ℝ) (502324796591/1000000000000 : ℝ) (251162398301/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16959/131072 : ℝ))) 6 (502324796591/1000000000000 : ℝ) (251162398301/500000000000 : ℝ) (502324796591/1000000000000 : ℝ) (251162398301/500000000000 : ℝ) (502324796591/1000000000000 : ℝ) (251162398301/500000000000 : ℝ) (502324796591/1000000000000 : ℝ) (251162398301/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16959/131072 : ℝ))) 7 (502324796591/1000000000000 : ℝ) (251162398301/500000000000 : ℝ) (502324796591/1000000000000 : ℝ) (251162398301/500000000000 : ℝ) (502324796591/1000000000000 : ℝ) (251162398301/500000000000 : ℝ) (502324796591/1000000000000 : ℝ) (251162398301/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16959/131072 : ℝ)) hmem 8 (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ) (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16959/131072 : ℝ))) hcmem 8 (502324796591/1000000000000 : ℝ) (251162398301/500000000000 : ℝ) (502324796591/1000000000000 : ℝ) (251162398301/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16959/131072 : ℝ)) (495981072417/500000000000 : ℝ) (991962144837/1000000000000 : ℝ) (502324796591/1000000000000 : ℝ) (251162398301/500000000000 : ℝ) (795443605837/1000000000000 : ℝ) (397721802929/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1439_exp_lower
  have heNumeric : (1027452920797/500000000000 : ℝ)/4 ≤ Real.exp (-10657029334353/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452920797/500000000000 : ℝ)/4 ≤ Real.exp ((8479/65536 : ℝ)-(397721802929/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8479/65536 : ℝ) (16959/131072 : ℝ) (397721802929/500000000000 : ℝ) (1027452920797/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1440; no trusted numerical premise.
theorem cover8_leaf1440_exp_radius : (498990126444509773/500000000000000000 : ℝ) ≤ Real.exp ((-265/16384 : ℝ)/8) ∧ Real.exp ((-265/16384 : ℝ)/8) ≤ (997980252889019547/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-265/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1440_exp_lower : (460056848430608839/500000000000000000 : ℝ) ≤ Real.exp ((-21314056455697/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314056455697/32000000000000 : ℝ)/8) ≤ (920113696861217679/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314056455697/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1440_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256863247963/125000000000 : ℝ) ≤ 4*Real.exp (16959/131072 : ℝ)*Real.exp (-mu (radius 8 (265/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (256863247963/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (265/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1440_exp_radius
  have hrNumeric : (245988946367/250000000000 : ℝ) ≤ Real.exp (-265/16384 : ℝ) ∧ Real.exp (-265/16384 : ℝ) ≤ (983955785469/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245988946367/250000000000 : ℝ) ≤ (radius 8 (265/2048 : ℝ)) ∧ (radius 8 (265/2048 : ℝ)) ≤ (983955785469/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (265/2048 : ℝ)) (245988946367/250000000000 : ℝ) (983955785469/1000000000000 : ℝ) (8920623891/50000000000 : ℝ) (178412477827/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (265/2048 : ℝ)) (245988946367/250000000000 : ℝ) (983955785469/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (265/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245988946367/250000000000 : ℝ) (983955785469/1000000000000 : ℝ) (495988946367/500000000000 : ℝ) (198395578547/200000000000 : ℝ) (198389090977/200000000000 : ℝ) (991945454887/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (265/2048 : ℝ)) 1 (495988946367/500000000000 : ℝ) (198395578547/200000000000 : ℝ) (198389090977/200000000000 : ℝ) (991945454887/1000000000000 : ℝ) (991961673809/1000000000000 : ℝ) (991961673811/1000000000000 : ℝ) (247990418419/250000000000 : ℝ) (991961673679/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (265/2048 : ℝ)) 2 (991961673809/1000000000000 : ℝ) (991961673811/1000000000000 : ℝ) (247990418419/250000000000 : ℝ) (991961673679/1000000000000 : ℝ) (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ) (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (265/2048 : ℝ)) 3 (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ) (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ) (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ) (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (265/2048 : ℝ)) 4 (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ) (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ) (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ) (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (265/2048 : ℝ)) 5 (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ) (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ) (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ) (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (265/2048 : ℝ)) 6 (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ) (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ) (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ) (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (265/2048 : ℝ)) 7 (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ) (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ) (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ) (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (265/2048 : ℝ))) (8920623891/50000000000 : ℝ) (178412477827/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (265/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8920623891/50000000000 : ℝ) (178412477827/1000000000000 : ℝ) (58920623891/100000000000 : ℝ) (294603119457/500000000000 : ℝ) (105597253107/250000000000 : ℝ) (422389012437/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (265/2048 : ℝ))) 1 (58920623891/100000000000 : ℝ) (294603119457/500000000000 : ℝ) (105597253107/250000000000 : ℝ) (422389012437/1000000000000 : ℝ) (505797625669/1000000000000 : ℝ) (126449406419/250000000000 : ℝ) (19954918847/40000000000 : ℝ) (498872971183/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (265/2048 : ℝ))) 2 (505797625669/1000000000000 : ℝ) (126449406419/250000000000 : ℝ) (19954918847/40000000000 : ℝ) (498872971183/1000000000000 : ℝ) (251167649211/500000000000 : ℝ) (50233529843/100000000000 : ℝ) (502323366299/1000000000000 : ℝ) (125580841577/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (265/2048 : ℝ))) 3 (251167649211/500000000000 : ℝ) (50233529843/100000000000 : ℝ) (502323366299/1000000000000 : ℝ) (125580841577/250000000000 : ℝ) (12558233309/25000000000 : ℝ) (502329332369/1000000000000 : ℝ) (20093173293/40000000000 : ℝ) (251164666167/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (265/2048 : ℝ))) 4 (12558233309/25000000000 : ℝ) (502329332369/1000000000000 : ℝ) (20093173293/40000000000 : ℝ) (251164666167/500000000000 : ℝ) (251164666171/500000000000 : ℝ) (3924447909/7812500000 : ℝ) (251164666171/500000000000 : ℝ) (3924447909/7812500000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (265/2048 : ℝ))) 5 (251164666171/500000000000 : ℝ) (3924447909/7812500000 : ℝ) (251164666171/500000000000 : ℝ) (3924447909/7812500000 : ℝ) (251164666171/500000000000 : ℝ) (3924447909/7812500000 : ℝ) (251164666171/500000000000 : ℝ) (3924447909/7812500000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (265/2048 : ℝ))) 6 (251164666171/500000000000 : ℝ) (3924447909/7812500000 : ℝ) (251164666171/500000000000 : ℝ) (3924447909/7812500000 : ℝ) (251164666171/500000000000 : ℝ) (3924447909/7812500000 : ℝ) (251164666171/500000000000 : ℝ) (3924447909/7812500000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (265/2048 : ℝ))) 7 (251164666171/500000000000 : ℝ) (3924447909/7812500000 : ℝ) (251164666171/500000000000 : ℝ) (3924447909/7812500000 : ℝ) (251164666171/500000000000 : ℝ) (3924447909/7812500000 : ℝ) (251164666171/500000000000 : ℝ) (3924447909/7812500000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (265/2048 : ℝ)) hmem 8 (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ) (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (265/2048 : ℝ))) hcmem 8 (251164666171/500000000000 : ℝ) (3924447909/7812500000 : ℝ) (251164666171/500000000000 : ℝ) (3924447909/7812500000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (265/2048 : ℝ)) (495980836871/500000000000 : ℝ) (198392334749/200000000000 : ℝ) (251164666171/500000000000 : ℝ) (3924447909/7812500000 : ℝ) (198862791519/250000000000 : ℝ) (49715697881/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1440_exp_lower
  have heNumeric : (256863247963/125000000000 : ℝ)/4 ≤ Real.exp (-21314056455697/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256863247963/125000000000 : ℝ)/4 ≤ Real.exp ((16959/131072 : ℝ)-(49715697881/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16959/131072 : ℝ) (265/2048 : ℝ) (49715697881/62500000000 : ℝ) (256863247963/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1441; no trusted numerical premise.
theorem cover8_leaf1441_exp_radius : (199596026784101941/200000000000000000 : ℝ) ≤ Real.exp ((-16961/1048576 : ℝ)/8) ∧ Real.exp ((-16961/1048576 : ℝ)/8) ≤ (498990066960254853/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16961/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1441_exp_lower : (920113704850165987/1000000000000000000 : ℝ) ≤ Real.exp ((-33303209739/50000000000 : ℝ)/8) ∧ Real.exp ((-33303209739/50000000000 : ℝ)/8) ≤ (230028426212541497/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33303209739/50000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1441_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906126439/1000000000000 : ℝ) ≤ 4*Real.exp (265/2048 : ℝ)*Real.exp (-mu (radius 8 (16961/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906126439/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16961/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1441_exp_radius
  have hrNumeric : (196790969419/200000000000 : ℝ) ≤ Real.exp (-16961/1048576 : ℝ) ∧ Real.exp (-16961/1048576 : ℝ) ≤ (122994355887/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196790969419/200000000000 : ℝ) ≤ (radius 8 (16961/131072 : ℝ)) ∧ (radius 8 (16961/131072 : ℝ)) ≤ (122994355887/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16961/131072 : ℝ)) (196790969419/200000000000 : ℝ) (122994355887/125000000000 : ℝ) (178417652927/1000000000000 : ℝ) (89208826467/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16961/131072 : ℝ)) (196790969419/200000000000 : ℝ) (122994355887/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16961/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196790969419/200000000000 : ℝ) (122994355887/125000000000 : ℝ) (991977423547/1000000000000 : ℝ) (247994355887/250000000000 : ℝ) (991944981889/1000000000000 : ℝ) (99194498189/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16961/131072 : ℝ)) 1 (991977423547/1000000000000 : ℝ) (247994355887/250000000000 : ℝ) (991944981889/1000000000000 : ℝ) (99194498189/100000000000 : ℝ) (495980601359/500000000000 : ℝ) (991961202719/1000000000000 : ℝ) (198392240517/200000000000 : ℝ) (991961202587/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16961/131072 : ℝ)) 2 (495980601359/500000000000 : ℝ) (991961202719/1000000000000 : ℝ) (198392240517/200000000000 : ℝ) (991961202587/1000000000000 : ℝ) (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ) (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16961/131072 : ℝ)) 3 (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ) (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ) (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ) (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16961/131072 : ℝ)) 4 (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ) (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ) (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ) (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16961/131072 : ℝ)) 5 (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ) (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ) (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ) (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16961/131072 : ℝ)) 6 (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ) (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ) (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ) (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16961/131072 : ℝ)) 7 (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ) (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ) (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ) (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16961/131072 : ℝ))) (178417652927/1000000000000 : ℝ) (89208826467/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16961/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178417652927/1000000000000 : ℝ) (89208826467/500000000000 : ℝ) (589208826463/1000000000000 : ℝ) (589208826467/1000000000000 : ℝ) (422395138379/1000000000000 : ℝ) (422395138389/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16961/131072 : ℝ))) 1 (589208826463/1000000000000 : ℝ) (589208826467/1000000000000 : ℝ) (422395138379/1000000000000 : ℝ) (422395138389/1000000000000 : ℝ) (505801982421/1000000000000 : ℝ) (126450495607/250000000000 : ℝ) (99775536839/200000000000 : ℝ) (498877684203/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16961/131072 : ℝ))) 2 (505801982421/1000000000000 : ℝ) (126450495607/250000000000 : ℝ) (99775536839/200000000000 : ℝ) (498877684203/1000000000000 : ℝ) (125584958327/250000000000 : ℝ) (125584958329/250000000000 : ℝ) (502327902521/1000000000000 : ℝ) (502327902529/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16961/131072 : ℝ))) 3 (125584958327/250000000000 : ℝ) (125584958329/250000000000 : ℝ) (502327902521/1000000000000 : ℝ) (502327902529/1000000000000 : ℝ) (251166933957/500000000000 : ℝ) (502333867923/1000000000000 : ℝ) (502333867879/1000000000000 : ℝ) (31395866743/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16961/131072 : ℝ))) 4 (251166933957/500000000000 : ℝ) (502333867923/1000000000000 : ℝ) (502333867879/1000000000000 : ℝ) (31395866743/62500000000 : ℝ) (62791733487/125000000000 : ℝ) (251166933953/500000000000 : ℝ) (62791733487/125000000000 : ℝ) (251166933953/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16961/131072 : ℝ))) 5 (62791733487/125000000000 : ℝ) (251166933953/500000000000 : ℝ) (62791733487/125000000000 : ℝ) (251166933953/500000000000 : ℝ) (62791733487/125000000000 : ℝ) (251166933953/500000000000 : ℝ) (62791733487/125000000000 : ℝ) (251166933953/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16961/131072 : ℝ))) 6 (62791733487/125000000000 : ℝ) (251166933953/500000000000 : ℝ) (62791733487/125000000000 : ℝ) (251166933953/500000000000 : ℝ) (62791733487/125000000000 : ℝ) (251166933953/500000000000 : ℝ) (62791733487/125000000000 : ℝ) (251166933953/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16961/131072 : ℝ))) 7 (62791733487/125000000000 : ℝ) (251166933953/500000000000 : ℝ) (62791733487/125000000000 : ℝ) (251166933953/500000000000 : ℝ) (62791733487/125000000000 : ℝ) (251166933953/500000000000 : ℝ) (62791733487/125000000000 : ℝ) (251166933953/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16961/131072 : ℝ)) hmem 8 (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ) (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16961/131072 : ℝ))) hcmem 8 (62791733487/125000000000 : ℝ) (251166933953/500000000000 : ℝ) (62791733487/125000000000 : ℝ) (251166933953/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16961/131072 : ℝ)) (991961202651/1000000000000 : ℝ) (991961202653/1000000000000 : ℝ) (62791733487/125000000000 : ℝ) (251166933953/500000000000 : ℝ) (198864681503/250000000000 : ℝ) (79545872603/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1441_exp_lower
  have heNumeric : (2054906126439/1000000000000 : ℝ)/4 ≤ Real.exp (-33303209739/50000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906126439/1000000000000 : ℝ)/4 ≤ Real.exp ((265/2048 : ℝ)-(79545872603/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (265/2048 : ℝ) (16961/131072 : ℝ) (79545872603/100000000000 : ℝ) (2054906126439/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1442; no trusted numerical premise.
theorem cover8_leaf1442_exp_radius : (199596002990402809/200000000000000000 : ℝ) ≤ Real.exp ((-8481/524288 : ℝ)/8) ∧ Real.exp ((-8481/524288 : ℝ)/8) ≤ (498990007476007023/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8481/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1442_exp_lower : (920113712873733643/1000000000000000000 : ℝ) ≤ Real.exp ((-21314052000591/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314052000591/32000000000000 : ℝ)/8) ≤ (230028428218433411/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314052000591/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1442_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (64215820931/31250000000 : ℝ) ≤ 4*Real.exp (16961/131072 : ℝ)*Real.exp (-mu (radius 8 (8481/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (64215820931/31250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8481/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1442_exp_radius
  have hrNumeric : (983953908723/1000000000000 : ℝ) ≤ Real.exp (-8481/524288 : ℝ) ∧ Real.exp (-8481/524288 : ℝ) ≤ (245988477181/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983953908723/1000000000000 : ℝ) ≤ (radius 8 (8481/65536 : ℝ)) ∧ (radius 8 (8481/65536 : ℝ)) ≤ (245988477181/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8481/65536 : ℝ)) (983953908723/1000000000000 : ℝ) (245988477181/250000000000 : ℝ) (89211413937/500000000000 : ℝ) (178422827881/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8481/65536 : ℝ)) (983953908723/1000000000000 : ℝ) (245988477181/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8481/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983953908723/1000000000000 : ℝ) (245988477181/250000000000 : ℝ) (991976954361/1000000000000 : ℝ) (495988477181/500000000000 : ℝ) (991944508893/1000000000000 : ℝ) (495972254447/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8481/65536 : ℝ)) 1 (991976954361/1000000000000 : ℝ) (495988477181/500000000000 : ℝ) (991944508893/1000000000000 : ℝ) (495972254447/500000000000 : ℝ) (991960731627/1000000000000 : ℝ) (247990182907/250000000000 : ℝ) (495980365747/500000000000 : ℝ) (123995091437/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8481/65536 : ℝ)) 2 (991960731627/1000000000000 : ℝ) (247990182907/250000000000 : ℝ) (495980365747/500000000000 : ℝ) (123995091437/125000000000 : ℝ) (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ) (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8481/65536 : ℝ)) 3 (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ) (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ) (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ) (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8481/65536 : ℝ)) 4 (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ) (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ) (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ) (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8481/65536 : ℝ)) 5 (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ) (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ) (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ) (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8481/65536 : ℝ)) 6 (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ) (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ) (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ) (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8481/65536 : ℝ)) 7 (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ) (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ) (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ) (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8481/65536 : ℝ))) (89211413937/500000000000 : ℝ) (178422827881/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8481/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89211413937/500000000000 : ℝ) (178422827881/1000000000000 : ℝ) (589211413937/1000000000000 : ℝ) (589211413941/1000000000000 : ℝ) (422401264053/1000000000000 : ℝ) (211200632031/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8481/65536 : ℝ))) 1 (589211413937/1000000000000 : ℝ) (589211413941/1000000000000 : ℝ) (422401264053/1000000000000 : ℝ) (211200632031/500000000000 : ℝ) (101161267799/200000000000 : ℝ) (252903169501/500000000000 : ℝ) (124720599251/250000000000 : ℝ) (124720599253/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8481/65536 : ℝ))) 2 (101161267799/200000000000 : ℝ) (252903169501/500000000000 : ℝ) (124720599251/250000000000 : ℝ) (124720599253/250000000000 : ℝ) (502344367999/1000000000000 : ℝ) (502344368007/1000000000000 : ℝ) (125583109637/250000000000 : ℝ) (125583109639/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8481/65536 : ℝ))) 3 (502344367999/1000000000000 : ℝ) (502344368007/1000000000000 : ℝ) (125583109637/250000000000 : ℝ) (125583109639/250000000000 : ℝ) (502338403273/1000000000000 : ℝ) (251169201641/500000000000 : ℝ) (251169201619/500000000000 : ℝ) (502338403247/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8481/65536 : ℝ))) 4 (502338403273/1000000000000 : ℝ) (251169201641/500000000000 : ℝ) (251169201619/500000000000 : ℝ) (502338403247/1000000000000 : ℝ) (100467680651/200000000000 : ℝ) (100467680653/200000000000 : ℝ) (100467680651/200000000000 : ℝ) (100467680653/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8481/65536 : ℝ))) 5 (100467680651/200000000000 : ℝ) (100467680653/200000000000 : ℝ) (100467680651/200000000000 : ℝ) (100467680653/200000000000 : ℝ) (100467680651/200000000000 : ℝ) (100467680653/200000000000 : ℝ) (100467680651/200000000000 : ℝ) (100467680653/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8481/65536 : ℝ))) 6 (100467680651/200000000000 : ℝ) (100467680653/200000000000 : ℝ) (100467680651/200000000000 : ℝ) (100467680653/200000000000 : ℝ) (100467680651/200000000000 : ℝ) (100467680653/200000000000 : ℝ) (100467680651/200000000000 : ℝ) (100467680653/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8481/65536 : ℝ))) 7 (100467680651/200000000000 : ℝ) (100467680653/200000000000 : ℝ) (100467680651/200000000000 : ℝ) (100467680653/200000000000 : ℝ) (100467680651/200000000000 : ℝ) (100467680653/200000000000 : ℝ) (100467680651/200000000000 : ℝ) (100467680653/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8481/65536 : ℝ)) hmem 8 (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ) (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8481/65536 : ℝ))) hcmem 8 (100467680651/200000000000 : ℝ) (100467680653/200000000000 : ℝ) (100467680651/200000000000 : ℝ) (100467680653/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8481/65536 : ℝ)) (24799018289/25000000000 : ℝ) (495980365781/500000000000 : ℝ) (100467680651/200000000000 : ℝ) (100467680653/200000000000 : ℝ) (198866571411/250000000000 : ℝ) (795466285663/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1442_exp_lower
  have heNumeric : (64215820931/31250000000 : ℝ)/4 ≤ Real.exp (-21314052000591/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (64215820931/31250000000 : ℝ)/4 ≤ Real.exp ((16961/131072 : ℝ)-(795466285663/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16961/131072 : ℝ) (8481/65536 : ℝ) (795466285663/1000000000000 : ℝ) (64215820931/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1443; no trusted numerical premise.
theorem cover8_leaf1443_exp_radius : (124747486997941571/125000000000000000 : ℝ) ≤ Real.exp ((-16963/1048576 : ℝ)/8) ∧ Real.exp ((-16963/1048576 : ℝ)/8) ≤ (997979895983532569/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16963/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1443_exp_lower : (920113720932265691/1000000000000000000 : ℝ) ≤ Real.exp ((-10657024879247/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657024879247/16000000000000 : ℝ)/8) ≤ (230028430233066423/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657024879247/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1443_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490641377/100000000000 : ℝ) ≤ 4*Real.exp (8481/65536 : ℝ)*Real.exp (-mu (radius 8 (16963/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (205490641377/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16963/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1443_exp_radius
  have hrNumeric : (61497060647/62500000000 : ℝ) ≤ Real.exp (-16963/1048576 : ℝ) ∧ Real.exp (-16963/1048576 : ℝ) ≤ (983952970353/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61497060647/62500000000 : ℝ) ≤ (radius 8 (16963/131072 : ℝ)) ∧ (radius 8 (16963/131072 : ℝ)) ≤ (983952970353/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16963/131072 : ℝ)) (61497060647/62500000000 : ℝ) (983952970353/1000000000000 : ℝ) (8921400133/50000000000 : ℝ) (178428002667/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16963/131072 : ℝ)) (61497060647/62500000000 : ℝ) (983952970353/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16963/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61497060647/62500000000 : ℝ) (983952970353/1000000000000 : ℝ) (123997060647/125000000000 : ℝ) (991976485177/1000000000000 : ℝ) (991944035897/1000000000000 : ℝ) (495972017949/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16963/131072 : ℝ)) 1 (123997060647/125000000000 : ℝ) (991976485177/1000000000000 : ℝ) (991944035897/1000000000000 : ℝ) (495972017949/500000000000 : ℝ) (123995032567/125000000000 : ℝ) (495980130269/500000000000 : ℝ) (991960260403/1000000000000 : ℝ) (198392052081/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16963/131072 : ℝ)) 2 (123995032567/125000000000 : ℝ) (495980130269/500000000000 : ℝ) (991960260403/1000000000000 : ℝ) (198392052081/200000000000 : ℝ) (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ) (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16963/131072 : ℝ)) 3 (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ) (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ) (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ) (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16963/131072 : ℝ)) 4 (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ) (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ) (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ) (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16963/131072 : ℝ)) 5 (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ) (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ) (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ) (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16963/131072 : ℝ)) 6 (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ) (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ) (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ) (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16963/131072 : ℝ)) 7 (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ) (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ) (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ) (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16963/131072 : ℝ))) (8921400133/50000000000 : ℝ) (178428002667/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16963/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8921400133/50000000000 : ℝ) (178428002667/1000000000000 : ℝ) (58921400133/100000000000 : ℝ) (294607000667/500000000000 : ℝ) (422407389447/1000000000000 : ℝ) (26400461841/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16963/131072 : ℝ))) 1 (58921400133/100000000000 : ℝ) (294607000667/500000000000 : ℝ) (422407389447/1000000000000 : ℝ) (26400461841/62500000000 : ℝ) (126452673847/250000000000 : ℝ) (101162139079/200000000000 : ℝ) (249443554801/500000000000 : ℝ) (49888710961/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16963/131072 : ℝ))) 2 (126452673847/250000000000 : ℝ) (101162139079/200000000000 : ℝ) (249443554801/500000000000 : ℝ) (49888710961/100000000000 : ℝ) (100469780499/200000000000 : ℝ) (502348902503/1000000000000 : ℝ) (251168487189/500000000000 : ℝ) (502336974387/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16963/131072 : ℝ))) 3 (100469780499/200000000000 : ℝ) (502348902503/1000000000000 : ℝ) (251168487189/500000000000 : ℝ) (502336974387/1000000000000 : ℝ) (125585734609/250000000000 : ℝ) (100468587689/200000000000 : ℝ) (502342938401/1000000000000 : ℝ) (50234293841/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16963/131072 : ℝ))) 4 (125585734609/250000000000 : ℝ) (100468587689/200000000000 : ℝ) (502342938401/1000000000000 : ℝ) (50234293841/100000000000 : ℝ) (251171469209/500000000000 : ℝ) (125585734607/250000000000 : ℝ) (251171469209/500000000000 : ℝ) (125585734607/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16963/131072 : ℝ))) 5 (251171469209/500000000000 : ℝ) (125585734607/250000000000 : ℝ) (251171469209/500000000000 : ℝ) (125585734607/250000000000 : ℝ) (251171469209/500000000000 : ℝ) (125585734607/250000000000 : ℝ) (251171469209/500000000000 : ℝ) (125585734607/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16963/131072 : ℝ))) 6 (251171469209/500000000000 : ℝ) (125585734607/250000000000 : ℝ) (251171469209/500000000000 : ℝ) (125585734607/250000000000 : ℝ) (251171469209/500000000000 : ℝ) (125585734607/250000000000 : ℝ) (251171469209/500000000000 : ℝ) (125585734607/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16963/131072 : ℝ))) 7 (251171469209/500000000000 : ℝ) (125585734607/250000000000 : ℝ) (251171469209/500000000000 : ℝ) (125585734607/250000000000 : ℝ) (251171469209/500000000000 : ℝ) (125585734607/250000000000 : ℝ) (251171469209/500000000000 : ℝ) (125585734607/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16963/131072 : ℝ)) hmem 8 (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ) (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16963/131072 : ℝ))) hcmem 8 (251171469209/500000000000 : ℝ) (125585734607/250000000000 : ℝ) (251171469209/500000000000 : ℝ) (125585734607/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16963/131072 : ℝ)) (991960260469/1000000000000 : ℝ) (123995032559/125000000000 : ℝ) (251171469209/500000000000 : ℝ) (125585734607/250000000000 : ℝ) (795473844973/1000000000000 : ℝ) (3107319707/3906250000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1443_exp_lower
  have heNumeric : (205490641377/100000000000 : ℝ)/4 ≤ Real.exp (-10657024879247/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490641377/100000000000 : ℝ)/4 ≤ Real.exp ((8481/65536 : ℝ)-(3107319707/3906250000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8481/65536 : ℝ) (16963/131072 : ℝ) (3107319707/3906250000 : ℝ) (205490641377/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1444; no trusted numerical premise.
theorem cover8_leaf1444_exp_radius : (997979777015065273/1000000000000000000 : ℝ) ≤ Real.exp ((-4241/262144 : ℝ)/8) ∧ Real.exp ((-4241/262144 : ℝ)/8) ≤ (498989888507532637/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4241/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1444_exp_lower : (920113729025532103/1000000000000000000 : ℝ) ≤ Real.exp ((-21314047506733/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314047506733/32000000000000 : ℝ)/8) ≤ (115014216128191513/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314047506733/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1444_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906558369/1000000000000 : ℝ) ≤ 4*Real.exp (16963/131072 : ℝ)*Real.exp (-mu (radius 8 (4241/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906558369/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4241/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1444_exp_radius
  have hrNumeric : (491976015991/500000000000 : ℝ) ≤ Real.exp (-4241/262144 : ℝ) ∧ Real.exp (-4241/262144 : ℝ) ≤ (983952031983/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491976015991/500000000000 : ℝ) ≤ (radius 8 (4241/32768 : ℝ)) ∧ (radius 8 (4241/32768 : ℝ)) ≤ (983952031983/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4241/32768 : ℝ)) (491976015991/500000000000 : ℝ) (983952031983/1000000000000 : ℝ) (89216588643/500000000000 : ℝ) (44608294323/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4241/32768 : ℝ)) (491976015991/500000000000 : ℝ) (983952031983/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4241/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491976015991/500000000000 : ℝ) (983952031983/1000000000000 : ℝ) (991976015991/1000000000000 : ℝ) (123997001999/125000000000 : ℝ) (991943562901/1000000000000 : ℝ) (991943562903/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4241/32768 : ℝ)) 1 (991976015991/1000000000000 : ℝ) (123997001999/125000000000 : ℝ) (991943562901/1000000000000 : ℝ) (991943562903/1000000000000 : ℝ) (495979894723/500000000000 : ℝ) (123994973681/125000000000 : ℝ) (991959789313/1000000000000 : ℝ) (198391957863/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4241/32768 : ℝ)) 2 (495979894723/500000000000 : ℝ) (123994973681/125000000000 : ℝ) (991959789313/1000000000000 : ℝ) (198391957863/200000000000 : ℝ) (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ) (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4241/32768 : ℝ)) 3 (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ) (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ) (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ) (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4241/32768 : ℝ)) 4 (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ) (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ) (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ) (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4241/32768 : ℝ)) 5 (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ) (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ) (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ) (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4241/32768 : ℝ)) 6 (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ) (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ) (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ) (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4241/32768 : ℝ)) 7 (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ) (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ) (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ) (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4241/32768 : ℝ))) (89216588643/500000000000 : ℝ) (44608294323/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4241/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89216588643/500000000000 : ℝ) (44608294323/250000000000 : ℝ) (589216588643/1000000000000 : ℝ) (294608294323/500000000000 : ℝ) (422413514563/1000000000000 : ℝ) (422413514571/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4241/32768 : ℝ))) 1 (589216588643/1000000000000 : ℝ) (294608294323/500000000000 : ℝ) (422413514563/1000000000000 : ℝ) (422413514571/1000000000000 : ℝ) (505815051603/1000000000000 : ℝ) (505815051609/1000000000000 : ℝ) (498891821989/1000000000000 : ℝ) (124722955499/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4241/32768 : ℝ))) 2 (505815051603/1000000000000 : ℝ) (505815051609/1000000000000 : ℝ) (498891821989/1000000000000 : ℝ) (124722955499/250000000000 : ℝ) (125588359199/250000000000 : ℝ) (502353436803/1000000000000 : ℝ) (251170755007/500000000000 : ℝ) (251170755011/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4241/32768 : ℝ))) 3 (125588359199/250000000000 : ℝ) (502353436803/1000000000000 : ℝ) (251170755007/500000000000 : ℝ) (251170755011/500000000000 : ℝ) (100469494681/200000000000 : ℝ) (502347473413/1000000000000 : ℝ) (502347473369/1000000000000 : ℝ) (251173736689/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4241/32768 : ℝ))) 4 (100469494681/200000000000 : ℝ) (502347473413/1000000000000 : ℝ) (502347473369/1000000000000 : ℝ) (251173736689/500000000000 : ℝ) (502347473387/1000000000000 : ℝ) (125586868349/250000000000 : ℝ) (251173736693/500000000000 : ℝ) (125586868349/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4241/32768 : ℝ))) 5 (502347473387/1000000000000 : ℝ) (125586868349/250000000000 : ℝ) (251173736693/500000000000 : ℝ) (125586868349/250000000000 : ℝ) (251173736693/500000000000 : ℝ) (125586868349/250000000000 : ℝ) (251173736693/500000000000 : ℝ) (125586868349/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4241/32768 : ℝ))) 6 (251173736693/500000000000 : ℝ) (125586868349/250000000000 : ℝ) (251173736693/500000000000 : ℝ) (125586868349/250000000000 : ℝ) (251173736693/500000000000 : ℝ) (125586868349/250000000000 : ℝ) (251173736693/500000000000 : ℝ) (125586868349/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4241/32768 : ℝ))) 7 (251173736693/500000000000 : ℝ) (125586868349/250000000000 : ℝ) (251173736693/500000000000 : ℝ) (125586868349/250000000000 : ℝ) (251173736693/500000000000 : ℝ) (125586868349/250000000000 : ℝ) (251173736693/500000000000 : ℝ) (125586868349/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4241/32768 : ℝ)) hmem 8 (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ) (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4241/32768 : ℝ))) hcmem 8 (251173736693/500000000000 : ℝ) (125586868349/250000000000 : ℝ) (251173736693/500000000000 : ℝ) (125586868349/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4241/32768 : ℝ)) (991959789379/1000000000000 : ℝ) (495979894691/500000000000 : ℝ) (251173736693/500000000000 : ℝ) (125586868349/250000000000 : ℝ) (198870351/250000000 : ℝ) (795481404019/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1444_exp_lower
  have heNumeric : (2054906558369/1000000000000 : ℝ)/4 ≤ Real.exp (-21314047506733/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906558369/1000000000000 : ℝ)/4 ≤ Real.exp ((16963/131072 : ℝ)-(795481404019/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16963/131072 : ℝ) (4241/32768 : ℝ) (795481404019/1000000000000 : ℝ) (2054906558369/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1445; no trusted numerical premise.
theorem cover8_leaf1445_exp_radius : (3118686431395663/3125000000000000 : ℝ) ≤ Real.exp ((-16965/1048576 : ℝ)/8) ∧ Real.exp ((-16965/1048576 : ℝ)/8) ≤ (997979658046612161/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16965/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1445_exp_lower : (460056868576823947/500000000000000000 : ℝ) ≤ Real.exp ((-5328511311319/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328511311319/8000000000000 : ℝ)/8) ≤ (184022747430729579/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328511311319/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1445_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490670359/100000000000 : ℝ) ≤ 4*Real.exp (4241/32768 : ℝ)*Real.exp (-mu (radius 8 (16965/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (205490670359/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16965/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1445_exp_radius
  have hrNumeric : (983951093613/1000000000000 : ℝ) ≤ Real.exp (-16965/1048576 : ℝ) ∧ Real.exp (-16965/1048576 : ℝ) ≤ (491975546807/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983951093613/1000000000000 : ℝ) ≤ (radius 8 (16965/131072 : ℝ)) ∧ (radius 8 (16965/131072 : ℝ)) ≤ (491975546807/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16965/131072 : ℝ)) (983951093613/1000000000000 : ℝ) (491975546807/500000000000 : ℝ) (178438351751/1000000000000 : ℝ) (89219175879/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16965/131072 : ℝ)) (983951093613/1000000000000 : ℝ) (491975546807/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16965/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983951093613/1000000000000 : ℝ) (491975546807/500000000000 : ℝ) (495987773403/500000000000 : ℝ) (991975546807/1000000000000 : ℝ) (495971544953/500000000000 : ℝ) (991943089907/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16965/131072 : ℝ)) 1 (495987773403/500000000000 : ℝ) (991975546807/1000000000000 : ℝ) (495971544953/500000000000 : ℝ) (991943089907/1000000000000 : ℝ) (247989829589/250000000000 : ℝ) (991959318357/1000000000000 : ℝ) (991959318223/1000000000000 : ℝ) (39678372729/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16965/131072 : ℝ)) 2 (247989829589/250000000000 : ℝ) (991959318357/1000000000000 : ℝ) (991959318223/1000000000000 : ℝ) (39678372729/40000000000 : ℝ) (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ) (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16965/131072 : ℝ)) 3 (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ) (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ) (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ) (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16965/131072 : ℝ)) 4 (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ) (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ) (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ) (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16965/131072 : ℝ)) 5 (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ) (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ) (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ) (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16965/131072 : ℝ)) 6 (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ) (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ) (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ) (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16965/131072 : ℝ)) 7 (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ) (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ) (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ) (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16965/131072 : ℝ))) (178438351751/1000000000000 : ℝ) (89219175879/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16965/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178438351751/1000000000000 : ℝ) (89219175879/500000000000 : ℝ) (4713753407/8000000000 : ℝ) (589219175879/1000000000000 : ℝ) (2112098197/5000000000 : ℝ) (422419639409/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16965/131072 : ℝ))) 1 (4713753407/8000000000 : ℝ) (589219175879/1000000000000 : ℝ) (2112098197/5000000000 : ℝ) (422419639409/1000000000000 : ℝ) (505819407637/1000000000000 : ℝ) (126454851911/250000000000 : ℝ) (498896534163/1000000000000 : ℝ) (498896534171/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16965/131072 : ℝ))) 2 (505819407637/1000000000000 : ℝ) (126454851911/250000000000 : ℝ) (498896534163/1000000000000 : ℝ) (498896534171/1000000000000 : ℝ) (5023579709/10000000000 : ℝ) (125589492727/250000000000 : ℝ) (502346045453/1000000000000 : ℝ) (502346045461/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16965/131072 : ℝ))) 3 (5023579709/10000000000 : ℝ) (125589492727/250000000000 : ℝ) (502346045453/1000000000000 : ℝ) (502346045461/1000000000000 : ℝ) (31397000511/62500000000 : ℝ) (100470401637/200000000000 : ℝ) (502352008141/1000000000000 : ℝ) (10047040163/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16965/131072 : ℝ))) 4 (31397000511/62500000000 : ℝ) (100470401637/200000000000 : ℝ) (502352008141/1000000000000 : ℝ) (10047040163/20000000000 : ℝ) (251176004079/500000000000 : ℝ) (62794001021/125000000000 : ℝ) (251176004079/500000000000 : ℝ) (62794001021/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16965/131072 : ℝ))) 5 (251176004079/500000000000 : ℝ) (62794001021/125000000000 : ℝ) (251176004079/500000000000 : ℝ) (62794001021/125000000000 : ℝ) (251176004079/500000000000 : ℝ) (62794001021/125000000000 : ℝ) (251176004079/500000000000 : ℝ) (62794001021/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16965/131072 : ℝ))) 6 (251176004079/500000000000 : ℝ) (62794001021/125000000000 : ℝ) (251176004079/500000000000 : ℝ) (62794001021/125000000000 : ℝ) (251176004079/500000000000 : ℝ) (62794001021/125000000000 : ℝ) (251176004079/500000000000 : ℝ) (62794001021/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16965/131072 : ℝ))) 7 (251176004079/500000000000 : ℝ) (62794001021/125000000000 : ℝ) (251176004079/500000000000 : ℝ) (62794001021/125000000000 : ℝ) (251176004079/500000000000 : ℝ) (62794001021/125000000000 : ℝ) (251176004079/500000000000 : ℝ) (62794001021/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16965/131072 : ℝ)) hmem 8 (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ) (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16965/131072 : ℝ))) hcmem 8 (251176004079/500000000000 : ℝ) (62794001021/125000000000 : ℝ) (251176004079/500000000000 : ℝ) (62794001021/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16965/131072 : ℝ)) (991959318289/1000000000000 : ℝ) (991959318291/1000000000000 : ℝ) (251176004079/500000000000 : ℝ) (62794001021/125000000000 : ℝ) (198872240681/250000000000 : ℝ) (795488962743/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1445_exp_lower
  have heNumeric : (205490670359/100000000000 : ℝ)/4 ≤ Real.exp (-5328511311319/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490670359/100000000000 : ℝ)/4 ≤ Real.exp ((4241/32768 : ℝ)-(795488962743/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4241/32768 : ℝ) (16965/131072 : ℝ) (795488962743/1000000000000 : ℝ) (205490670359/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1446; no trusted numerical premise.
theorem cover8_leaf1446_exp_radius : (997979539078173229/1000000000000000000 : ℝ) ≤ Real.exp ((-8483/524288 : ℝ)/8) ∧ Real.exp ((-8483/524288 : ℝ)/8) ≤ (99797953907817323/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8483/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1446_exp_lower : (460056872657903983/500000000000000000 : ℝ) ≤ Real.exp ((-21314042974347/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314042974347/32000000000000 : ℝ)/8) ≤ (920113745315807967/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314042974347/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1446_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745342471/50000000000 : ℝ) ≤ 4*Real.exp (16965/131072 : ℝ)*Real.exp (-mu (radius 8 (8483/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (102745342471/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8483/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1446_exp_radius
  have hrNumeric : (245987538811/250000000000 : ℝ) ≤ Real.exp (-8483/524288 : ℝ) ∧ Real.exp (-8483/524288 : ℝ) ≤ (196790031049/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245987538811/250000000000 : ℝ) ≤ (radius 8 (8483/65536 : ℝ)) ∧ (radius 8 (8483/65536 : ℝ)) ≤ (196790031049/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8483/65536 : ℝ)) (245987538811/250000000000 : ℝ) (196790031049/200000000000 : ℝ) (178443526061/1000000000000 : ℝ) (44610881517/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8483/65536 : ℝ)) (245987538811/250000000000 : ℝ) (196790031049/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8483/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245987538811/250000000000 : ℝ) (196790031049/200000000000 : ℝ) (495987538811/500000000000 : ℝ) (991975077623/1000000000000 : ℝ) (99194261691/100000000000 : ℝ) (61996413557/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8483/65536 : ℝ)) 1 (495987538811/500000000000 : ℝ) (991975077623/1000000000000 : ℝ) (99194261691/100000000000 : ℝ) (61996413557/62500000000 : ℝ) (495979423633/500000000000 : ℝ) (247989711817/250000000000 : ℝ) (991958847133/1000000000000 : ℝ) (198391769427/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8483/65536 : ℝ)) 2 (495979423633/500000000000 : ℝ) (247989711817/250000000000 : ℝ) (991958847133/1000000000000 : ℝ) (198391769427/200000000000 : ℝ) (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ) (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8483/65536 : ℝ)) 3 (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ) (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ) (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ) (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8483/65536 : ℝ)) 4 (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ) (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ) (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ) (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8483/65536 : ℝ)) 5 (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ) (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ) (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ) (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8483/65536 : ℝ)) 6 (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ) (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ) (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ) (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8483/65536 : ℝ)) 7 (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ) (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ) (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ) (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8483/65536 : ℝ))) (178443526061/1000000000000 : ℝ) (44610881517/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8483/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178443526061/1000000000000 : ℝ) (44610881517/250000000000 : ℝ) (58922176303/100000000000 : ℝ) (294610881517/500000000000 : ℝ) (105606440991/250000000000 : ℝ) (422425763973/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8483/65536 : ℝ))) 1 (58922176303/100000000000 : ℝ) (294610881517/500000000000 : ℝ) (105606440991/250000000000 : ℝ) (422425763973/1000000000000 : ℝ) (505823763497/1000000000000 : ℝ) (31613985219/62500000000 : ℝ) (124725311533/250000000000 : ℝ) (24945062307/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8483/65536 : ℝ))) 2 (505823763497/1000000000000 : ℝ) (31613985219/62500000000 : ℝ) (124725311533/250000000000 : ℝ) (24945062307/50000000000 : ℝ) (251181252407/500000000000 : ℝ) (251181252411/500000000000 : ℝ) (251175290351/500000000000 : ℝ) (50235058071/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8483/65536 : ℝ))) 3 (251181252407/500000000000 : ℝ) (251181252411/500000000000 : ℝ) (251175290351/500000000000 : ℝ) (50235058071/100000000000 : ℝ) (251178271379/500000000000 : ℝ) (251178271383/500000000000 : ℝ) (251178271361/500000000000 : ℝ) (502356542731/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8483/65536 : ℝ))) 4 (251178271379/500000000000 : ℝ) (251178271383/500000000000 : ℝ) (251178271361/500000000000 : ℝ) (502356542731/1000000000000 : ℝ) (25117827137/50000000000 : ℝ) (502356542749/1000000000000 : ℝ) (502356542739/1000000000000 : ℝ) (502356542749/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8483/65536 : ℝ))) 5 (25117827137/50000000000 : ℝ) (502356542749/1000000000000 : ℝ) (502356542739/1000000000000 : ℝ) (502356542749/1000000000000 : ℝ) (502356542739/1000000000000 : ℝ) (502356542749/1000000000000 : ℝ) (502356542739/1000000000000 : ℝ) (502356542749/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8483/65536 : ℝ))) 6 (502356542739/1000000000000 : ℝ) (502356542749/1000000000000 : ℝ) (502356542739/1000000000000 : ℝ) (502356542749/1000000000000 : ℝ) (502356542739/1000000000000 : ℝ) (502356542749/1000000000000 : ℝ) (502356542739/1000000000000 : ℝ) (502356542749/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8483/65536 : ℝ))) 7 (502356542739/1000000000000 : ℝ) (502356542749/1000000000000 : ℝ) (502356542739/1000000000000 : ℝ) (502356542749/1000000000000 : ℝ) (502356542739/1000000000000 : ℝ) (502356542749/1000000000000 : ℝ) (502356542739/1000000000000 : ℝ) (502356542749/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8483/65536 : ℝ)) hmem 8 (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ) (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8483/65536 : ℝ))) hcmem 8 (502356542739/1000000000000 : ℝ) (502356542749/1000000000000 : ℝ) (502356542739/1000000000000 : ℝ) (502356542749/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8483/65536 : ℝ)) (991958847199/1000000000000 : ℝ) (495979423601/500000000000 : ℝ) (502356542739/1000000000000 : ℝ) (502356542749/1000000000000 : ℝ) (12429633143/15625000000 : ℝ) (795496521171/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1446_exp_lower
  have heNumeric : (102745342471/50000000000 : ℝ)/4 ≤ Real.exp (-21314042974347/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745342471/50000000000 : ℝ)/4 ≤ Real.exp ((16965/131072 : ℝ)-(795496521171/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16965/131072 : ℝ) (8483/65536 : ℝ) (795496521171/1000000000000 : ℝ) (102745342471/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1447; no trusted numerical premise.
theorem cover8_leaf1447_exp_radius : (997979420109748481/1000000000000000000 : ℝ) ≤ Real.exp ((-16967/1048576 : ℝ)/8) ∧ Real.exp ((-16967/1048576 : ℝ)/8) ≤ (498989710054874241/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16967/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1447_exp_lower : (920113753513507503/1000000000000000000 : ℝ) ≤ Real.exp ((-2131404069353/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131404069353/3200000000000 : ℝ)/8) ≤ (57507109594594219/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131404069353/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1447_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726748971/250000000000 : ℝ) ≤ 4*Real.exp (8483/65536 : ℝ)*Real.exp (-mu (radius 8 (16967/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513726748971/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16967/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1447_exp_radius
  have hrNumeric : (983949216877/1000000000000 : ℝ) ≤ Real.exp (-16967/1048576 : ℝ) ∧ Real.exp (-16967/1048576 : ℝ) ≤ (491974608439/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983949216877/1000000000000 : ℝ) ≤ (radius 8 (16967/131072 : ℝ)) ∧ (radius 8 (16967/131072 : ℝ)) ≤ (491974608439/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16967/131072 : ℝ)) (983949216877/1000000000000 : ℝ) (491974608439/500000000000 : ℝ) (35689740041/200000000000 : ℝ) (44612175053/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16967/131072 : ℝ)) (983949216877/1000000000000 : ℝ) (491974608439/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16967/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983949216877/1000000000000 : ℝ) (491974608439/500000000000 : ℝ) (495987304219/500000000000 : ℝ) (991974608439/1000000000000 : ℝ) (247985535979/250000000000 : ℝ) (991942143917/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16967/131072 : ℝ)) 1 (495987304219/500000000000 : ℝ) (991974608439/1000000000000 : ℝ) (247985535979/250000000000 : ℝ) (991942143917/1000000000000 : ℝ) (991958376177/1000000000000 : ℝ) (495979188089/500000000000 : ℝ) (247989594011/250000000000 : ℝ) (495979188023/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16967/131072 : ℝ)) 2 (991958376177/1000000000000 : ℝ) (495979188089/500000000000 : ℝ) (247989594011/250000000000 : ℝ) (495979188023/500000000000 : ℝ) (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ) (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16967/131072 : ℝ)) 3 (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ) (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ) (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ) (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16967/131072 : ℝ)) 4 (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ) (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ) (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ) (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16967/131072 : ℝ)) 5 (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ) (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ) (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ) (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16967/131072 : ℝ)) 6 (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ) (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ) (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ) (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16967/131072 : ℝ)) 7 (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ) (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ) (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ) (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16967/131072 : ℝ))) (35689740041/200000000000 : ℝ) (44612175053/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16967/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35689740041/200000000000 : ℝ) (44612175053/250000000000 : ℝ) (294612175051/500000000000 : ℝ) (294612175053/500000000000 : ℝ) (422431888243/1000000000000 : ℝ) (105607972063/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16967/131072 : ℝ))) 1 (294612175051/500000000000 : ℝ) (294612175053/500000000000 : ℝ) (422431888243/1000000000000 : ℝ) (105607972063/250000000000 : ℝ) (126457029793/250000000000 : ℝ) (505828119179/1000000000000 : ℝ) (124726489471/250000000000 : ℝ) (124726489473/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16967/131072 : ℝ))) 2 (126457029793/250000000000 : ℝ) (505828119179/1000000000000 : ℝ) (124726489471/250000000000 : ℝ) (124726489473/250000000000 : ℝ) (7849484977/15625000000 : ℝ) (62795879817/125000000000 : ℝ) (502355115749/1000000000000 : ℝ) (251177557879/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16967/131072 : ℝ))) 3 (7849484977/15625000000 : ℝ) (62795879817/125000000000 : ℝ) (502355115749/1000000000000 : ℝ) (251177557879/500000000000 : ℝ) (251180538569/500000000000 : ℝ) (502361077147/1000000000000 : ℝ) (502361077103/1000000000000 : ℝ) (62795134639/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16967/131072 : ℝ))) 4 (251180538569/500000000000 : ℝ) (502361077147/1000000000000 : ℝ) (502361077103/1000000000000 : ℝ) (62795134639/125000000000 : ℝ) (784939183/1562500000 : ℝ) (50236107713/100000000000 : ℝ) (784939183/1562500000 : ℝ) (50236107713/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16967/131072 : ℝ))) 5 (784939183/1562500000 : ℝ) (50236107713/100000000000 : ℝ) (784939183/1562500000 : ℝ) (50236107713/100000000000 : ℝ) (784939183/1562500000 : ℝ) (50236107713/100000000000 : ℝ) (784939183/1562500000 : ℝ) (50236107713/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16967/131072 : ℝ))) 6 (784939183/1562500000 : ℝ) (50236107713/100000000000 : ℝ) (784939183/1562500000 : ℝ) (50236107713/100000000000 : ℝ) (784939183/1562500000 : ℝ) (50236107713/100000000000 : ℝ) (784939183/1562500000 : ℝ) (50236107713/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16967/131072 : ℝ))) 7 (784939183/1562500000 : ℝ) (50236107713/100000000000 : ℝ) (784939183/1562500000 : ℝ) (50236107713/100000000000 : ℝ) (784939183/1562500000 : ℝ) (50236107713/100000000000 : ℝ) (784939183/1562500000 : ℝ) (50236107713/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16967/131072 : ℝ)) hmem 8 (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ) (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16967/131072 : ℝ))) hcmem 8 (784939183/1562500000 : ℝ) (50236107713/100000000000 : ℝ) (784939183/1562500000 : ℝ) (50236107713/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16967/131072 : ℝ)) (99195837611/100000000000 : ℝ) (61997398507/62500000000 : ℝ) (784939183/1562500000 : ℝ) (50236107713/100000000000 : ℝ) (795504079271/1000000000000 : ℝ) (79550407929/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1447_exp_lower
  have heNumeric : (513726748971/250000000000 : ℝ)/4 ≤ Real.exp (-2131404069353/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726748971/250000000000 : ℝ)/4 ≤ Real.exp ((8483/65536 : ℝ)-(79550407929/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8483/65536 : ℝ) (16967/131072 : ℝ) (79550407929/100000000000 : ℝ) (513726748971/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1448; no trusted numerical premise.
theorem cover8_leaf1448_exp_radius : (498989650570668957/500000000000000000 : ℝ) ≤ Real.exp ((-2121/131072 : ℝ)/8) ∧ Real.exp ((-2121/131072 : ℝ)/8) ≤ (199595860228267583/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2121/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1448_exp_lower : (920113761745136309/1000000000000000000 : ℝ) ≤ Real.exp ((-21314038403273/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314038403273/32000000000000 : ℝ)/8) ≤ (92011376174513631/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314038403273/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1448_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410981428591/200000000000 : ℝ) ≤ 4*Real.exp (16967/131072 : ℝ)*Real.exp (-mu (radius 8 (2121/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (410981428591/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2121/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1448_exp_radius
  have hrNumeric : (98394827851/100000000000 : ℝ) ≤ Real.exp (-2121/131072 : ℝ) ∧ Real.exp (-2121/131072 : ℝ) ≤ (983948278511/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98394827851/100000000000 : ℝ) ≤ (radius 8 (2121/16384 : ℝ)) ∧ (radius 8 (2121/16384 : ℝ)) ≤ (983948278511/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2121/16384 : ℝ)) (98394827851/100000000000 : ℝ) (983948278511/1000000000000 : ℝ) (35690774839/200000000000 : ℝ) (178453874201/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2121/16384 : ℝ)) (98394827851/100000000000 : ℝ) (983948278511/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2121/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98394827851/100000000000 : ℝ) (983948278511/1000000000000 : ℝ) (198394827851/200000000000 : ℝ) (123996767407/125000000000 : ℝ) (991941670921/1000000000000 : ℝ) (495970835461/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2121/16384 : ℝ)) 1 (198394827851/200000000000 : ℝ) (123996767407/125000000000 : ℝ) (991941670921/1000000000000 : ℝ) (495970835461/500000000000 : ℝ) (15499342267/15625000000 : ℝ) (991957905089/1000000000000 : ℝ) (198391580991/200000000000 : ℝ) (991957904957/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2121/16384 : ℝ)) 2 (15499342267/15625000000 : ℝ) (991957905089/1000000000000 : ℝ) (198391580991/200000000000 : ℝ) (991957904957/1000000000000 : ℝ) (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ) (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2121/16384 : ℝ)) 3 (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ) (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ) (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ) (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2121/16384 : ℝ)) 4 (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ) (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ) (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ) (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2121/16384 : ℝ)) 5 (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ) (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ) (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ) (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2121/16384 : ℝ)) 6 (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ) (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ) (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ) (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2121/16384 : ℝ)) 7 (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ) (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ) (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ) (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2121/16384 : ℝ))) (35690774839/200000000000 : ℝ) (178453874201/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2121/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35690774839/200000000000 : ℝ) (178453874201/1000000000000 : ℝ) (589226937097/1000000000000 : ℝ) (589226937101/1000000000000 : ℝ) (422438012251/1000000000000 : ℝ) (422438012259/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2121/16384 : ℝ))) 1 (589226937097/1000000000000 : ℝ) (589226937101/1000000000000 : ℝ) (422438012251/1000000000000 : ℝ) (422438012259/1000000000000 : ℝ) (252916237337/500000000000 : ℝ) (12645811867/25000000000 : ℝ) (49891066943/100000000000 : ℝ) (249455334719/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2121/16384 : ℝ))) 2 (252916237337/500000000000 : ℝ) (12645811867/25000000000 : ℝ) (49891066943/100000000000 : ℝ) (249455334719/500000000000 : ℝ) (125592893013/250000000000 : ℝ) (502371572059/1000000000000 : ℝ) (31397478163/62500000000 : ℝ) (62794956327/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2121/16384 : ℝ))) 3 (125592893013/250000000000 : ℝ) (502371572059/1000000000000 : ℝ) (31397478163/62500000000 : ℝ) (62794956327/125000000000 : ℝ) (50236561133/100000000000 : ℝ) (251182805669/500000000000 : ℝ) (251182805647/500000000000 : ℝ) (502365611303/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2121/16384 : ℝ))) 4 (50236561133/100000000000 : ℝ) (251182805669/500000000000 : ℝ) (251182805647/500000000000 : ℝ) (502365611303/1000000000000 : ℝ) (31397850707/62500000000 : ℝ) (502365611321/1000000000000 : ℝ) (502365611311/1000000000000 : ℝ) (502365611321/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2121/16384 : ℝ))) 5 (31397850707/62500000000 : ℝ) (502365611321/1000000000000 : ℝ) (502365611311/1000000000000 : ℝ) (502365611321/1000000000000 : ℝ) (502365611311/1000000000000 : ℝ) (502365611321/1000000000000 : ℝ) (502365611311/1000000000000 : ℝ) (502365611321/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2121/16384 : ℝ))) 6 (502365611311/1000000000000 : ℝ) (502365611321/1000000000000 : ℝ) (502365611311/1000000000000 : ℝ) (502365611321/1000000000000 : ℝ) (502365611311/1000000000000 : ℝ) (502365611321/1000000000000 : ℝ) (502365611311/1000000000000 : ℝ) (502365611321/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2121/16384 : ℝ))) 7 (502365611311/1000000000000 : ℝ) (502365611321/1000000000000 : ℝ) (502365611311/1000000000000 : ℝ) (502365611321/1000000000000 : ℝ) (502365611311/1000000000000 : ℝ) (502365611321/1000000000000 : ℝ) (502365611311/1000000000000 : ℝ) (502365611321/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2121/16384 : ℝ)) hmem 8 (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ) (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2121/16384 : ℝ))) hcmem 8 (502365611311/1000000000000 : ℝ) (502365611321/1000000000000 : ℝ) (502365611311/1000000000000 : ℝ) (502365611321/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2121/16384 : ℝ)) (991957905021/1000000000000 : ℝ) (991957905023/1000000000000 : ℝ) (502365611311/1000000000000 : ℝ) (502365611321/1000000000000 : ℝ) (99438954637/125000000000 : ℝ) (397755818557/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1448_exp_lower
  have heNumeric : (410981428591/200000000000 : ℝ)/4 ≤ Real.exp (-21314038403273/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410981428591/200000000000 : ℝ)/4 ≤ Real.exp ((16967/131072 : ℝ)-(397755818557/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16967/131072 : ℝ) (2121/16384 : ℝ) (397755818557/500000000000 : ℝ) (410981428591/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1449; no trusted numerical premise.
theorem cover8_leaf1449_exp_radius : (99797918217294153/100000000000000000 : ℝ) ≤ Real.exp ((-16969/1048576 : ℝ)/8) ∧ Real.exp ((-16969/1048576 : ℝ)/8) ≤ (997979182172941531/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16969/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1449_exp_lower : (920113770011499483/1000000000000000000 : ℝ) ≤ Real.exp ((-2664254512919/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664254512919/4000000000000 : ℝ)/8) ≤ (230028442502874871/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664254512919/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1449_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907290647/1000000000000 : ℝ) ≤ 4*Real.exp (2121/16384 : ℝ)*Real.exp (-mu (radius 8 (16969/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907290647/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16969/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1449_exp_radius
  have hrNumeric : (61496708759/62500000000 : ℝ) ≤ Real.exp (-16969/1048576 : ℝ) ∧ Real.exp (-16969/1048576 : ℝ) ≤ (196789468029/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61496708759/62500000000 : ℝ) ≤ (radius 8 (16969/131072 : ℝ)) ∧ (radius 8 (16969/131072 : ℝ)) ≤ (196789468029/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16969/131072 : ℝ)) (61496708759/62500000000 : ℝ) (196789468029/200000000000 : ℝ) (178459048023/1000000000000 : ℝ) (17845904803/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16969/131072 : ℝ)) (61496708759/62500000000 : ℝ) (196789468029/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16969/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61496708759/62500000000 : ℝ) (196789468029/200000000000 : ℝ) (123996708759/125000000000 : ℝ) (991973670073/1000000000000 : ℝ) (495970598963/500000000000 : ℝ) (123992649741/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16969/131072 : ℝ)) 1 (123996708759/125000000000 : ℝ) (991973670073/1000000000000 : ℝ) (495970598963/500000000000 : ℝ) (123992649741/125000000000 : ℝ) (991957433999/1000000000000 : ℝ) (991957434001/1000000000000 : ℝ) (495978716933/500000000000 : ℝ) (247989358467/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16969/131072 : ℝ)) 2 (991957433999/1000000000000 : ℝ) (991957434001/1000000000000 : ℝ) (495978716933/500000000000 : ℝ) (247989358467/250000000000 : ℝ) (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ) (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16969/131072 : ℝ)) 3 (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ) (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ) (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ) (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16969/131072 : ℝ)) 4 (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ) (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ) (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ) (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16969/131072 : ℝ)) 5 (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ) (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ) (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ) (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16969/131072 : ℝ)) 6 (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ) (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ) (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ) (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16969/131072 : ℝ)) 7 (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ) (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ) (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ) (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16969/131072 : ℝ))) (178459048023/1000000000000 : ℝ) (17845904803/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16969/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178459048023/1000000000000 : ℝ) (17845904803/100000000000 : ℝ) (589229524011/1000000000000 : ℝ) (117845904803/200000000000 : ℝ) (211222067989/500000000000 : ℝ) (105611033997/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16969/131072 : ℝ))) 1 (589229524011/1000000000000 : ℝ) (117845904803/200000000000 : ℝ) (211222067989/500000000000 : ℝ) (105611033997/250000000000 : ℝ) (252918414997/500000000000 : ℝ) (252918415001/500000000000 : ℝ) (124728845191/250000000000 : ℝ) (498915380773/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16969/131072 : ℝ))) 2 (252918414997/500000000000 : ℝ) (252918415001/500000000000 : ℝ) (124728845191/250000000000 : ℝ) (498915380773/1000000000000 : ℝ) (502376105379/1000000000000 : ℝ) (125594026347/250000000000 : ℝ) (125591046317/250000000000 : ℝ) (251182092639/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16969/131072 : ℝ))) 3 (502376105379/1000000000000 : ℝ) (125594026347/250000000000 : ℝ) (125591046317/250000000000 : ℝ) (251182092639/500000000000 : ℝ) (502370145323/1000000000000 : ℝ) (502370145333/1000000000000 : ℝ) (62796268161/125000000000 : ℝ) (251185072649/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16969/131072 : ℝ))) 4 (502370145323/1000000000000 : ℝ) (502370145333/1000000000000 : ℝ) (62796268161/125000000000 : ℝ) (251185072649/500000000000 : ℝ) (100474029061/200000000000 : ℝ) (125592536329/250000000000 : ℝ) (100474029061/200000000000 : ℝ) (125592536329/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16969/131072 : ℝ))) 5 (100474029061/200000000000 : ℝ) (125592536329/250000000000 : ℝ) (100474029061/200000000000 : ℝ) (125592536329/250000000000 : ℝ) (100474029061/200000000000 : ℝ) (125592536329/250000000000 : ℝ) (100474029061/200000000000 : ℝ) (125592536329/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16969/131072 : ℝ))) 6 (100474029061/200000000000 : ℝ) (125592536329/250000000000 : ℝ) (100474029061/200000000000 : ℝ) (125592536329/250000000000 : ℝ) (100474029061/200000000000 : ℝ) (125592536329/250000000000 : ℝ) (100474029061/200000000000 : ℝ) (125592536329/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16969/131072 : ℝ))) 7 (100474029061/200000000000 : ℝ) (125592536329/250000000000 : ℝ) (100474029061/200000000000 : ℝ) (125592536329/250000000000 : ℝ) (100474029061/200000000000 : ℝ) (125592536329/250000000000 : ℝ) (100474029061/200000000000 : ℝ) (125592536329/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16969/131072 : ℝ)) hmem 8 (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ) (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16969/131072 : ℝ))) hcmem 8 (100474029061/200000000000 : ℝ) (125592536329/250000000000 : ℝ) (100474029061/200000000000 : ℝ) (125592536329/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16969/131072 : ℝ)) (247989358483/250000000000 : ℝ) (198391486787/200000000000 : ℝ) (100474029061/200000000000 : ℝ) (125592536329/250000000000 : ℝ) (159103838923/200000000000 : ℝ) (198879798659/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1449_exp_lower
  have heNumeric : (2054907290647/1000000000000 : ℝ)/4 ≤ Real.exp (-2664254512919/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907290647/1000000000000 : ℝ)/4 ≤ Real.exp ((2121/16384 : ℝ)-(198879798659/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2121/16384 : ℝ) (16969/131072 : ℝ) (198879798659/250000000000 : ℝ) (2054907290647/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1425_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1425_certificate
#check SmaleRate.Proofs.cover8_leaf1426_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1426_certificate
#check SmaleRate.Proofs.cover8_leaf1427_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1427_certificate
#check SmaleRate.Proofs.cover8_leaf1428_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1428_certificate
#check SmaleRate.Proofs.cover8_leaf1429_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1429_certificate
#check SmaleRate.Proofs.cover8_leaf1430_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1430_certificate
#check SmaleRate.Proofs.cover8_leaf1431_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1431_certificate
#check SmaleRate.Proofs.cover8_leaf1432_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1432_certificate
#check SmaleRate.Proofs.cover8_leaf1433_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1433_certificate
#check SmaleRate.Proofs.cover8_leaf1434_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1434_certificate
#check SmaleRate.Proofs.cover8_leaf1435_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1435_certificate
#check SmaleRate.Proofs.cover8_leaf1436_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1436_certificate
#check SmaleRate.Proofs.cover8_leaf1437_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1437_certificate
#check SmaleRate.Proofs.cover8_leaf1438_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1438_certificate
#check SmaleRate.Proofs.cover8_leaf1439_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1439_certificate
#check SmaleRate.Proofs.cover8_leaf1440_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1440_certificate
#check SmaleRate.Proofs.cover8_leaf1441_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1441_certificate
#check SmaleRate.Proofs.cover8_leaf1442_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1442_certificate
#check SmaleRate.Proofs.cover8_leaf1443_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1443_certificate
#check SmaleRate.Proofs.cover8_leaf1444_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1444_certificate
#check SmaleRate.Proofs.cover8_leaf1445_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1445_certificate
#check SmaleRate.Proofs.cover8_leaf1446_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1446_certificate
#check SmaleRate.Proofs.cover8_leaf1447_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1447_certificate
#check SmaleRate.Proofs.cover8_leaf1448_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1448_certificate
#check SmaleRate.Proofs.cover8_leaf1449_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1449_certificate
