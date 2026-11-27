/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0475; no trusted numerical premise.
theorem cover7_leaf0475_exp_radius : (498760400149018611/500000000000000000 : ℝ) ≤ Real.exp ((-4555/229376 : ℝ)/8) ∧ Real.exp ((-4555/229376 : ℝ)/8) ≤ (997520800298037223/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4555/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0475_exp_lower : (459044718008638169/500000000000000000 : ℝ) ≤ Real.exp ((-546946996811/800000000000 : ℝ)/8) ∧ Real.exp ((-546946996811/800000000000 : ℝ)/8) ≤ (918089436017276339/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-546946996811/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0475_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019016708859/1000000000000 : ℝ) ≤ 4*Real.exp (2277/16384 : ℝ)*Real.exp (-mu (radius 7 (4555/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019016708859/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4555/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0475_exp_radius
  have hrNumeric : (196067530351/200000000000 : ℝ) ≤ Real.exp (-4555/229376 : ℝ) ∧ Real.exp (-4555/229376 : ℝ) ≤ (245084412939/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196067530351/200000000000 : ℝ) ≤ (radius 7 (4555/32768 : ℝ)) ∧ (radius 7 (4555/32768 : ℝ)) ≤ (245084412939/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4555/32768 : ℝ)) (196067530351/200000000000 : ℝ) (245084412939/250000000000 : ℝ) (98663681957/500000000000 : ℝ) (2466592049/12500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4555/32768 : ℝ)) (196067530351/200000000000 : ℝ) (245084412939/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4555/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196067530351/200000000000 : ℝ) (245084412939/250000000000 : ℝ) (990168825877/1000000000000 : ℝ) (495084412939/500000000000 : ℝ) (990120018863/1000000000000 : ℝ) (198024003773/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4555/32768 : ℝ)) 1 (990168825877/1000000000000 : ℝ) (495084412939/500000000000 : ℝ) (990120018863/1000000000000 : ℝ) (198024003773/200000000000 : ℝ) (99014442237/100000000000 : ℝ) (247536105593/250000000000 : ℝ) (990144422069/1000000000000 : ℝ) (990144422071/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4555/32768 : ℝ)) 2 (99014442237/100000000000 : ℝ) (247536105593/250000000000 : ℝ) (990144422069/1000000000000 : ℝ) (990144422071/1000000000000 : ℝ) (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ) (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4555/32768 : ℝ)) 3 (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ) (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ) (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ) (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4555/32768 : ℝ)) 4 (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ) (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ) (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ) (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4555/32768 : ℝ)) 5 (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ) (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ) (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ) (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4555/32768 : ℝ)) 6 (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ) (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ) (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ) (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4555/32768 : ℝ)) 7 (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ) (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ) (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ) (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4555/32768 : ℝ))) (98663681957/500000000000 : ℝ) (2466592049/12500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4555/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98663681957/500000000000 : ℝ) (2466592049/12500000000 : ℝ) (598663681957/1000000000000 : ℝ) (14966592049/25000000000 : ℝ) (44421544763/100000000000 : ℝ) (222107723819/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4555/32768 : ℝ))) 1 (598663681957/1000000000000 : ℝ) (14966592049/25000000000 : ℝ) (44421544763/100000000000 : ℝ) (222107723819/500000000000 : ℝ) (521439564793/1000000000000 : ℝ) (521439564799/1000000000000 : ℝ) (644611869/1250000000 : ℝ) (515689495207/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4555/32768 : ℝ))) 2 (521439564793/1000000000000 : ℝ) (521439564799/1000000000000 : ℝ) (644611869/1250000000 : ℝ) (515689495207/1000000000000 : ℝ) (129641132499/250000000000 : ℝ) (518564530003/1000000000000 : ℝ) (20742262401/40000000000 : ℝ) (16204892501/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4555/32768 : ℝ))) 3 (129641132499/250000000000 : ℝ) (518564530003/1000000000000 : ℝ) (20742262401/40000000000 : ℝ) (16204892501/31250000000 : ℝ) (51856054501/100000000000 : ℝ) (259280272509/500000000000 : ℝ) (103712108999/200000000000 : ℝ) (518560545003/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4555/32768 : ℝ))) 4 (51856054501/100000000000 : ℝ) (259280272509/500000000000 : ℝ) (103712108999/200000000000 : ℝ) (518560545003/1000000000000 : ℝ) (259280272501/500000000000 : ℝ) (518560545011/1000000000000 : ℝ) (259280272501/500000000000 : ℝ) (518560545011/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4555/32768 : ℝ))) 5 (259280272501/500000000000 : ℝ) (518560545011/1000000000000 : ℝ) (259280272501/500000000000 : ℝ) (518560545011/1000000000000 : ℝ) (259280272501/500000000000 : ℝ) (518560545011/1000000000000 : ℝ) (259280272501/500000000000 : ℝ) (518560545011/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4555/32768 : ℝ))) 6 (259280272501/500000000000 : ℝ) (518560545011/1000000000000 : ℝ) (259280272501/500000000000 : ℝ) (518560545011/1000000000000 : ℝ) (259280272501/500000000000 : ℝ) (518560545011/1000000000000 : ℝ) (259280272501/500000000000 : ℝ) (518560545011/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4555/32768 : ℝ))) 7 (259280272501/500000000000 : ℝ) (518560545011/1000000000000 : ℝ) (259280272501/500000000000 : ℝ) (518560545011/1000000000000 : ℝ) (259280272501/500000000000 : ℝ) (518560545011/1000000000000 : ℝ) (259280272501/500000000000 : ℝ) (518560545011/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4555/32768 : ℝ)) hmem 8 (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ) (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4555/32768 : ℝ))) hcmem 8 (259280272501/500000000000 : ℝ) (518560545011/1000000000000 : ℝ) (259280272501/500000000000 : ℝ) (518560545011/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4555/32768 : ℝ)) (990144422219/1000000000000 : ℝ) (495072211111/500000000000 : ℝ) (259280272501/500000000000 : ℝ) (518560545011/1000000000000 : ℝ) (822660796777/1000000000000 : ℝ) (164532159359/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0475_exp_lower
  have heNumeric : (2019016708859/1000000000000 : ℝ)/4 ≤ Real.exp (-546946996811/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019016708859/1000000000000 : ℝ)/4 ≤ Real.exp ((2277/16384 : ℝ)-(164532159359/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2277/16384 : ℝ) (4555/32768 : ℝ) (164532159359/200000000000 : ℝ) (2019016708859/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0476; no trusted numerical premise.
theorem cover7_leaf0476_exp_radius : (1948281751352519/1953125000000000 : ℝ) ≤ Real.exp ((-1139/57344 : ℝ)/8) ∧ Real.exp ((-1139/57344 : ℝ)/8) ≤ (997520256692489729/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1139/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0476_exp_lower : (91808948331771869/100000000000000000 : ℝ) ≤ Real.exp ((-5469466670797/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469466670797/8000000000000 : ℝ)/8) ≤ (918089483317718691/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469466670797/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0476_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009508770513/500000000000 : ℝ) ≤ 4*Real.exp (4555/32768 : ℝ)*Real.exp (-mu (radius 7 (1139/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (1009508770513/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1139/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0476_exp_radius
  have hrNumeric : (980333377831/1000000000000 : ℝ) ≤ Real.exp (-1139/57344 : ℝ) ∧ Real.exp (-1139/57344 : ℝ) ≤ (122541672229/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980333377831/1000000000000 : ℝ) ≤ (radius 7 (1139/8192 : ℝ)) ∧ (radius 7 (1139/8192 : ℝ)) ≤ (122541672229/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1139/8192 : ℝ)) (980333377831/1000000000000 : ℝ) (122541672229/125000000000 : ℝ) (24668574489/125000000000 : ℝ) (98674297959/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1139/8192 : ℝ)) (980333377831/1000000000000 : ℝ) (122541672229/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1139/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980333377831/1000000000000 : ℝ) (122541672229/125000000000 : ℝ) (198033337783/200000000000 : ℝ) (247541672229/250000000000 : ℝ) (39604714423/40000000000 : ℝ) (990117860577/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1139/8192 : ℝ)) 1 (198033337783/200000000000 : ℝ) (247541672229/250000000000 : ℝ) (39604714423/40000000000 : ℝ) (990117860577/1000000000000 : ℝ) (198028454949/200000000000 : ℝ) (990142274747/1000000000000 : ℝ) (247535568611/250000000000 : ℝ) (495071137223/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1139/8192 : ℝ)) 2 (198028454949/200000000000 : ℝ) (990142274747/1000000000000 : ℝ) (247535568611/250000000000 : ℝ) (495071137223/500000000000 : ℝ) (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ) (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1139/8192 : ℝ)) 3 (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ) (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ) (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ) (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1139/8192 : ℝ)) 4 (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ) (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ) (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ) (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1139/8192 : ℝ)) 5 (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ) (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ) (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ) (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1139/8192 : ℝ)) 6 (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ) (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ) (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ) (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1139/8192 : ℝ)) 7 (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ) (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ) (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ) (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1139/8192 : ℝ))) (24668574489/125000000000 : ℝ) (98674297959/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1139/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24668574489/125000000000 : ℝ) (98674297959/500000000000 : ℝ) (149668574489/250000000000 : ℝ) (598674297959/1000000000000 : ℝ) (444239345299/1000000000000 : ℝ) (444239345307/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1139/8192 : ℝ))) 1 (149668574489/250000000000 : ℝ) (598674297959/1000000000000 : ℝ) (444239345299/1000000000000 : ℝ) (444239345307/1000000000000 : ℝ) (521456821627/1000000000000 : ℝ) (521456821633/1000000000000 : ℝ) (515707938829/1000000000000 : ℝ) (103141587767/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1139/8192 : ℝ))) 2 (521456821627/1000000000000 : ℝ) (521456821633/1000000000000 : ℝ) (515707938829/1000000000000 : ℝ) (103141587767/200000000000 : ℝ) (129645595057/250000000000 : ℝ) (259291190117/500000000000 : ℝ) (25928720691/50000000000 : ℝ) (518574413827/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1139/8192 : ℝ))) 3 (129645595057/250000000000 : ℝ) (259291190117/500000000000 : ℝ) (25928720691/50000000000 : ℝ) (518574413827/1000000000000 : ℝ) (16205574907/31250000000 : ℝ) (518578397031/1000000000000 : ℝ) (32411149813/62500000000 : ℝ) (64822299627/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1139/8192 : ℝ))) 4 (16205574907/31250000000 : ℝ) (518578397031/1000000000000 : ℝ) (32411149813/62500000000 : ℝ) (64822299627/125000000000 : ℝ) (64822299627/125000000000 : ℝ) (16205574907/31250000000 : ℝ) (103715679403/200000000000 : ℝ) (16205574907/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1139/8192 : ℝ))) 5 (64822299627/125000000000 : ℝ) (16205574907/31250000000 : ℝ) (103715679403/200000000000 : ℝ) (16205574907/31250000000 : ℝ) (103715679403/200000000000 : ℝ) (16205574907/31250000000 : ℝ) (103715679403/200000000000 : ℝ) (16205574907/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1139/8192 : ℝ))) 6 (103715679403/200000000000 : ℝ) (16205574907/31250000000 : ℝ) (103715679403/200000000000 : ℝ) (16205574907/31250000000 : ℝ) (103715679403/200000000000 : ℝ) (16205574907/31250000000 : ℝ) (103715679403/200000000000 : ℝ) (16205574907/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1139/8192 : ℝ))) 7 (103715679403/200000000000 : ℝ) (16205574907/31250000000 : ℝ) (103715679403/200000000000 : ℝ) (16205574907/31250000000 : ℝ) (103715679403/200000000000 : ℝ) (16205574907/31250000000 : ℝ) (103715679403/200000000000 : ℝ) (16205574907/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1139/8192 : ℝ)) hmem 8 (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ) (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1139/8192 : ℝ))) hcmem 8 (103715679403/200000000000 : ℝ) (16205574907/31250000000 : ℝ) (103715679403/200000000000 : ℝ) (16205574907/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1139/8192 : ℝ)) (495071137297/500000000000 : ℝ) (990142274597/1000000000000 : ℝ) (103715679403/200000000000 : ℝ) (16205574907/31250000000 : ℝ) (822690902191/1000000000000 : ℝ) (822690902209/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0476_exp_lower
  have heNumeric : (1009508770513/500000000000 : ℝ)/4 ≤ Real.exp (-5469466670797/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009508770513/500000000000 : ℝ)/4 ≤ Real.exp ((4555/32768 : ℝ)-(822690902209/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4555/32768 : ℝ) (1139/8192 : ℝ) (822690902209/1000000000000 : ℝ) (1009508770513/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0477; no trusted numerical premise.
theorem cover7_leaf0477_exp_radius : (249379928271809619/250000000000000000 : ℝ) ≤ Real.exp ((-651/32768 : ℝ)/8) ∧ Real.exp ((-651/32768 : ℝ)/8) ≤ (997519713087238477/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-651/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0477_exp_lower : (918089531123916049/1000000000000000000 : ℝ) ≤ Real.exp ((-1367365834557/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367365834557/2000000000000 : ℝ)/8) ≤ (18361790622478321/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367365834557/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0477_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201901838209/100000000000 : ℝ) ≤ 4*Real.exp (1139/8192 : ℝ)*Real.exp (-mu (radius 7 (4557/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (201901838209/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4557/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0477_exp_radius
  have hrNumeric : (490164551963/500000000000 : ℝ) ≤ Real.exp (-651/32768 : ℝ) ∧ Real.exp (-651/32768 : ℝ) ≤ (980329103927/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490164551963/500000000000 : ℝ) ≤ (radius 7 (4557/32768 : ℝ)) ∧ (radius 7 (4557/32768 : ℝ)) ≤ (980329103927/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4557/32768 : ℝ)) (490164551963/500000000000 : ℝ) (980329103927/1000000000000 : ℝ) (98684912719/500000000000 : ℝ) (49342456361/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4557/32768 : ℝ)) (490164551963/500000000000 : ℝ) (980329103927/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4557/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490164551963/500000000000 : ℝ) (980329103927/1000000000000 : ℝ) (990164551963/1000000000000 : ℝ) (247541137991/250000000000 : ℝ) (247528925573/250000000000 : ℝ) (990115702293/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4557/32768 : ℝ)) 1 (990164551963/1000000000000 : ℝ) (247541137991/250000000000 : ℝ) (247528925573/250000000000 : ℝ) (990115702293/1000000000000 : ℝ) (990140127127/1000000000000 : ℝ) (990140127129/1000000000000 : ℝ) (495070063413/500000000000 : ℝ) (247535031707/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4557/32768 : ℝ)) 2 (990140127127/1000000000000 : ℝ) (990140127129/1000000000000 : ℝ) (495070063413/500000000000 : ℝ) (247535031707/250000000000 : ℝ) (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ) (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4557/32768 : ℝ)) 3 (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ) (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ) (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ) (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4557/32768 : ℝ)) 4 (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ) (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ) (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ) (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4557/32768 : ℝ)) 5 (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ) (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ) (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ) (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4557/32768 : ℝ)) 6 (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ) (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ) (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ) (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4557/32768 : ℝ)) 7 (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ) (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ) (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ) (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4557/32768 : ℝ))) (98684912719/500000000000 : ℝ) (49342456361/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4557/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98684912719/500000000000 : ℝ) (49342456361/250000000000 : ℝ) (598684912719/1000000000000 : ℝ) (299342456361/500000000000 : ℝ) (4442632389/10000000000 : ℝ) (444263238907/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4557/32768 : ℝ))) 1 (598684912719/1000000000000 : ℝ) (299342456361/500000000000 : ℝ) (4442632389/10000000000 : ℝ) (444263238907/1000000000000 : ℝ) (521474075809/1000000000000 : ℝ) (104294815163/200000000000 : ℝ) (128931594849/250000000000 : ℝ) (257863189701/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4557/32768 : ℝ))) 2 (521474075809/1000000000000 : ℝ) (104294815163/200000000000 : ℝ) (128931594849/250000000000 : ℝ) (257863189701/500000000000 : ℝ) (259300113801/500000000000 : ℝ) (518600227609/1000000000000 : ℝ) (518592264757/1000000000000 : ℝ) (129648066191/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4557/32768 : ℝ))) 3 (259300113801/500000000000 : ℝ) (518600227609/1000000000000 : ℝ) (518592264757/1000000000000 : ℝ) (129648066191/250000000000 : ℝ) (518596246179/1000000000000 : ℝ) (518596246187/1000000000000 : ℝ) (129649061541/250000000000 : ℝ) (129649061543/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4557/32768 : ℝ))) 4 (518596246179/1000000000000 : ℝ) (518596246187/1000000000000 : ℝ) (129649061541/250000000000 : ℝ) (129649061543/250000000000 : ℝ) (518596246171/1000000000000 : ℝ) (25929812309/50000000000 : ℝ) (518596246171/1000000000000 : ℝ) (25929812309/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4557/32768 : ℝ))) 5 (518596246171/1000000000000 : ℝ) (25929812309/50000000000 : ℝ) (518596246171/1000000000000 : ℝ) (25929812309/50000000000 : ℝ) (518596246171/1000000000000 : ℝ) (25929812309/50000000000 : ℝ) (518596246171/1000000000000 : ℝ) (25929812309/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4557/32768 : ℝ))) 6 (518596246171/1000000000000 : ℝ) (25929812309/50000000000 : ℝ) (518596246171/1000000000000 : ℝ) (25929812309/50000000000 : ℝ) (518596246171/1000000000000 : ℝ) (25929812309/50000000000 : ℝ) (518596246171/1000000000000 : ℝ) (25929812309/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4557/32768 : ℝ))) 7 (518596246171/1000000000000 : ℝ) (25929812309/50000000000 : ℝ) (518596246171/1000000000000 : ℝ) (25929812309/50000000000 : ℝ) (518596246171/1000000000000 : ℝ) (25929812309/50000000000 : ℝ) (518596246171/1000000000000 : ℝ) (25929812309/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4557/32768 : ℝ)) hmem 8 (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ) (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4557/32768 : ℝ))) hcmem 8 (518596246171/1000000000000 : ℝ) (25929812309/50000000000 : ℝ) (518596246171/1000000000000 : ℝ) (25929812309/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4557/32768 : ℝ)) (3867734871/3906250000 : ℝ) (990140126979/1000000000000 : ℝ) (518596246171/1000000000000 : ℝ) (25929812309/50000000000 : ℝ) (411360501599/500000000000 : ℝ) (51420062701/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0477_exp_lower
  have heNumeric : (201901838209/100000000000 : ℝ)/4 ≤ Real.exp (-1367365834557/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201901838209/100000000000 : ℝ)/4 ≤ Real.exp ((1139/8192 : ℝ)-(51420062701/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1139/8192 : ℝ) (4557/32768 : ℝ) (51420062701/62500000000 : ℝ) (201901838209/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0478; no trusted numerical premise.
theorem cover7_leaf0478_exp_radius : (199503833896456693/200000000000000000 : ℝ) ≤ Real.exp ((-2279/114688 : ℝ)/8) ∧ Real.exp ((-2279/114688 : ℝ)/8) ≤ (498759584741141733/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2279/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0478_exp_lower : (918089579436098017/1000000000000000000 : ℝ) ≤ Real.exp ((-5469459970387/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469459970387/8000000000000 : ℝ)/8) ≤ (459044789718049009/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469459970387/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0478_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019019232057/1000000000000 : ℝ) ≤ 4*Real.exp (4557/32768 : ℝ)*Real.exp (-mu (radius 7 (2279/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019019232057/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2279/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0478_exp_radius
  have hrNumeric : (24508120751/25000000000 : ℝ) ≤ Real.exp (-2279/114688 : ℝ) ∧ Real.exp (-2279/114688 : ℝ) ≤ (980324830041/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24508120751/25000000000 : ℝ) ≤ (radius 7 (2279/16384 : ℝ)) ∧ (radius 7 (2279/16384 : ℝ)) ≤ (980324830041/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2279/16384 : ℝ)) (24508120751/25000000000 : ℝ) (980324830041/1000000000000 : ℝ) (39478210499/200000000000 : ℝ) (78956421/400000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2279/16384 : ℝ)) (24508120751/25000000000 : ℝ) (980324830041/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2279/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24508120751/25000000000 : ℝ) (980324830041/1000000000000 : ℝ) (49508120751/50000000000 : ℝ) (990162415021/1000000000000 : ℝ) (495056772007/500000000000 : ℝ) (198022708803/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2279/16384 : ℝ)) 1 (49508120751/50000000000 : ℝ) (990162415021/1000000000000 : ℝ) (495056772007/500000000000 : ℝ) (198022708803/200000000000 : ℝ) (990137979517/1000000000000 : ℝ) (495068989759/500000000000 : ℝ) (198027595843/200000000000 : ℝ) (990137979217/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2279/16384 : ℝ)) 2 (990137979517/1000000000000 : ℝ) (495068989759/500000000000 : ℝ) (198027595843/200000000000 : ℝ) (990137979217/1000000000000 : ℝ) (495068989683/500000000000 : ℝ) (123767247421/125000000000 : ℝ) (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2279/16384 : ℝ)) 3 (495068989683/500000000000 : ℝ) (123767247421/125000000000 : ℝ) (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ) (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ) (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2279/16384 : ℝ)) 4 (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ) (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ) (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ) (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2279/16384 : ℝ)) 5 (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ) (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ) (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ) (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2279/16384 : ℝ)) 6 (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ) (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ) (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ) (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2279/16384 : ℝ)) 7 (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ) (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ) (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ) (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2279/16384 : ℝ))) (39478210499/200000000000 : ℝ) (78956421/400000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2279/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39478210499/200000000000 : ℝ) (78956421/400000000 : ℝ) (598695526247/1000000000000 : ℝ) (478956421/800000000 : ℝ) (444287128437/1000000000000 : ℝ) (444287128443/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2279/16384 : ℝ))) 1 (598695526247/1000000000000 : ℝ) (478956421/800000000 : ℝ) (444287128437/1000000000000 : ℝ) (444287128443/1000000000000 : ℝ) (260745663671/500000000000 : ℝ) (521491327347/1000000000000 : ℝ) (64468102113/125000000000 : ℝ) (51574481691/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2279/16384 : ℝ))) 2 (260745663671/500000000000 : ℝ) (521491327347/1000000000000 : ℝ) (64468102113/125000000000 : ℝ) (51574481691/100000000000 : ℝ) (518618072123/1000000000000 : ℝ) (518618072129/1000000000000 : ℝ) (518610112837/1000000000000 : ℝ) (518610112843/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2279/16384 : ℝ))) 3 (518618072123/1000000000000 : ℝ) (518618072129/1000000000000 : ℝ) (518610112837/1000000000000 : ℝ) (518610112843/1000000000000 : ℝ) (1620669039/3125000000 : ℝ) (259307046243/500000000000 : ℝ) (32413380779/62500000000 : ℝ) (518614092471/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2279/16384 : ℝ))) 4 (1620669039/3125000000 : ℝ) (259307046243/500000000000 : ℝ) (32413380779/62500000000 : ℝ) (518614092471/1000000000000 : ℝ) (64826761559/125000000000 : ℝ) (518614092479/1000000000000 : ℝ) (518614092471/1000000000000 : ℝ) (518614092479/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2279/16384 : ℝ))) 5 (64826761559/125000000000 : ℝ) (518614092479/1000000000000 : ℝ) (518614092471/1000000000000 : ℝ) (518614092479/1000000000000 : ℝ) (518614092471/1000000000000 : ℝ) (518614092479/1000000000000 : ℝ) (518614092471/1000000000000 : ℝ) (518614092479/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2279/16384 : ℝ))) 6 (518614092471/1000000000000 : ℝ) (518614092479/1000000000000 : ℝ) (518614092471/1000000000000 : ℝ) (518614092479/1000000000000 : ℝ) (518614092471/1000000000000 : ℝ) (518614092479/1000000000000 : ℝ) (518614092471/1000000000000 : ℝ) (518614092479/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2279/16384 : ℝ))) 7 (518614092471/1000000000000 : ℝ) (518614092479/1000000000000 : ℝ) (518614092471/1000000000000 : ℝ) (518614092479/1000000000000 : ℝ) (518614092471/1000000000000 : ℝ) (518614092479/1000000000000 : ℝ) (518614092471/1000000000000 : ℝ) (518614092479/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2279/16384 : ℝ)) hmem 8 (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ) (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2279/16384 : ℝ))) hcmem 8 (518614092471/1000000000000 : ℝ) (518614092479/1000000000000 : ℝ) (518614092471/1000000000000 : ℝ) (518614092479/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2279/16384 : ℝ)) (198027595873/200000000000 : ℝ) (123767247421/125000000000 : ℝ) (518614092471/1000000000000 : ℝ) (518614092479/1000000000000 : ℝ) (411375549899/500000000000 : ℝ) (411375549907/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0478_exp_lower
  have heNumeric : (2019019232057/1000000000000 : ℝ)/4 ≤ Real.exp (-5469459970387/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019019232057/1000000000000 : ℝ)/4 ≤ Real.exp ((4557/32768 : ℝ)-(411375549907/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4557/32768 : ℝ) (2279/16384 : ℝ) (411375549907/500000000000 : ℝ) (2019019232057/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0479; no trusted numerical premise.
theorem cover7_leaf0479_exp_radius : (199503725175524939/200000000000000000 : ℝ) ≤ Real.exp ((-4559/229376 : ℝ)/8) ∧ Real.exp ((-4559/229376 : ℝ)/8) ≤ (124689828234703087/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4559/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0479_exp_lower : (114761203531567907/125000000000000000 : ℝ) ≤ Real.exp ((-2734728283697/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734728283697/4000000000000 : ℝ)/8) ≤ (918089628252543257/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734728283697/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0479_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (126188755681/62500000000 : ℝ) ≤ 4*Real.exp (2279/16384 : ℝ)*Real.exp (-mu (radius 7 (4559/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (126188755681/62500000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4559/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0479_exp_radius
  have hrNumeric : (245080139043/250000000000 : ℝ) ≤ Real.exp (-4559/229376 : ℝ) ∧ Real.exp (-4559/229376 : ℝ) ≤ (980320556173/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245080139043/250000000000 : ℝ) ≤ (radius 7 (4559/32768 : ℝ)) ∧ (radius 7 (4559/32768 : ℝ)) ≤ (980320556173/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4559/32768 : ℝ)) (245080139043/250000000000 : ℝ) (980320556173/1000000000000 : ℝ) (98706138543/500000000000 : ℝ) (49353069273/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4559/32768 : ℝ)) (245080139043/250000000000 : ℝ) (980320556173/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4559/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245080139043/250000000000 : ℝ) (980320556173/1000000000000 : ℝ) (495080139043/500000000000 : ℝ) (990160278087/1000000000000 : ℝ) (49505569287/50000000000 : ℝ) (990111385741/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4559/32768 : ℝ)) 1 (495080139043/500000000000 : ℝ) (990160278087/1000000000000 : ℝ) (49505569287/50000000000 : ℝ) (990111385741/1000000000000 : ℝ) (990135831913/1000000000000 : ℝ) (495067915957/500000000000 : ℝ) (990135831611/1000000000000 : ℝ) (990135831613/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4559/32768 : ℝ)) 2 (990135831913/1000000000000 : ℝ) (495067915957/500000000000 : ℝ) (990135831611/1000000000000 : ℝ) (990135831613/1000000000000 : ℝ) (495067915881/500000000000 : ℝ) (247533957941/250000000000 : ℝ) (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4559/32768 : ℝ)) 3 (495067915881/500000000000 : ℝ) (247533957941/250000000000 : ℝ) (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ) (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ) (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4559/32768 : ℝ)) 4 (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ) (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ) (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ) (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4559/32768 : ℝ)) 5 (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ) (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ) (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ) (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4559/32768 : ℝ)) 6 (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ) (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ) (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ) (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4559/32768 : ℝ)) 7 (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ) (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ) (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ) (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4559/32768 : ℝ))) (98706138543/500000000000 : ℝ) (49353069273/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4559/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98706138543/500000000000 : ℝ) (49353069273/250000000000 : ℝ) (598706138543/1000000000000 : ℝ) (299353069273/500000000000 : ℝ) (222155506957/500000000000 : ℝ) (222155506961/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4559/32768 : ℝ))) 1 (598706138543/1000000000000 : ℝ) (299353069273/500000000000 : ℝ) (222155506957/500000000000 : ℝ) (222155506961/500000000000 : ℝ) (130377144057/250000000000 : ℝ) (260754288117/500000000000 : ℝ) (515763251359/1000000000000 : ℝ) (257881625683/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4559/32768 : ℝ))) 2 (130377144057/250000000000 : ℝ) (260754288117/500000000000 : ℝ) (515763251359/1000000000000 : ℝ) (257881625683/500000000000 : ℝ) (518635913793/1000000000000 : ℝ) (2593179569/5000000000 : ℝ) (103725591613/200000000000 : ℝ) (64828494759/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4559/32768 : ℝ))) 3 (518635913793/1000000000000 : ℝ) (2593179569/5000000000 : ℝ) (103725591613/200000000000 : ℝ) (64828494759/125000000000 : ℝ) (518631935929/1000000000000 : ℝ) (8103623999/15625000000 : ℝ) (518631935913/1000000000000 : ℝ) (518631935921/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4559/32768 : ℝ))) 4 (518631935929/1000000000000 : ℝ) (8103623999/15625000000 : ℝ) (518631935913/1000000000000 : ℝ) (518631935921/1000000000000 : ℝ) (518631935921/1000000000000 : ℝ) (518631935929/1000000000000 : ℝ) (6482899199/12500000000 : ℝ) (518631935929/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4559/32768 : ℝ))) 5 (518631935921/1000000000000 : ℝ) (518631935929/1000000000000 : ℝ) (6482899199/12500000000 : ℝ) (518631935929/1000000000000 : ℝ) (6482899199/12500000000 : ℝ) (518631935929/1000000000000 : ℝ) (6482899199/12500000000 : ℝ) (518631935929/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4559/32768 : ℝ))) 6 (6482899199/12500000000 : ℝ) (518631935929/1000000000000 : ℝ) (6482899199/12500000000 : ℝ) (518631935929/1000000000000 : ℝ) (6482899199/12500000000 : ℝ) (518631935929/1000000000000 : ℝ) (6482899199/12500000000 : ℝ) (518631935929/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4559/32768 : ℝ))) 7 (6482899199/12500000000 : ℝ) (518631935929/1000000000000 : ℝ) (6482899199/12500000000 : ℝ) (518631935929/1000000000000 : ℝ) (6482899199/12500000000 : ℝ) (518631935929/1000000000000 : ℝ) (6482899199/12500000000 : ℝ) (518631935929/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4559/32768 : ℝ)) hmem 8 (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ) (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4559/32768 : ℝ))) hcmem 8 (6482899199/12500000000 : ℝ) (518631935929/1000000000000 : ℝ) (6482899199/12500000000 : ℝ) (518631935929/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4559/32768 : ℝ)) (990135831761/1000000000000 : ℝ) (247533957941/250000000000 : ℝ) (6482899199/12500000000 : ℝ) (518631935929/1000000000000 : ℝ) (102847649/125000000 : ℝ) (411390596009/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0479_exp_lower
  have heNumeric : (126188755681/62500000000 : ℝ)/4 ≤ Real.exp (-2734728283697/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (126188755681/62500000000 : ℝ)/4 ≤ Real.exp ((2279/16384 : ℝ)-(411390596009/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2279/16384 : ℝ) (4559/32768 : ℝ) (411390596009/500000000000 : ℝ) (126188755681/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0480; no trusted numerical premise.
theorem cover7_leaf0480_exp_radius : (498759041136631083/500000000000000000 : ℝ) ≤ Real.exp ((-285/14336 : ℝ)/8) ∧ Real.exp ((-285/14336 : ℝ)/8) ≤ (997518082273262167/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-285/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0480_exp_lower : (918089677573825651/1000000000000000000 : ℝ) ≤ Real.exp ((-5469453129209/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469453129209/8000000000000 : ℝ)/8) ≤ (229522419393456413/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469453129209/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0480_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019020958617/1000000000000 : ℝ) ≤ 4*Real.exp (4559/32768 : ℝ)*Real.exp (-mu (radius 7 (285/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (2019020958617/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (285/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0480_exp_radius
  have hrNumeric : (980316282323/1000000000000 : ℝ) ≤ Real.exp (-285/14336 : ℝ) ∧ Real.exp (-285/14336 : ℝ) ≤ (245079070581/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980316282323/1000000000000 : ℝ) ≤ (radius 7 (285/2048 : ℝ)) ∧ (radius 7 (285/2048 : ℝ)) ≤ (245079070581/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (285/2048 : ℝ)) (980316282323/1000000000000 : ℝ) (245079070581/250000000000 : ℝ) (19743349921/100000000000 : ℝ) (12339593701/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (285/2048 : ℝ)) (980316282323/1000000000000 : ℝ) (245079070581/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (285/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980316282323/1000000000000 : ℝ) (245079070581/250000000000 : ℝ) (990158141161/1000000000000 : ℝ) (495079070581/500000000000 : ℝ) (99010922747/100000000000 : ℝ) (61881826717/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (285/2048 : ℝ)) 1 (990158141161/1000000000000 : ℝ) (495079070581/500000000000 : ℝ) (99010922747/100000000000 : ℝ) (61881826717/62500000000 : ℝ) (198026736863/200000000000 : ℝ) (990133684317/1000000000000 : ℝ) (990133684013/1000000000000 : ℝ) (198026736803/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (285/2048 : ℝ)) 2 (198026736863/200000000000 : ℝ) (990133684317/1000000000000 : ℝ) (990133684013/1000000000000 : ℝ) (198026736803/200000000000 : ℝ) (247533421041/250000000000 : ℝ) (495066842083/500000000000 : ℝ) (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (285/2048 : ℝ)) 3 (247533421041/250000000000 : ℝ) (495066842083/500000000000 : ℝ) (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ) (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ) (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (285/2048 : ℝ)) 4 (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ) (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ) (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ) (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (285/2048 : ℝ)) 5 (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ) (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ) (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ) (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (285/2048 : ℝ)) 6 (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ) (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ) (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ) (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (285/2048 : ℝ)) 7 (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ) (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ) (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ) (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (285/2048 : ℝ))) (19743349921/100000000000 : ℝ) (12339593701/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (285/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19743349921/100000000000 : ℝ) (12339593701/62500000000 : ℝ) (119743349921/200000000000 : ℝ) (74839593701/125000000000 : ℝ) (111083723833/250000000000 : ℝ) (22216744767/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (285/2048 : ℝ))) 1 (119743349921/200000000000 : ℝ) (74839593701/125000000000 : ℝ) (111083723833/250000000000 : ℝ) (22216744767/50000000000 : ℝ) (130381455617/250000000000 : ℝ) (260762911237/500000000000 : ℝ) (257890841379/500000000000 : ℝ) (103156336553/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (285/2048 : ℝ))) 2 (130381455617/250000000000 : ℝ) (260762911237/500000000000 : ℝ) (257890841379/500000000000 : ℝ) (103156336553/200000000000 : ℝ) (518653752613/1000000000000 : ℝ) (25932687631/50000000000 : ℝ) (12966145011/25000000000 : ℝ) (518645800447/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (285/2048 : ℝ))) 3 (518653752613/1000000000000 : ℝ) (25932687631/50000000000 : ℝ) (12966145011/25000000000 : ℝ) (518645800447/1000000000000 : ℝ) (259324888263/500000000000 : ℝ) (259324888267/500000000000 : ℝ) (518649776511/1000000000000 : ℝ) (518649776519/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (285/2048 : ℝ))) 4 (259324888263/500000000000 : ℝ) (259324888267/500000000000 : ℝ) (518649776511/1000000000000 : ℝ) (518649776519/1000000000000 : ℝ) (259324888259/500000000000 : ℝ) (518649776527/1000000000000 : ℝ) (259324888259/500000000000 : ℝ) (518649776527/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (285/2048 : ℝ))) 5 (259324888259/500000000000 : ℝ) (518649776527/1000000000000 : ℝ) (259324888259/500000000000 : ℝ) (518649776527/1000000000000 : ℝ) (259324888259/500000000000 : ℝ) (518649776527/1000000000000 : ℝ) (259324888259/500000000000 : ℝ) (518649776527/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (285/2048 : ℝ))) 6 (259324888259/500000000000 : ℝ) (518649776527/1000000000000 : ℝ) (259324888259/500000000000 : ℝ) (518649776527/1000000000000 : ℝ) (259324888259/500000000000 : ℝ) (518649776527/1000000000000 : ℝ) (259324888259/500000000000 : ℝ) (518649776527/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (285/2048 : ℝ))) 7 (259324888259/500000000000 : ℝ) (518649776527/1000000000000 : ℝ) (259324888259/500000000000 : ℝ) (518649776527/1000000000000 : ℝ) (259324888259/500000000000 : ℝ) (518649776527/1000000000000 : ℝ) (259324888259/500000000000 : ℝ) (518649776527/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (285/2048 : ℝ)) hmem 8 (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ) (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (285/2048 : ℝ))) hcmem 8 (259324888259/500000000000 : ℝ) (518649776527/1000000000000 : ℝ) (259324888259/500000000000 : ℝ) (518649776527/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (285/2048 : ℝ)) (990133684163/1000000000000 : ℝ) (495066842083/500000000000 : ℝ) (259324888259/500000000000 : ℝ) (518649776527/1000000000000 : ℝ) (164562255961/200000000000 : ℝ) (822811279823/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0480_exp_lower
  have heNumeric : (2019020958617/1000000000000 : ℝ)/4 ≤ Real.exp (-5469453129209/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019020958617/1000000000000 : ℝ)/4 ≤ Real.exp ((4559/32768 : ℝ)-(822811279823/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4559/32768 : ℝ) (285/2048 : ℝ) (822811279823/1000000000000 : ℝ) (2019020958617/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0481; no trusted numerical premise.
theorem cover7_leaf0481_exp_radius : (498758769334597939/500000000000000000 : ℝ) ≤ Real.exp ((-4561/229376 : ℝ)/8) ∧ Real.exp ((-4561/229376 : ℝ)/8) ≤ (997517538669195879/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4561/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0481_exp_lower : (918089727399830523/1000000000000000000 : ℝ) ≤ Real.exp ((-34184060349/50000000000 : ℝ)/8) ∧ Real.exp ((-34184060349/50000000000 : ℝ)/8) ≤ (229522431849957631/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-34184060349/50000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0481_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019021835217/1000000000000 : ℝ) ≤ 4*Real.exp (285/2048 : ℝ)*Real.exp (-mu (radius 7 (4561/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019021835217/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4561/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0481_exp_radius
  have hrNumeric : (245078002123/250000000000 : ℝ) ≤ Real.exp (-4561/229376 : ℝ) ∧ Real.exp (-4561/229376 : ℝ) ≤ (980312008493/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245078002123/250000000000 : ℝ) ≤ (radius 7 (4561/32768 : ℝ)) ∧ (radius 7 (4561/32768 : ℝ)) ≤ (980312008493/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4561/32768 : ℝ)) (245078002123/250000000000 : ℝ) (980312008493/1000000000000 : ℝ) (19745471887/100000000000 : ℝ) (49363679719/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4561/32768 : ℝ)) (245078002123/250000000000 : ℝ) (980312008493/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4561/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245078002123/250000000000 : ℝ) (980312008493/1000000000000 : ℝ) (495078002123/500000000000 : ℝ) (990156004247/1000000000000 : ℝ) (495053534603/500000000000 : ℝ) (990107069207/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4561/32768 : ℝ)) 1 (495078002123/500000000000 : ℝ) (990156004247/1000000000000 : ℝ) (495053534603/500000000000 : ℝ) (990107069207/1000000000000 : ℝ) (495065768363/500000000000 : ℝ) (990131536727/1000000000000 : ℝ) (990131536423/1000000000000 : ℝ) (39605261457/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4561/32768 : ℝ)) 2 (495065768363/500000000000 : ℝ) (990131536727/1000000000000 : ℝ) (990131536423/1000000000000 : ℝ) (39605261457/40000000000 : ℝ) (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ) (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4561/32768 : ℝ)) 3 (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ) (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ) (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ) (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4561/32768 : ℝ)) 4 (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ) (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ) (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ) (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4561/32768 : ℝ)) 5 (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ) (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ) (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ) (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4561/32768 : ℝ)) 6 (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ) (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ) (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ) (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4561/32768 : ℝ)) 7 (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ) (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ) (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ) (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4561/32768 : ℝ))) (19745471887/100000000000 : ℝ) (49363679719/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4561/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19745471887/100000000000 : ℝ) (49363679719/250000000000 : ℝ) (119745471887/200000000000 : ℝ) (299363679719/500000000000 : ℝ) (444358772693/1000000000000 : ℝ) (444358772701/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4561/32768 : ℝ))) 1 (119745471887/200000000000 : ℝ) (299363679719/500000000000 : ℝ) (444358772693/1000000000000 : ℝ) (444358772701/1000000000000 : ℝ) (32596441629/62500000000 : ℝ) (52154306607/100000000000 : ℝ) (103160022221/200000000000 : ℝ) (64475013889/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4561/32768 : ℝ))) 2 (32596441629/62500000000 : ℝ) (52154306607/100000000000 : ℝ) (103160022221/200000000000 : ℝ) (64475013889/125000000000 : ℝ) (64833948573/125000000000 : ℝ) (518671588591/1000000000000 : ℝ) (103732727993/200000000000 : ℝ) (129665909993/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4561/32768 : ℝ))) 3 (64833948573/125000000000 : ℝ) (518671588591/1000000000000 : ℝ) (103732727993/200000000000 : ℝ) (129665909993/250000000000 : ℝ) (259333807137/500000000000 : ℝ) (259333807141/500000000000 : ℝ) (518667614259/1000000000000 : ℝ) (518667614267/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4561/32768 : ℝ))) 4 (259333807137/500000000000 : ℝ) (259333807141/500000000000 : ℝ) (518667614259/1000000000000 : ℝ) (518667614267/1000000000000 : ℝ) (259333807133/500000000000 : ℝ) (20746704571/40000000000 : ℝ) (259333807133/500000000000 : ℝ) (20746704571/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4561/32768 : ℝ))) 5 (259333807133/500000000000 : ℝ) (20746704571/40000000000 : ℝ) (259333807133/500000000000 : ℝ) (20746704571/40000000000 : ℝ) (259333807133/500000000000 : ℝ) (20746704571/40000000000 : ℝ) (259333807133/500000000000 : ℝ) (20746704571/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4561/32768 : ℝ))) 6 (259333807133/500000000000 : ℝ) (20746704571/40000000000 : ℝ) (259333807133/500000000000 : ℝ) (20746704571/40000000000 : ℝ) (259333807133/500000000000 : ℝ) (20746704571/40000000000 : ℝ) (259333807133/500000000000 : ℝ) (20746704571/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4561/32768 : ℝ))) 7 (259333807133/500000000000 : ℝ) (20746704571/40000000000 : ℝ) (259333807133/500000000000 : ℝ) (20746704571/40000000000 : ℝ) (259333807133/500000000000 : ℝ) (20746704571/40000000000 : ℝ) (259333807133/500000000000 : ℝ) (20746704571/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4561/32768 : ℝ)) hmem 8 (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ) (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4561/32768 : ℝ))) hcmem 8 (259333807133/500000000000 : ℝ) (20746704571/40000000000 : ℝ) (259333807133/500000000000 : ℝ) (20746704571/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4561/32768 : ℝ)) (495065768287/500000000000 : ℝ) (15470805259/15625000000 : ℝ) (259333807133/500000000000 : ℝ) (20746704571/40000000000 : ℝ) (822841363213/1000000000000 : ℝ) (82284136323/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0481_exp_lower
  have heNumeric : (2019021835217/1000000000000 : ℝ)/4 ≤ Real.exp (-34184060349/50000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019021835217/1000000000000 : ℝ)/4 ≤ Real.exp ((285/2048 : ℝ)-(82284136323/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (285/2048 : ℝ) (4561/32768 : ℝ) (82284136323/100000000000 : ℝ) (2019021835217/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0482; no trusted numerical premise.
theorem cover7_leaf0482_exp_radius : (997516995065425831/1000000000000000000 : ℝ) ≤ Real.exp ((-2281/114688 : ℝ)/8) ∧ Real.exp ((-2281/114688 : ℝ)/8) ≤ (124689624383178229/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2281/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0482_exp_lower : (183617955546111591/200000000000000000 : ℝ) ≤ Real.exp ((-5469446147287/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469446147287/8000000000000 : ℝ)/8) ≤ (229522444432639489/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469446147287/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0482_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009511360349/500000000000 : ℝ) ≤ 4*Real.exp (4561/32768 : ℝ)*Real.exp (-mu (radius 7 (2281/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (1009511360349/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2281/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0482_exp_radius
  have hrNumeric : (24507693367/25000000000 : ℝ) ≤ Real.exp (-2281/114688 : ℝ) ∧ Real.exp (-2281/114688 : ℝ) ≤ (980307734681/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24507693367/25000000000 : ℝ) ≤ (radius 7 (2281/16384 : ℝ)) ∧ (radius 7 (2281/16384 : ℝ)) ≤ (980307734681/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2281/16384 : ℝ)) (24507693367/25000000000 : ℝ) (980307734681/1000000000000 : ℝ) (3085561501/15625000000 : ℝ) (19747593607/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2281/16384 : ℝ)) (24507693367/25000000000 : ℝ) (980307734681/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2281/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24507693367/25000000000 : ℝ) (980307734681/1000000000000 : ℝ) (49507693367/50000000000 : ℝ) (990153867341/1000000000000 : ℝ) (495052455473/500000000000 : ℝ) (990104910947/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2281/16384 : ℝ)) 1 (49507693367/50000000000 : ℝ) (990153867341/1000000000000 : ℝ) (495052455473/500000000000 : ℝ) (990104910947/1000000000000 : ℝ) (990129389143/1000000000000 : ℝ) (123766173643/125000000000 : ℝ) (24753234721/25000000000 : ℝ) (495064694421/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2281/16384 : ℝ)) 2 (990129389143/1000000000000 : ℝ) (123766173643/125000000000 : ℝ) (24753234721/25000000000 : ℝ) (495064694421/500000000000 : ℝ) (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ) (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2281/16384 : ℝ)) 3 (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ) (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ) (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ) (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2281/16384 : ℝ)) 4 (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ) (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ) (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ) (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2281/16384 : ℝ)) 5 (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ) (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ) (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ) (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2281/16384 : ℝ)) 6 (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ) (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ) (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ) (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2281/16384 : ℝ)) 7 (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ) (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ) (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ) (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2281/16384 : ℝ))) (3085561501/15625000000 : ℝ) (19747593607/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2281/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3085561501/15625000000 : ℝ) (19747593607/100000000000 : ℝ) (18710561501/31250000000 : ℝ) (119747593607/200000000000 : ℝ) (444382645997/1000000000000 : ℝ) (88876529201/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2281/16384 : ℝ))) 1 (18710561501/31250000000 : ℝ) (119747593607/200000000000 : ℝ) (444382645997/1000000000000 : ℝ) (88876529201/200000000000 : ℝ) (260780153507/500000000000 : ℝ) (26078015351/50000000000 : ℝ) (515818536399/1000000000000 : ℝ) (257909268203/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2281/16384 : ℝ))) 2 (260780153507/500000000000 : ℝ) (26078015351/50000000000 : ℝ) (515818536399/1000000000000 : ℝ) (257909268203/500000000000 : ℝ) (259344710853/500000000000 : ℝ) (518689421713/1000000000000 : ℝ) (259340738319/500000000000 : ℝ) (103736295329/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2281/16384 : ℝ))) 3 (259344710853/500000000000 : ℝ) (518689421713/1000000000000 : ℝ) (259340738319/500000000000 : ℝ) (103736295329/200000000000 : ℝ) (129671362293/250000000000 : ℝ) (518685449179/1000000000000 : ℝ) (129671362289/250000000000 : ℝ) (129671362291/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2281/16384 : ℝ))) 4 (129671362293/250000000000 : ℝ) (518685449179/1000000000000 : ℝ) (129671362289/250000000000 : ℝ) (129671362291/250000000000 : ℝ) (129671362291/250000000000 : ℝ) (129671362293/250000000000 : ℝ) (518685449163/1000000000000 : ℝ) (129671362293/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2281/16384 : ℝ))) 5 (129671362291/250000000000 : ℝ) (129671362293/250000000000 : ℝ) (518685449163/1000000000000 : ℝ) (129671362293/250000000000 : ℝ) (518685449163/1000000000000 : ℝ) (129671362293/250000000000 : ℝ) (518685449163/1000000000000 : ℝ) (129671362293/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2281/16384 : ℝ))) 6 (518685449163/1000000000000 : ℝ) (129671362293/250000000000 : ℝ) (518685449163/1000000000000 : ℝ) (129671362293/250000000000 : ℝ) (518685449163/1000000000000 : ℝ) (129671362293/250000000000 : ℝ) (518685449163/1000000000000 : ℝ) (129671362293/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2281/16384 : ℝ))) 7 (518685449163/1000000000000 : ℝ) (129671362293/250000000000 : ℝ) (518685449163/1000000000000 : ℝ) (129671362293/250000000000 : ℝ) (518685449163/1000000000000 : ℝ) (129671362293/250000000000 : ℝ) (518685449163/1000000000000 : ℝ) (129671362293/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2281/16384 : ℝ)) hmem 8 (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ) (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2281/16384 : ℝ))) hcmem 8 (518685449163/1000000000000 : ℝ) (129671362293/250000000000 : ℝ) (518685449163/1000000000000 : ℝ) (129671362293/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2281/16384 : ℝ)) (990129388991/1000000000000 : ℝ) (990129388993/1000000000000 : ℝ) (518685449163/1000000000000 : ℝ) (129671362293/250000000000 : ℝ) (411435721111/500000000000 : ℝ) (822871442239/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0482_exp_lower
  have heNumeric : (1009511360349/500000000000 : ℝ)/4 ≤ Real.exp (-5469446147287/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009511360349/500000000000 : ℝ)/4 ≤ Real.exp ((4561/32768 : ℝ)-(822871442239/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4561/32768 : ℝ) (2281/16384 : ℝ) (822871442239/1000000000000 : ℝ) (1009511360349/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0483; no trusted numerical premise.
theorem cover7_leaf0483_exp_radius : (124689556432744003/125000000000000000 : ℝ) ≤ Real.exp ((-4563/229376 : ℝ)/8) ∧ Real.exp ((-4563/229376 : ℝ)/8) ≤ (39900658058478081/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4563/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0483_exp_lower : (114761228570693623/125000000000000000 : ℝ) ≤ Real.exp ((-2734721301791/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734721301791/4000000000000 : ℝ)/8) ≤ (183617965713109797/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734721301791/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0483_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019023615051/1000000000000 : ℝ) ≤ 4*Real.exp (2281/16384 : ℝ)*Real.exp (-mu (radius 7 (4563/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019023615051/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4563/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0483_exp_radius
  have hrNumeric : (980303460887/1000000000000 : ℝ) ≤ Real.exp (-4563/229376 : ℝ) ∧ Real.exp (-4563/229376 : ℝ) ≤ (122537932611/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980303460887/1000000000000 : ℝ) ≤ (radius 7 (4563/32768 : ℝ)) ∧ (radius 7 (4563/32768 : ℝ)) ≤ (122537932611/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4563/32768 : ℝ)) (980303460887/1000000000000 : ℝ) (122537932611/125000000000 : ℝ) (24687143849/125000000000 : ℝ) (98748575399/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4563/32768 : ℝ)) (980303460887/1000000000000 : ℝ) (122537932611/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4563/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980303460887/1000000000000 : ℝ) (122537932611/125000000000 : ℝ) (990151730443/1000000000000 : ℝ) (247537932611/250000000000 : ℝ) (990102752691/1000000000000 : ℝ) (247525688173/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4563/32768 : ℝ)) 1 (990151730443/1000000000000 : ℝ) (247537932611/250000000000 : ℝ) (990102752691/1000000000000 : ℝ) (247525688173/250000000000 : ℝ) (990127241567/1000000000000 : ℝ) (30941476299/31250000000 : ℝ) (61882952579/62500000000 : ℝ) (495063620633/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4563/32768 : ℝ)) 2 (990127241567/1000000000000 : ℝ) (30941476299/31250000000 : ℝ) (61882952579/62500000000 : ℝ) (495063620633/500000000000 : ℝ) (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ) (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4563/32768 : ℝ)) 3 (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ) (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ) (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ) (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4563/32768 : ℝ)) 4 (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ) (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ) (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ) (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4563/32768 : ℝ)) 5 (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ) (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ) (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ) (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4563/32768 : ℝ)) 6 (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ) (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ) (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ) (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4563/32768 : ℝ)) 7 (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ) (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ) (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ) (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4563/32768 : ℝ))) (24687143849/125000000000 : ℝ) (98748575399/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4563/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24687143849/125000000000 : ℝ) (98748575399/500000000000 : ℝ) (149687143849/250000000000 : ℝ) (598748575399/1000000000000 : ℝ) (111101628811/250000000000 : ℝ) (111101628813/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4563/32768 : ℝ))) 1 (149687143849/250000000000 : ℝ) (598748575399/1000000000000 : ℝ) (111101628811/250000000000 : ℝ) (111101628813/250000000000 : ℝ) (13039438633/25000000000 : ℝ) (260788772663/500000000000 : ℝ) (6447961983/12500000000 : ℝ) (515836958647/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4563/32768 : ℝ))) 2 (13039438633/25000000000 : ℝ) (260788772663/500000000000 : ℝ) (6447961983/12500000000 : ℝ) (515836958647/1000000000000 : ℝ) (25935362599/50000000000 : ℝ) (518707251987/1000000000000 : ℝ) (518699310461/1000000000000 : ℝ) (129674827617/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4563/32768 : ℝ))) 3 (25935362599/50000000000 : ℝ) (518707251987/1000000000000 : ℝ) (518699310461/1000000000000 : ℝ) (129674827617/250000000000 : ℝ) (25935164061/50000000000 : ℝ) (129675820307/250000000000 : ℝ) (103740656241/200000000000 : ℝ) (518703281213/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4563/32768 : ℝ))) 4 (25935164061/50000000000 : ℝ) (129675820307/250000000000 : ℝ) (103740656241/200000000000 : ℝ) (518703281213/1000000000000 : ℝ) (129675820303/250000000000 : ℝ) (518703281221/1000000000000 : ℝ) (129675820303/250000000000 : ℝ) (518703281221/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4563/32768 : ℝ))) 5 (129675820303/250000000000 : ℝ) (518703281221/1000000000000 : ℝ) (129675820303/250000000000 : ℝ) (518703281221/1000000000000 : ℝ) (129675820303/250000000000 : ℝ) (518703281221/1000000000000 : ℝ) (129675820303/250000000000 : ℝ) (518703281221/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4563/32768 : ℝ))) 6 (129675820303/250000000000 : ℝ) (518703281221/1000000000000 : ℝ) (129675820303/250000000000 : ℝ) (518703281221/1000000000000 : ℝ) (129675820303/250000000000 : ℝ) (518703281221/1000000000000 : ℝ) (129675820303/250000000000 : ℝ) (518703281221/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4563/32768 : ℝ))) 7 (129675820303/250000000000 : ℝ) (518703281221/1000000000000 : ℝ) (129675820303/250000000000 : ℝ) (518703281221/1000000000000 : ℝ) (129675820303/250000000000 : ℝ) (518703281221/1000000000000 : ℝ) (129675820303/250000000000 : ℝ) (518703281221/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4563/32768 : ℝ)) hmem 8 (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ) (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4563/32768 : ℝ))) hcmem 8 (129675820303/250000000000 : ℝ) (518703281221/1000000000000 : ℝ) (129675820303/250000000000 : ℝ) (518703281221/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4563/32768 : ℝ)) (198025448283/200000000000 : ℝ) (990127241417/1000000000000 : ℝ) (129675820303/250000000000 : ℝ) (518703281221/1000000000000 : ℝ) (822901516837/1000000000000 : ℝ) (411450758427/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0483_exp_lower
  have heNumeric : (2019023615051/1000000000000 : ℝ)/4 ≤ Real.exp (-2734721301791/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019023615051/1000000000000 : ℝ)/4 ≤ Real.exp ((2281/16384 : ℝ)-(411450758427/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2281/16384 : ℝ) (4563/32768 : ℝ) (411450758427/500000000000 : ℝ) (2019023615051/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0484; no trusted numerical premise.
theorem cover7_leaf0484_exp_radius : (997515907858774457/1000000000000000000 : ℝ) ≤ Real.exp ((-163/8192 : ℝ)/8) ∧ Real.exp ((-163/8192 : ℝ)/8) ≤ (498757953929387229/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-163/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0484_exp_lower : (918089879904459411/1000000000000000000 : ℝ) ≤ Real.exp ((-5469439024749/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469439024749/8000000000000 : ℝ)/8) ≤ (229522469976114853/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469439024749/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0484_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201902451827/100000000000 : ℝ) ≤ 4*Real.exp (4563/32768 : ℝ)*Real.exp (-mu (radius 7 (1141/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (201902451827/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1141/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0484_exp_radius
  have hrNumeric : (122537398389/125000000000 : ℝ) ≤ Real.exp (-163/8192 : ℝ) ∧ Real.exp (-163/8192 : ℝ) ≤ (980299187113/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122537398389/125000000000 : ℝ) ≤ (radius 7 (1141/8192 : ℝ)) ∧ (radius 7 (1141/8192 : ℝ)) ≤ (980299187113/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1141/8192 : ℝ)) (122537398389/125000000000 : ℝ) (980299187113/1000000000000 : ℝ) (197518363059/1000000000000 : ℝ) (39503672613/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1141/8192 : ℝ)) (122537398389/125000000000 : ℝ) (980299187113/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1141/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122537398389/125000000000 : ℝ) (980299187113/1000000000000 : ℝ) (247537398389/250000000000 : ℝ) (990149593557/1000000000000 : ℝ) (24752514861/25000000000 : ℝ) (495050297221/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1141/8192 : ℝ)) 1 (247537398389/250000000000 : ℝ) (990149593557/1000000000000 : ℝ) (24752514861/25000000000 : ℝ) (495050297221/500000000000 : ℝ) (495062546999/500000000000 : ℝ) (495062547/500000000 : ℝ) (495062546847/500000000000 : ℝ) (990125093697/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1141/8192 : ℝ)) 2 (495062546999/500000000000 : ℝ) (495062547/500000000 : ℝ) (495062546847/500000000000 : ℝ) (990125093697/1000000000000 : ℝ) (495062546923/500000000000 : ℝ) (990125093849/1000000000000 : ℝ) (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1141/8192 : ℝ)) 3 (495062546923/500000000000 : ℝ) (990125093849/1000000000000 : ℝ) (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ) (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ) (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1141/8192 : ℝ)) 4 (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ) (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ) (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ) (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1141/8192 : ℝ)) 5 (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ) (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ) (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ) (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1141/8192 : ℝ)) 6 (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ) (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ) (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ) (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1141/8192 : ℝ)) 7 (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ) (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ) (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ) (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1141/8192 : ℝ))) (197518363059/1000000000000 : ℝ) (39503672613/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1141/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (197518363059/1000000000000 : ℝ) (39503672613/200000000000 : ℝ) (598759181529/1000000000000 : ℝ) (598759181533/1000000000000 : ℝ) (444430380441/1000000000000 : ℝ) (13888449389/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1141/8192 : ℝ))) 1 (598759181529/1000000000000 : ℝ) (598759181533/1000000000000 : ℝ) (444430380441/1000000000000 : ℝ) (13888449389/31250000000 : ℝ) (104318956197/200000000000 : ℝ) (521594780991/1000000000000 : ℝ) (515855377833/1000000000000 : ℝ) (6448192223/12500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1141/8192 : ℝ))) 2 (104318956197/200000000000 : ℝ) (521594780991/1000000000000 : ℝ) (515855377833/1000000000000 : ℝ) (6448192223/12500000000 : ℝ) (518725079409/1000000000000 : ℝ) (64840634927/125000000000 : ℝ) (518717141437/1000000000000 : ℝ) (129679285361/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1141/8192 : ℝ))) 3 (518725079409/1000000000000 : ℝ) (64840634927/125000000000 : ℝ) (518717141437/1000000000000 : ℝ) (129679285361/250000000000 : ℝ) (518721110423/1000000000000 : ℝ) (51872111043/100000000000 : ℝ) (518721110407/1000000000000 : ℝ) (103744222083/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1141/8192 : ℝ))) 4 (518721110423/1000000000000 : ℝ) (51872111043/100000000000 : ℝ) (518721110407/1000000000000 : ℝ) (103744222083/200000000000 : ℝ) (103744222083/200000000000 : ℝ) (518721110423/1000000000000 : ℝ) (259360555207/500000000000 : ℝ) (518721110423/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1141/8192 : ℝ))) 5 (103744222083/200000000000 : ℝ) (518721110423/1000000000000 : ℝ) (259360555207/500000000000 : ℝ) (518721110423/1000000000000 : ℝ) (259360555207/500000000000 : ℝ) (518721110423/1000000000000 : ℝ) (259360555207/500000000000 : ℝ) (518721110423/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1141/8192 : ℝ))) 6 (259360555207/500000000000 : ℝ) (518721110423/1000000000000 : ℝ) (259360555207/500000000000 : ℝ) (518721110423/1000000000000 : ℝ) (259360555207/500000000000 : ℝ) (518721110423/1000000000000 : ℝ) (259360555207/500000000000 : ℝ) (518721110423/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1141/8192 : ℝ))) 7 (259360555207/500000000000 : ℝ) (518721110423/1000000000000 : ℝ) (259360555207/500000000000 : ℝ) (518721110423/1000000000000 : ℝ) (259360555207/500000000000 : ℝ) (518721110423/1000000000000 : ℝ) (259360555207/500000000000 : ℝ) (518721110423/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1141/8192 : ℝ)) hmem 8 (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ) (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1141/8192 : ℝ))) hcmem 8 (259360555207/500000000000 : ℝ) (518721110423/1000000000000 : ℝ) (259360555207/500000000000 : ℝ) (518721110423/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1141/8192 : ℝ)) (198025018769/200000000000 : ℝ) (990125093849/1000000000000 : ℝ) (259360555207/500000000000 : ℝ) (518721110423/1000000000000 : ℝ) (41146579353/50000000000 : ℝ) (411465793539/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0484_exp_lower
  have heNumeric : (201902451827/100000000000 : ℝ)/4 ≤ Real.exp (-5469439024749/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201902451827/100000000000 : ℝ)/4 ≤ Real.exp ((4563/32768 : ℝ)-(411465793539/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4563/32768 : ℝ) (1141/8192 : ℝ) (411465793539/500000000000 : ℝ) (201902451827/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0485; no trusted numerical premise.
theorem cover7_leaf0485_exp_radius : (99751536425589313/100000000000000000 : ℝ) ≤ Real.exp ((-4565/229376 : ℝ)/8) ∧ Real.exp ((-4565/229376 : ℝ)/8) ≤ (997515364255893131/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4565/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0485_exp_lower : (229522482937109233/250000000000000000 : ℝ) ≤ Real.exp ((-1367358852677/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367358852677/2000000000000 : ℝ)/8) ≤ (918089931748436933/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367358852677/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0485_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (16152203443/8000000000 : ℝ) ≤ 4*Real.exp (1141/8192 : ℝ)*Real.exp (-mu (radius 7 (4565/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (16152203443/8000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4565/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0485_exp_radius
  have hrNumeric : (980294913357/1000000000000 : ℝ) ≤ Real.exp (-4565/229376 : ℝ) ∧ Real.exp (-4565/229376 : ℝ) ≤ (490147456679/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980294913357/1000000000000 : ℝ) ≤ (radius 7 (4565/32768 : ℝ)) ∧ (radius 7 (4565/32768 : ℝ)) ≤ (490147456679/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4565/32768 : ℝ)) (980294913357/1000000000000 : ℝ) (490147456679/500000000000 : ℝ) (24692446607/125000000000 : ℝ) (98769786431/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4565/32768 : ℝ)) (980294913357/1000000000000 : ℝ) (490147456679/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4565/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980294913357/1000000000000 : ℝ) (490147456679/500000000000 : ℝ) (495073728339/500000000000 : ℝ) (990147456679/1000000000000 : ℝ) (198019687239/200000000000 : ℝ) (990098436197/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4565/32768 : ℝ)) 1 (495073728339/500000000000 : ℝ) (990147456679/1000000000000 : ℝ) (198019687239/200000000000 : ℝ) (990098436197/1000000000000 : ℝ) (247530736609/250000000000 : ℝ) (495061473219/500000000000 : ℝ) (990122946133/1000000000000 : ℝ) (198024589227/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4565/32768 : ℝ)) 2 (247530736609/250000000000 : ℝ) (495061473219/500000000000 : ℝ) (990122946133/1000000000000 : ℝ) (198024589227/200000000000 : ℝ) (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ) (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4565/32768 : ℝ)) 3 (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ) (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ) (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ) (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4565/32768 : ℝ)) 4 (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ) (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ) (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ) (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4565/32768 : ℝ)) 5 (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ) (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ) (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ) (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4565/32768 : ℝ)) 6 (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ) (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ) (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ) (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4565/32768 : ℝ)) 7 (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ) (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ) (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ) (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4565/32768 : ℝ))) (24692446607/125000000000 : ℝ) (98769786431/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4565/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24692446607/125000000000 : ℝ) (98769786431/500000000000 : ℝ) (149692446607/250000000000 : ℝ) (598769786431/1000000000000 : ℝ) (444454241577/1000000000000 : ℝ) (27778390099/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4565/32768 : ℝ))) 1 (149692446607/250000000000 : ℝ) (598769786431/1000000000000 : ℝ) (444454241577/1000000000000 : ℝ) (27778390099/62500000000 : ℝ) (260806007001/500000000000 : ℝ) (65201501751/125000000000 : ℝ) (515873793971/1000000000000 : ℝ) (515873793977/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4565/32768 : ℝ))) 2 (260806007001/500000000000 : ℝ) (65201501751/125000000000 : ℝ) (515873793971/1000000000000 : ℝ) (515873793977/1000000000000 : ℝ) (259371451993/500000000000 : ℝ) (518742903993/1000000000000 : ℝ) (518734969559/1000000000000 : ℝ) (259367484783/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4565/32768 : ℝ))) 3 (259371451993/500000000000 : ℝ) (518742903993/1000000000000 : ℝ) (518734969559/1000000000000 : ℝ) (259367484783/500000000000 : ℝ) (129684734193/250000000000 : ℝ) (25936946839/50000000000 : ℝ) (518738936757/1000000000000 : ℝ) (103747787353/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4565/32768 : ℝ))) 4 (129684734193/250000000000 : ℝ) (25936946839/50000000000 : ℝ) (518738936757/1000000000000 : ℝ) (103747787353/200000000000 : ℝ) (129684734191/250000000000 : ℝ) (518738936773/1000000000000 : ℝ) (129684734191/250000000000 : ℝ) (518738936773/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4565/32768 : ℝ))) 5 (129684734191/250000000000 : ℝ) (518738936773/1000000000000 : ℝ) (129684734191/250000000000 : ℝ) (518738936773/1000000000000 : ℝ) (129684734191/250000000000 : ℝ) (518738936773/1000000000000 : ℝ) (129684734191/250000000000 : ℝ) (518738936773/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4565/32768 : ℝ))) 6 (129684734191/250000000000 : ℝ) (518738936773/1000000000000 : ℝ) (129684734191/250000000000 : ℝ) (518738936773/1000000000000 : ℝ) (129684734191/250000000000 : ℝ) (518738936773/1000000000000 : ℝ) (129684734191/250000000000 : ℝ) (518738936773/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4565/32768 : ℝ))) 7 (129684734191/250000000000 : ℝ) (518738936773/1000000000000 : ℝ) (129684734191/250000000000 : ℝ) (518738936773/1000000000000 : ℝ) (129684734191/250000000000 : ℝ) (518738936773/1000000000000 : ℝ) (129684734191/250000000000 : ℝ) (518738936773/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4565/32768 : ℝ)) hmem 8 (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ) (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4565/32768 : ℝ))) hcmem 8 (129684734191/250000000000 : ℝ) (518738936773/1000000000000 : ℝ) (129684734191/250000000000 : ℝ) (518738936773/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4565/32768 : ℝ)) (247530736571/250000000000 : ℝ) (990122946287/1000000000000 : ℝ) (129684734191/250000000000 : ℝ) (518738936773/1000000000000 : ℝ) (822961652883/1000000000000 : ℝ) (822961652901/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0485_exp_lower
  have heNumeric : (16152203443/8000000000 : ℝ)/4 ≤ Real.exp (-1367358852677/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (16152203443/8000000000 : ℝ)/4 ≤ Real.exp ((1141/8192 : ℝ)-(822961652901/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1141/8192 : ℝ) (4565/32768 : ℝ) (822961652901/1000000000000 : ℝ) (16152203443/8000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0486; no trusted numerical premise.
theorem cover7_leaf0486_exp_radius : (249378705163327011/250000000000000000 : ℝ) ≤ Real.exp ((-2283/114688 : ℝ)/8) ∧ Real.exp ((-2283/114688 : ℝ)/8) ≤ (199502964130661609/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2283/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0486_exp_lower : (918089984094727363/1000000000000000000 : ℝ) ≤ Real.exp ((-5469431761651/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469431761651/8000000000000 : ℝ)/8) ≤ (229522496023681841/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469431761651/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0486_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019026351317/1000000000000 : ℝ) ≤ 4*Real.exp (4565/32768 : ℝ)*Real.exp (-mu (radius 7 (2283/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019026351317/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2283/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0486_exp_radius
  have hrNumeric : (980290639619/1000000000000 : ℝ) ≤ Real.exp (-2283/114688 : ℝ) ∧ Real.exp (-2283/114688 : ℝ) ≤ (49014531981/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980290639619/1000000000000 : ℝ) ≤ (radius 7 (2283/16384 : ℝ)) ∧ (radius 7 (2283/16384 : ℝ)) ≤ (49014531981/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2283/16384 : ℝ)) (980290639619/1000000000000 : ℝ) (49014531981/50000000000 : ℝ) (987803901/5000000000 : ℝ) (98780390103/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2283/16384 : ℝ)) (980290639619/1000000000000 : ℝ) (49014531981/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2283/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980290639619/1000000000000 : ℝ) (49014531981/50000000000 : ℝ) (990145319809/1000000000000 : ℝ) (99014531981/100000000000 : ℝ) (495048138977/500000000000 : ℝ) (198019255591/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2283/16384 : ℝ)) 1 (990145319809/1000000000000 : ℝ) (99014531981/100000000000 : ℝ) (495048138977/500000000000 : ℝ) (198019255591/200000000000 : ℝ) (990120798881/1000000000000 : ℝ) (990120798883/1000000000000 : ℝ) (990120798577/1000000000000 : ℝ) (990120798579/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2283/16384 : ℝ)) 2 (990120798881/1000000000000 : ℝ) (990120798883/1000000000000 : ℝ) (990120798577/1000000000000 : ℝ) (990120798579/1000000000000 : ℝ) (990120798729/1000000000000 : ℝ) (990120798731/1000000000000 : ℝ) (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2283/16384 : ℝ)) 3 (990120798729/1000000000000 : ℝ) (990120798731/1000000000000 : ℝ) (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ) (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ) (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2283/16384 : ℝ)) 4 (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ) (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ) (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ) (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2283/16384 : ℝ)) 5 (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ) (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ) (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ) (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2283/16384 : ℝ)) 6 (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ) (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ) (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ) (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2283/16384 : ℝ)) 7 (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ) (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ) (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ) (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2283/16384 : ℝ))) (987803901/5000000000 : ℝ) (98780390103/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2283/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (987803901/5000000000 : ℝ) (98780390103/500000000000 : ℝ) (5987803901/10000000000 : ℝ) (598780390103/1000000000000 : ℝ) (444478098673/1000000000000 : ℝ) (11111952467/25000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2283/16384 : ℝ))) 1 (5987803901/10000000000 : ℝ) (598780390103/1000000000000 : ℝ) (444478098673/1000000000000 : ℝ) (11111952467/25000000000 : ℝ) (260814622193/500000000000 : ℝ) (65203655549/125000000000 : ℝ) (128973051767/250000000000 : ℝ) (20635688283/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2283/16384 : ℝ))) 2 (260814622193/500000000000 : ℝ) (65203655549/125000000000 : ℝ) (128973051767/250000000000 : ℝ) (20635688283/40000000000 : ℝ) (518760725727/1000000000000 : ℝ) (259380362867/500000000000 : ℝ) (518752794843/1000000000000 : ℝ) (10375055897/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2283/16384 : ℝ))) 3 (518760725727/1000000000000 : ℝ) (259380362867/500000000000 : ℝ) (518752794843/1000000000000 : ℝ) (10375055897/20000000000 : ℝ) (103751352057/200000000000 : ℝ) (129689190073/250000000000 : ℝ) (518756760269/1000000000000 : ℝ) (518756760277/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2283/16384 : ℝ))) 4 (103751352057/200000000000 : ℝ) (129689190073/250000000000 : ℝ) (518756760269/1000000000000 : ℝ) (518756760277/1000000000000 : ℝ) (518756760277/1000000000000 : ℝ) (103751352057/200000000000 : ℝ) (129689190069/250000000000 : ℝ) (103751352057/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2283/16384 : ℝ))) 5 (518756760277/1000000000000 : ℝ) (103751352057/200000000000 : ℝ) (129689190069/250000000000 : ℝ) (103751352057/200000000000 : ℝ) (129689190069/250000000000 : ℝ) (103751352057/200000000000 : ℝ) (129689190069/250000000000 : ℝ) (103751352057/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2283/16384 : ℝ))) 6 (129689190069/250000000000 : ℝ) (103751352057/200000000000 : ℝ) (129689190069/250000000000 : ℝ) (103751352057/200000000000 : ℝ) (129689190069/250000000000 : ℝ) (103751352057/200000000000 : ℝ) (129689190069/250000000000 : ℝ) (103751352057/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2283/16384 : ℝ))) 7 (129689190069/250000000000 : ℝ) (103751352057/200000000000 : ℝ) (129689190069/250000000000 : ℝ) (103751352057/200000000000 : ℝ) (129689190069/250000000000 : ℝ) (103751352057/200000000000 : ℝ) (129689190069/250000000000 : ℝ) (103751352057/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2283/16384 : ℝ)) hmem 8 (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ) (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2283/16384 : ℝ))) hcmem 8 (129689190069/250000000000 : ℝ) (103751352057/200000000000 : ℝ) (129689190069/250000000000 : ℝ) (103751352057/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2283/16384 : ℝ)) (123765099841/125000000000 : ℝ) (990120798731/1000000000000 : ℝ) (129689190069/250000000000 : ℝ) (103751352057/200000000000 : ℝ) (82299171433/100000000000 : ℝ) (822991714347/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0486_exp_lower
  have heNumeric : (2019026351317/1000000000000 : ℝ)/4 ≤ Real.exp (-5469431761651/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019026351317/1000000000000 : ℝ)/4 ≤ Real.exp ((4565/32768 : ℝ)-(822991714347/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4565/32768 : ℝ) (2283/16384 : ℝ) (822991714347/1000000000000 : ℝ) (2019026351317/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0487; no trusted numerical premise.
theorem cover7_leaf0487_exp_radius : (997514277051019197/1000000000000000000 : ℝ) ≤ Real.exp ((-4567/229376 : ℝ)/8) ∧ Real.exp ((-4567/229376 : ℝ)/8) ≤ (498757138525509599/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4567/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0487_exp_lower : (36723601477788317/40000000000000000 : ℝ) ≤ Real.exp ((-2734714038741/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734714038741/4000000000000 : ℝ)/8) ≤ (459045018472353963/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734714038741/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0487_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009513640561/500000000000 : ℝ) ≤ 4*Real.exp (2283/16384 : ℝ)*Real.exp (-mu (radius 7 (4567/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009513640561/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4567/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0487_exp_radius
  have hrNumeric : (9802863659/10000000000 : ℝ) ≤ Real.exp (-4567/229376 : ℝ) ∧ Real.exp (-4567/229376 : ℝ) ≤ (980286365901/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (9802863659/10000000000 : ℝ) ≤ (radius 7 (4567/32768 : ℝ)) ∧ (radius 7 (4567/32768 : ℝ)) ≤ (980286365901/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4567/32768 : ℝ)) (9802863659/10000000000 : ℝ) (980286365901/1000000000000 : ℝ) (197581985081/1000000000000 : ℝ) (197581985087/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4567/32768 : ℝ)) (9802863659/10000000000 : ℝ) (980286365901/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4567/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (9802863659/10000000000 : ℝ) (980286365901/1000000000000 : ℝ) (19802863659/20000000000 : ℝ) (990143182951/1000000000000 : ℝ) (990094119717/1000000000000 : ℝ) (990094119719/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4567/32768 : ℝ)) 1 (19802863659/20000000000 : ℝ) (990143182951/1000000000000 : ℝ) (990094119717/1000000000000 : ℝ) (990094119719/1000000000000 : ℝ) (990118651333/1000000000000 : ℝ) (198023730267/200000000000 : ℝ) (990118651029/1000000000000 : ℝ) (123764831379/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4567/32768 : ℝ)) 2 (990118651333/1000000000000 : ℝ) (198023730267/200000000000 : ℝ) (990118651029/1000000000000 : ℝ) (123764831379/125000000000 : ℝ) (990118651181/1000000000000 : ℝ) (61882415699/62500000000 : ℝ) (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4567/32768 : ℝ)) 3 (990118651181/1000000000000 : ℝ) (61882415699/62500000000 : ℝ) (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ) (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ) (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4567/32768 : ℝ)) 4 (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ) (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ) (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ) (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4567/32768 : ℝ)) 5 (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ) (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ) (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ) (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4567/32768 : ℝ)) 6 (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ) (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ) (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ) (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4567/32768 : ℝ)) 7 (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ) (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ) (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ) (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4567/32768 : ℝ))) (197581985081/1000000000000 : ℝ) (197581985087/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4567/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (197581985081/1000000000000 : ℝ) (197581985087/1000000000000 : ℝ) (29939549627/50000000000 : ℝ) (18712218517/31250000000 : ℝ) (444501951717/1000000000000 : ℝ) (17780078069/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4567/32768 : ℝ))) 1 (29939549627/50000000000 : ℝ) (18712218517/31250000000 : ℝ) (444501951717/1000000000000 : ℝ) (17780078069/40000000000 : ℝ) (8150726127/15625000000 : ℝ) (104329294427/200000000000 : ℝ) (515910617117/1000000000000 : ℝ) (128977654281/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4567/32768 : ℝ))) 2 (8150726127/15625000000 : ℝ) (104329294427/200000000000 : ℝ) (515910617117/1000000000000 : ℝ) (128977654281/250000000000 : ℝ) (259389272311/500000000000 : ℝ) (51877854463/100000000000 : ℝ) (518770617279/1000000000000 : ℝ) (518770617287/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4567/32768 : ℝ))) 3 (259389272311/500000000000 : ℝ) (51877854463/100000000000 : ℝ) (518770617279/1000000000000 : ℝ) (518770617287/1000000000000 : ℝ) (10375491619/20000000000 : ℝ) (518774580959/1000000000000 : ℝ) (103754916187/200000000000 : ℝ) (32423411309/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4567/32768 : ℝ))) 4 (10375491619/20000000000 : ℝ) (518774580959/1000000000000 : ℝ) (103754916187/200000000000 : ℝ) (32423411309/62500000000 : ℝ) (259387290471/500000000000 : ℝ) (64846822619/125000000000 : ℝ) (259387290471/500000000000 : ℝ) (64846822619/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4567/32768 : ℝ))) 5 (259387290471/500000000000 : ℝ) (64846822619/125000000000 : ℝ) (259387290471/500000000000 : ℝ) (64846822619/125000000000 : ℝ) (259387290471/500000000000 : ℝ) (64846822619/125000000000 : ℝ) (259387290471/500000000000 : ℝ) (64846822619/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4567/32768 : ℝ))) 6 (259387290471/500000000000 : ℝ) (64846822619/125000000000 : ℝ) (259387290471/500000000000 : ℝ) (64846822619/125000000000 : ℝ) (259387290471/500000000000 : ℝ) (64846822619/125000000000 : ℝ) (259387290471/500000000000 : ℝ) (64846822619/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4567/32768 : ℝ))) 7 (259387290471/500000000000 : ℝ) (64846822619/125000000000 : ℝ) (259387290471/500000000000 : ℝ) (64846822619/125000000000 : ℝ) (259387290471/500000000000 : ℝ) (64846822619/125000000000 : ℝ) (259387290471/500000000000 : ℝ) (64846822619/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4567/32768 : ℝ)) hmem 8 (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ) (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4567/32768 : ℝ))) hcmem 8 (259387290471/500000000000 : ℝ) (64846822619/125000000000 : ℝ) (259387290471/500000000000 : ℝ) (64846822619/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4567/32768 : ℝ)) (49505932559/50000000000 : ℝ) (61882415699/62500000000 : ℝ) (259387290471/500000000000 : ℝ) (64846822619/125000000000 : ℝ) (102877721423/125000000000 : ℝ) (205755442851/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0487_exp_lower
  have heNumeric : (1009513640561/500000000000 : ℝ)/4 ≤ Real.exp (-2734714038741/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009513640561/500000000000 : ℝ)/4 ≤ Real.exp ((2283/16384 : ℝ)-(205755442851/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2283/16384 : ℝ) (4567/32768 : ℝ) (205755442851/250000000000 : ℝ) (1009513640561/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0488; no trusted numerical premise.
theorem cover7_leaf0488_exp_radius : (99751373344902659/100000000000000000 : ℝ) ≤ Real.exp ((-571/28672 : ℝ)/8) ∧ Real.exp ((-571/28672 : ℝ)/8) ≤ (997513733449026591/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-571/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0488_exp_lower : (918090090298608227/1000000000000000000 : ℝ) ≤ Real.exp ((-1093884871637/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093884871637/1600000000000 : ℝ)/8) ≤ (229522522574652057/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093884871637/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0488_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (126189263737/62500000000 : ℝ) ≤ 4*Real.exp (4567/32768 : ℝ)*Real.exp (-mu (radius 7 (571/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (126189263737/62500000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (571/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0488_exp_radius
  have hrNumeric : (4901410461/5000000000 : ℝ) ≤ Real.exp (-571/28672 : ℝ) ∧ Real.exp (-571/28672 : ℝ) ≤ (980282092201/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (4901410461/5000000000 : ℝ) ≤ (radius 7 (571/4096 : ℝ)) ∧ (radius 7 (571/4096 : ℝ)) ≤ (980282092201/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (571/4096 : ℝ)) (4901410461/5000000000 : ℝ) (980282092201/1000000000000 : ℝ) (197603187499/1000000000000 : ℝ) (39520637501/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (571/4096 : ℝ)) (4901410461/5000000000 : ℝ) (980282092201/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (571/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (4901410461/5000000000 : ℝ) (980282092201/1000000000000 : ℝ) (9901410461/10000000000 : ℝ) (990141046101/1000000000000 : ℝ) (495045980743/500000000000 : ℝ) (990091961487/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (571/4096 : ℝ)) 1 (9901410461/10000000000 : ℝ) (990141046101/1000000000000 : ℝ) (495045980743/500000000000 : ℝ) (990091961487/1000000000000 : ℝ) (990116503793/1000000000000 : ℝ) (495058251897/500000000000 : ℝ) (15470570367/15625000000 : ℝ) (99011650349/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (571/4096 : ℝ)) 2 (990116503793/1000000000000 : ℝ) (495058251897/500000000000 : ℝ) (15470570367/15625000000 : ℝ) (99011650349/100000000000 : ℝ) (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ) (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (571/4096 : ℝ)) 3 (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ) (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ) (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ) (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (571/4096 : ℝ)) 4 (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ) (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ) (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ) (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (571/4096 : ℝ)) 5 (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ) (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ) (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ) (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (571/4096 : ℝ)) 6 (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ) (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ) (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ) (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (571/4096 : ℝ)) 7 (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ) (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ) (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ) (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (571/4096 : ℝ))) (197603187499/1000000000000 : ℝ) (39520637501/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (571/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (197603187499/1000000000000 : ℝ) (39520637501/200000000000 : ℝ) (598801593749/1000000000000 : ℝ) (598801593753/1000000000000 : ℝ) (55565725089/125000000000 : ℝ) (5556572509/12500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (571/4096 : ℝ))) 1 (598801593749/1000000000000 : ℝ) (598801593753/1000000000000 : ℝ) (55565725089/125000000000 : ℝ) (5556572509/12500000000 : ℝ) (52166369723/100000000000 : ℝ) (521663697237/1000000000000 : ℝ) (515929024119/1000000000000 : ℝ) (257964512063/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (571/4096 : ℝ))) 2 (52166369723/100000000000 : ℝ) (521663697237/1000000000000 : ℝ) (515929024119/1000000000000 : ℝ) (257964512063/500000000000 : ℝ) (259398180337/500000000000 : ℝ) (259398180341/500000000000 : ℝ) (51878843687/100000000000 : ℝ) (259394218439/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (571/4096 : ℝ))) 3 (259398180337/500000000000 : ℝ) (259398180341/500000000000 : ℝ) (51878843687/100000000000 : ℝ) (259394218439/500000000000 : ℝ) (129698099693/250000000000 : ℝ) (25939619939/50000000000 : ℝ) (129698099689/250000000000 : ℝ) (103758479753/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (571/4096 : ℝ))) 4 (129698099693/250000000000 : ℝ) (25939619939/50000000000 : ℝ) (129698099689/250000000000 : ℝ) (103758479753/200000000000 : ℝ) (129698099691/250000000000 : ℝ) (518792398773/1000000000000 : ℝ) (518792398763/1000000000000 : ℝ) (518792398773/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (571/4096 : ℝ))) 5 (129698099691/250000000000 : ℝ) (518792398773/1000000000000 : ℝ) (518792398763/1000000000000 : ℝ) (518792398773/1000000000000 : ℝ) (518792398763/1000000000000 : ℝ) (518792398773/1000000000000 : ℝ) (518792398763/1000000000000 : ℝ) (518792398773/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (571/4096 : ℝ))) 6 (518792398763/1000000000000 : ℝ) (518792398773/1000000000000 : ℝ) (518792398763/1000000000000 : ℝ) (518792398773/1000000000000 : ℝ) (518792398763/1000000000000 : ℝ) (518792398773/1000000000000 : ℝ) (518792398763/1000000000000 : ℝ) (518792398773/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (571/4096 : ℝ))) 7 (518792398763/1000000000000 : ℝ) (518792398773/1000000000000 : ℝ) (518792398763/1000000000000 : ℝ) (518792398773/1000000000000 : ℝ) (518792398763/1000000000000 : ℝ) (518792398773/1000000000000 : ℝ) (518792398763/1000000000000 : ℝ) (518792398773/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (571/4096 : ℝ)) hmem 8 (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ) (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (571/4096 : ℝ))) hcmem 8 (518792398763/1000000000000 : ℝ) (518792398773/1000000000000 : ℝ) (518792398763/1000000000000 : ℝ) (518792398773/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (571/4096 : ℝ)) (24752912591/25000000000 : ℝ) (495058251821/500000000000 : ℝ) (518792398763/1000000000000 : ℝ) (518792398773/1000000000000 : ℝ) (823051824051/1000000000000 : ℝ) (82305182407/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0488_exp_lower
  have heNumeric : (126189263737/62500000000 : ℝ)/4 ≤ Real.exp (-1093884871637/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (126189263737/62500000000 : ℝ)/4 ≤ Real.exp ((4567/32768 : ℝ)-(82305182407/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4567/32768 : ℝ) (571/4096 : ℝ) (82305182407/100000000000 : ℝ) (126189263737/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0489; no trusted numerical premise.
theorem cover7_leaf0489_exp_radius : (498756594923665111/500000000000000000 : ℝ) ≤ Real.exp ((-4569/229376 : ℝ)/8) ∧ Real.exp ((-4569/229376 : ℝ)/8) ≤ (997513189847330223/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4569/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0489_exp_lower : (459045072078042037/500000000000000000 : ℝ) ≤ Real.exp ((-683677575473/1000000000000 : ℝ)/8) ∧ Real.exp ((-683677575473/1000000000000 : ℝ)/8) ≤ (36723605766243363/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683677575473/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0489_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019029167323/1000000000000 : ℝ) ≤ 4*Real.exp (571/4096 : ℝ)*Real.exp (-mu (radius 7 (4569/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019029167323/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4569/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0489_exp_radius
  have hrNumeric : (980277818519/1000000000000 : ℝ) ≤ Real.exp (-4569/229376 : ℝ) ∧ Real.exp (-4569/229376 : ℝ) ≤ (24506945463/25000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980277818519/1000000000000 : ℝ) ≤ (radius 7 (4569/32768 : ℝ)) ∧ (radius 7 (4569/32768 : ℝ)) ≤ (24506945463/25000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4569/32768 : ℝ)) (980277818519/1000000000000 : ℝ) (24506945463/25000000000 : ℝ) (1543940527/7812500000 : ℝ) (98812193731/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4569/32768 : ℝ)) (980277818519/1000000000000 : ℝ) (24506945463/25000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4569/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980277818519/1000000000000 : ℝ) (24506945463/25000000000 : ℝ) (990138909259/1000000000000 : ℝ) (49506945463/50000000000 : ℝ) (990089803259/1000000000000 : ℝ) (990089803261/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4569/32768 : ℝ)) 1 (990138909259/1000000000000 : ℝ) (49506945463/50000000000 : ℝ) (990089803259/1000000000000 : ℝ) (990089803261/1000000000000 : ℝ) (990114356259/1000000000000 : ℝ) (990114356261/1000000000000 : ℝ) (495057177977/500000000000 : ℝ) (990114355957/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4569/32768 : ℝ)) 2 (990114356259/1000000000000 : ℝ) (990114356261/1000000000000 : ℝ) (495057177977/500000000000 : ℝ) (990114355957/1000000000000 : ℝ) (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ) (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4569/32768 : ℝ)) 3 (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ) (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ) (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ) (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4569/32768 : ℝ)) 4 (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ) (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ) (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ) (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4569/32768 : ℝ)) 5 (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ) (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ) (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ) (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4569/32768 : ℝ)) 6 (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ) (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ) (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ) (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4569/32768 : ℝ)) 7 (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ) (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ) (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ) (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4569/32768 : ℝ))) (1543940527/7812500000 : ℝ) (98812193731/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4569/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1543940527/7812500000 : ℝ) (98812193731/500000000000 : ℝ) (9356440527/15625000000 : ℝ) (598812193731/1000000000000 : ℝ) (444549645659/1000000000000 : ℝ) (444549645667/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4569/32768 : ℝ))) 1 (9356440527/15625000000 : ℝ) (598812193731/1000000000000 : ℝ) (444549645659/1000000000000 : ℝ) (444549645667/1000000000000 : ℝ) (521680919693/1000000000000 : ℝ) (521680919699/1000000000000 : ℝ) (20637897123/40000000000 : ℝ) (257973714041/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4569/32768 : ℝ))) 2 (521680919693/1000000000000 : ℝ) (521680919699/1000000000000 : ℝ) (20637897123/40000000000 : ℝ) (257973714041/500000000000 : ℝ) (129703543471/250000000000 : ℝ) (518814173891/1000000000000 : ℝ) (32425390851/62500000000 : ℝ) (518806253623/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4569/32768 : ℝ))) 3 (129703543471/250000000000 : ℝ) (518814173891/1000000000000 : ℝ) (32425390851/62500000000 : ℝ) (518806253623/1000000000000 : ℝ) (415048171/800000000 : ℝ) (518810213757/1000000000000 : ℝ) (259405106867/500000000000 : ℝ) (259405106871/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4569/32768 : ℝ))) 4 (415048171/800000000 : ℝ) (518810213757/1000000000000 : ℝ) (259405106867/500000000000 : ℝ) (259405106871/500000000000 : ℝ) (259405106871/500000000000 : ℝ) (415048171/800000000 : ℝ) (518810213741/1000000000000 : ℝ) (415048171/800000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4569/32768 : ℝ))) 5 (259405106871/500000000000 : ℝ) (415048171/800000000 : ℝ) (518810213741/1000000000000 : ℝ) (415048171/800000000 : ℝ) (518810213741/1000000000000 : ℝ) (415048171/800000000 : ℝ) (518810213741/1000000000000 : ℝ) (415048171/800000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4569/32768 : ℝ))) 6 (518810213741/1000000000000 : ℝ) (415048171/800000000 : ℝ) (518810213741/1000000000000 : ℝ) (415048171/800000000 : ℝ) (518810213741/1000000000000 : ℝ) (415048171/800000000 : ℝ) (518810213741/1000000000000 : ℝ) (415048171/800000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4569/32768 : ℝ))) 7 (518810213741/1000000000000 : ℝ) (415048171/800000000 : ℝ) (518810213741/1000000000000 : ℝ) (415048171/800000000 : ℝ) (518810213741/1000000000000 : ℝ) (415048171/800000000 : ℝ) (518810213741/1000000000000 : ℝ) (415048171/800000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4569/32768 : ℝ)) hmem 8 (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ) (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4569/32768 : ℝ))) hcmem 8 (518810213741/1000000000000 : ℝ) (415048171/800000000 : ℝ) (518810213741/1000000000000 : ℝ) (415048171/800000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4569/32768 : ℝ)) (495057178053/500000000000 : ℝ) (990114356109/1000000000000 : ℝ) (518810213741/1000000000000 : ℝ) (415048171/800000000 : ℝ) (823081872331/1000000000000 : ℝ) (205770468087/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0489_exp_lower
  have heNumeric : (2019029167323/1000000000000 : ℝ)/4 ≤ Real.exp (-683677575473/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019029167323/1000000000000 : ℝ)/4 ≤ Real.exp ((571/4096 : ℝ)-(205770468087/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (571/4096 : ℝ) (4569/32768 : ℝ) (205770468087/250000000000 : ℝ) (2019029167323/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0490; no trusted numerical premise.
theorem cover7_leaf0490_exp_radius : (498756323122965047/500000000000000000 : ℝ) ≤ Real.exp ((-2285/114688 : ℝ)/8) ∧ Real.exp ((-2285/114688 : ℝ)/8) ≤ (199502529249186019/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2285/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0490_exp_lower : (918090198515528897/1000000000000000000 : ℝ) ≤ Real.exp ((-5469416814391/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469416814391/8000000000000 : ℝ)/8) ≤ (459045099257764449/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469416814391/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0490_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403806024737/200000000000 : ℝ) ≤ 4*Real.exp (4569/32768 : ℝ)*Real.exp (-mu (radius 7 (2285/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (403806024737/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2285/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0490_exp_radius
  have hrNumeric : (122534193107/125000000000 : ℝ) ≤ Real.exp (-2285/114688 : ℝ) ∧ Real.exp (-2285/114688 : ℝ) ≤ (980273544857/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122534193107/125000000000 : ℝ) ≤ (radius 7 (2285/16384 : ℝ)) ∧ (radius 7 (2285/16384 : ℝ)) ≤ (980273544857/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2285/16384 : ℝ)) (122534193107/125000000000 : ℝ) (980273544857/1000000000000 : ℝ) (98822792479/500000000000 : ℝ) (49411396241/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2285/16384 : ℝ)) (122534193107/125000000000 : ℝ) (980273544857/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2285/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122534193107/125000000000 : ℝ) (980273544857/1000000000000 : ℝ) (247534193107/250000000000 : ℝ) (990136772429/1000000000000 : ℝ) (990087645037/1000000000000 : ℝ) (990087645039/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2285/16384 : ℝ)) 1 (247534193107/250000000000 : ℝ) (990136772429/1000000000000 : ℝ) (990087645037/1000000000000 : ℝ) (990087645039/1000000000000 : ℝ) (247528052183/250000000000 : ℝ) (495056104367/500000000000 : ℝ) (990112208427/1000000000000 : ℝ) (99011220843/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2285/16384 : ℝ)) 2 (247528052183/250000000000 : ℝ) (495056104367/500000000000 : ℝ) (990112208427/1000000000000 : ℝ) (99011220843/100000000000 : ℝ) (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ) (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2285/16384 : ℝ)) 3 (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ) (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ) (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ) (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2285/16384 : ℝ)) 4 (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ) (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ) (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ) (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2285/16384 : ℝ)) 5 (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ) (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ) (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ) (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2285/16384 : ℝ)) 6 (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ) (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ) (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ) (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2285/16384 : ℝ)) 7 (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ) (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ) (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ) (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2285/16384 : ℝ))) (98822792479/500000000000 : ℝ) (49411396241/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2285/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98822792479/500000000000 : ℝ) (49411396241/250000000000 : ℝ) (598822792479/1000000000000 : ℝ) (299411396241/500000000000 : ℝ) (222286743283/500000000000 : ℝ) (222286743287/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2285/16384 : ℝ))) 1 (598822792479/1000000000000 : ℝ) (299411396241/500000000000 : ℝ) (222286743283/500000000000 : ℝ) (222286743287/500000000000 : ℝ) (260849069761/500000000000 : ℝ) (65212267441/125000000000 : ℝ) (4030983039/7812500000 : ℝ) (515965828999/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2285/16384 : ℝ))) 2 (260849069761/500000000000 : ℝ) (65212267441/125000000000 : ℝ) (4030983039/7812500000 : ℝ) (515965828999/1000000000000 : ℝ) (518831984257/1000000000000 : ℝ) (64853998033/125000000000 : ℝ) (518824067523/1000000000000 : ℝ) (518824067531/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2285/16384 : ℝ))) 3 (518831984257/1000000000000 : ℝ) (64853998033/125000000000 : ℝ) (518824067523/1000000000000 : ℝ) (518824067531/1000000000000 : ℝ) (51882802589/100000000000 : ℝ) (259414012949/500000000000 : ℝ) (259414012937/500000000000 : ℝ) (518828025883/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2285/16384 : ℝ))) 4 (51882802589/100000000000 : ℝ) (259414012949/500000000000 : ℝ) (259414012937/500000000000 : ℝ) (518828025883/1000000000000 : ℝ) (259414012941/500000000000 : ℝ) (518828025891/1000000000000 : ℝ) (518828025881/1000000000000 : ℝ) (518828025891/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2285/16384 : ℝ))) 5 (259414012941/500000000000 : ℝ) (518828025891/1000000000000 : ℝ) (518828025881/1000000000000 : ℝ) (518828025891/1000000000000 : ℝ) (518828025881/1000000000000 : ℝ) (518828025891/1000000000000 : ℝ) (518828025881/1000000000000 : ℝ) (518828025891/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2285/16384 : ℝ))) 6 (518828025881/1000000000000 : ℝ) (518828025891/1000000000000 : ℝ) (518828025881/1000000000000 : ℝ) (518828025891/1000000000000 : ℝ) (518828025881/1000000000000 : ℝ) (518828025891/1000000000000 : ℝ) (518828025881/1000000000000 : ℝ) (518828025891/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2285/16384 : ℝ))) 7 (518828025881/1000000000000 : ℝ) (518828025891/1000000000000 : ℝ) (518828025881/1000000000000 : ℝ) (518828025891/1000000000000 : ℝ) (518828025881/1000000000000 : ℝ) (518828025891/1000000000000 : ℝ) (518828025881/1000000000000 : ℝ) (518828025891/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2285/16384 : ℝ)) hmem 8 (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ) (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2285/16384 : ℝ))) hcmem 8 (518828025881/1000000000000 : ℝ) (518828025891/1000000000000 : ℝ) (518828025881/1000000000000 : ℝ) (518828025891/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2285/16384 : ℝ)) (990112208579/1000000000000 : ℝ) (495056104291/500000000000 : ℝ) (518828025881/1000000000000 : ℝ) (518828025891/1000000000000 : ℝ) (823111916233/1000000000000 : ℝ) (205777979063/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0490_exp_lower
  have heNumeric : (403806024737/200000000000 : ℝ)/4 ≤ Real.exp (-5469416814391/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403806024737/200000000000 : ℝ)/4 ≤ Real.exp ((4569/32768 : ℝ)-(205777979063/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4569/32768 : ℝ) (2285/16384 : ℝ) (205777979063/250000000000 : ℝ) (403806024737/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0491; no trusted numerical premise.
theorem cover7_leaf0491_exp_radius : (199502420528965241/200000000000000000 : ℝ) ≤ Real.exp ((-653/32768 : ℝ)/8) ∧ Real.exp ((-653/32768 : ℝ)/8) ≤ (498756051322413103/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-653/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0491_exp_lower : (918090253378549441/1000000000000000000 : ℝ) ≤ Real.exp ((-2734706494947/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734706494947/4000000000000 : ℝ)/8) ≤ (459045126689274721/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734706494947/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0491_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019031088907/1000000000000 : ℝ) ≤ 4*Real.exp (2285/16384 : ℝ)*Real.exp (-mu (radius 7 (4571/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019031088907/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4571/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0491_exp_radius
  have hrNumeric : (245067317803/250000000000 : ℝ) ≤ Real.exp (-653/32768 : ℝ) ∧ Real.exp (-653/32768 : ℝ) ≤ (980269271213/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245067317803/250000000000 : ℝ) ≤ (radius 7 (4571/32768 : ℝ)) ∧ (radius 7 (4571/32768 : ℝ)) ≤ (980269271213/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4571/32768 : ℝ)) (245067317803/250000000000 : ℝ) (980269271213/1000000000000 : ℝ) (197666779999/1000000000000 : ℝ) (39533356001/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4571/32768 : ℝ)) (245067317803/250000000000 : ℝ) (980269271213/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4571/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245067317803/250000000000 : ℝ) (980269271213/1000000000000 : ℝ) (495067317803/500000000000 : ℝ) (990134635607/1000000000000 : ℝ) (49504274341/50000000000 : ℝ) (990085486821/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4571/32768 : ℝ)) 1 (495067317803/500000000000 : ℝ) (990134635607/1000000000000 : ℝ) (49504274341/50000000000 : ℝ) (990085486821/1000000000000 : ℝ) (990110061213/1000000000000 : ℝ) (495055030607/500000000000 : ℝ) (247527515227/250000000000 : ℝ) (99011006091/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4571/32768 : ℝ)) 2 (990110061213/1000000000000 : ℝ) (495055030607/500000000000 : ℝ) (247527515227/250000000000 : ℝ) (99011006091/100000000000 : ℝ) (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ) (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4571/32768 : ℝ)) 3 (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ) (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ) (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ) (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4571/32768 : ℝ)) 4 (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ) (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ) (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ) (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4571/32768 : ℝ)) 5 (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ) (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ) (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ) (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4571/32768 : ℝ)) 6 (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ) (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ) (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ) (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4571/32768 : ℝ)) 7 (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ) (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ) (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ) (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4571/32768 : ℝ))) (197666779999/1000000000000 : ℝ) (39533356001/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4571/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (197666779999/1000000000000 : ℝ) (39533356001/200000000000 : ℝ) (598833389999/1000000000000 : ℝ) (598833390003/1000000000000 : ℝ) (444597323427/1000000000000 : ℝ) (88919464687/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4571/32768 : ℝ))) 1 (598833389999/1000000000000 : ℝ) (598833390003/1000000000000 : ℝ) (444597323427/1000000000000 : ℝ) (88919464687/200000000000 : ℝ) (521715356713/1000000000000 : ℝ) (521715356719/1000000000000 : ℝ) (515984226863/1000000000000 : ℝ) (515984226871/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4571/32768 : ℝ))) 2 (521715356713/1000000000000 : ℝ) (521715356719/1000000000000 : ℝ) (515984226863/1000000000000 : ℝ) (515984226871/1000000000000 : ℝ) (129712447947/250000000000 : ℝ) (103769958359/200000000000 : ℝ) (518841878587/1000000000000 : ℝ) (103768375719/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4571/32768 : ℝ))) 3 (129712447947/250000000000 : ℝ) (103769958359/200000000000 : ℝ) (518841878587/1000000000000 : ℝ) (103768375719/200000000000 : ℝ) (518845835187/1000000000000 : ℝ) (103769167039/200000000000 : ℝ) (129711458793/250000000000 : ℝ) (25942291759/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4571/32768 : ℝ))) 4 (518845835187/1000000000000 : ℝ) (103769167039/200000000000 : ℝ) (129711458793/250000000000 : ℝ) (25942291759/50000000000 : ℝ) (518845835179/1000000000000 : ℝ) (129711458797/250000000000 : ℝ) (518845835179/1000000000000 : ℝ) (129711458797/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4571/32768 : ℝ))) 5 (518845835179/1000000000000 : ℝ) (129711458797/250000000000 : ℝ) (518845835179/1000000000000 : ℝ) (129711458797/250000000000 : ℝ) (518845835179/1000000000000 : ℝ) (129711458797/250000000000 : ℝ) (518845835179/1000000000000 : ℝ) (129711458797/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4571/32768 : ℝ))) 6 (518845835179/1000000000000 : ℝ) (129711458797/250000000000 : ℝ) (518845835179/1000000000000 : ℝ) (129711458797/250000000000 : ℝ) (518845835179/1000000000000 : ℝ) (129711458797/250000000000 : ℝ) (518845835179/1000000000000 : ℝ) (129711458797/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4571/32768 : ℝ))) 7 (518845835179/1000000000000 : ℝ) (129711458797/250000000000 : ℝ) (518845835179/1000000000000 : ℝ) (129711458797/250000000000 : ℝ) (518845835179/1000000000000 : ℝ) (129711458797/250000000000 : ℝ) (518845835179/1000000000000 : ℝ) (129711458797/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4571/32768 : ℝ)) hmem 8 (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ) (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4571/32768 : ℝ))) hcmem 8 (518845835179/1000000000000 : ℝ) (129711458797/250000000000 : ℝ) (518845835179/1000000000000 : ℝ) (129711458797/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4571/32768 : ℝ)) (49505503053/50000000000 : ℝ) (495055030531/500000000000 : ℝ) (518845835179/1000000000000 : ℝ) (129711458797/250000000000 : ℝ) (823141955751/1000000000000 : ℝ) (102892744471/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0491_exp_lower
  have heNumeric : (2019031088907/1000000000000 : ℝ)/4 ≤ Real.exp (-2734706494947/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019031088907/1000000000000 : ℝ)/4 ≤ Real.exp ((2285/16384 : ℝ)-(102892744471/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2285/16384 : ℝ) (4571/32768 : ℝ) (102892744471/125000000000 : ℝ) (2019031088907/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0492; no trusted numerical premise.
theorem cover7_leaf0492_exp_radius : (199502311808803711/200000000000000000 : ℝ) ≤ Real.exp ((-1143/57344 : ℝ)/8) ∧ Real.exp ((-1143/57344 : ℝ)/8) ≤ (249377889761004639/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1143/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0492_exp_lower : (459045154371654809/500000000000000000 : ℝ) ≤ Real.exp ((-5469409130421/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469409130421/8000000000000 : ℝ)/8) ≤ (918090308743309619/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469409130421/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0492_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504758015739/250000000000 : ℝ) ≤ 4*Real.exp (4571/32768 : ℝ)*Real.exp (-mu (radius 7 (1143/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (504758015739/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1143/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0492_exp_radius
  have hrNumeric : (490132498793/500000000000 : ℝ) ≤ Real.exp (-1143/57344 : ℝ) ∧ Real.exp (-1143/57344 : ℝ) ≤ (980264997587/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490132498793/500000000000 : ℝ) ≤ (radius 7 (1143/8192 : ℝ)) ∧ (radius 7 (1143/8192 : ℝ)) ≤ (980264997587/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1143/8192 : ℝ)) (490132498793/500000000000 : ℝ) (980264997587/1000000000000 : ℝ) (197687972587/1000000000000 : ℝ) (197687972593/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1143/8192 : ℝ)) (490132498793/500000000000 : ℝ) (980264997587/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1143/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490132498793/500000000000 : ℝ) (980264997587/1000000000000 : ℝ) (990132498793/1000000000000 : ℝ) (495066249397/500000000000 : ℝ) (990083328607/1000000000000 : ℝ) (30940104019/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1143/8192 : ℝ)) 1 (990132498793/1000000000000 : ℝ) (495066249397/500000000000 : ℝ) (990083328607/1000000000000 : ℝ) (30940104019/31250000000 : ℝ) (9901079137/10000000000 : ℝ) (990107913701/1000000000000 : ℝ) (495053956697/500000000000 : ℝ) (247526978349/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1143/8192 : ℝ)) 2 (9901079137/10000000000 : ℝ) (990107913701/1000000000000 : ℝ) (495053956697/500000000000 : ℝ) (247526978349/250000000000 : ℝ) (990107913547/1000000000000 : ℝ) (990107913549/1000000000000 : ℝ) (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1143/8192 : ℝ)) 3 (990107913547/1000000000000 : ℝ) (990107913549/1000000000000 : ℝ) (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ) (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ) (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1143/8192 : ℝ)) 4 (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ) (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ) (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ) (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1143/8192 : ℝ)) 5 (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ) (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ) (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ) (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1143/8192 : ℝ)) 6 (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ) (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ) (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ) (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1143/8192 : ℝ)) 7 (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ) (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ) (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ) (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1143/8192 : ℝ))) (197687972587/1000000000000 : ℝ) (197687972593/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1143/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (197687972587/1000000000000 : ℝ) (197687972593/1000000000000 : ℝ) (598843986293/1000000000000 : ℝ) (598843986297/1000000000000 : ℝ) (111155289063/250000000000 : ℝ) (444621156259/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1143/8192 : ℝ))) 1 (598843986293/1000000000000 : ℝ) (598843986297/1000000000000 : ℝ) (111155289063/250000000000 : ℝ) (444621156259/1000000000000 : ℝ) (65216571409/125000000000 : ℝ) (260866285639/500000000000 : ℝ) (258001310849/500000000000 : ℝ) (103200524341/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1143/8192 : ℝ))) 2 (65216571409/125000000000 : ℝ) (260866285639/500000000000 : ℝ) (258001310849/500000000000 : ℝ) (103200524341/200000000000 : ℝ) (103773519297/200000000000 : ℝ) (129716899123/250000000000 : ℝ) (259429843407/500000000000 : ℝ) (259429843411/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1143/8192 : ℝ))) 3 (103773519297/200000000000 : ℝ) (129716899123/250000000000 : ℝ) (259429843407/500000000000 : ℝ) (259429843411/500000000000 : ℝ) (518863641649/1000000000000 : ℝ) (518863641657/1000000000000 : ℝ) (259431820817/500000000000 : ℝ) (259431820821/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1143/8192 : ℝ))) 4 (518863641649/1000000000000 : ℝ) (518863641657/1000000000000 : ℝ) (259431820817/500000000000 : ℝ) (259431820821/500000000000 : ℝ) (518863641641/1000000000000 : ℝ) (10377272833/20000000000 : ℝ) (518863641641/1000000000000 : ℝ) (10377272833/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1143/8192 : ℝ))) 5 (518863641641/1000000000000 : ℝ) (10377272833/20000000000 : ℝ) (518863641641/1000000000000 : ℝ) (10377272833/20000000000 : ℝ) (518863641641/1000000000000 : ℝ) (10377272833/20000000000 : ℝ) (518863641641/1000000000000 : ℝ) (10377272833/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1143/8192 : ℝ))) 6 (518863641641/1000000000000 : ℝ) (10377272833/20000000000 : ℝ) (518863641641/1000000000000 : ℝ) (10377272833/20000000000 : ℝ) (518863641641/1000000000000 : ℝ) (10377272833/20000000000 : ℝ) (518863641641/1000000000000 : ℝ) (10377272833/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1143/8192 : ℝ))) 7 (518863641641/1000000000000 : ℝ) (10377272833/20000000000 : ℝ) (518863641641/1000000000000 : ℝ) (10377272833/20000000000 : ℝ) (518863641641/1000000000000 : ℝ) (10377272833/20000000000 : ℝ) (518863641641/1000000000000 : ℝ) (10377272833/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1143/8192 : ℝ)) hmem 8 (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ) (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1143/8192 : ℝ))) hcmem 8 (518863641641/1000000000000 : ℝ) (10377272833/20000000000 : ℝ) (518863641641/1000000000000 : ℝ) (10377272833/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1143/8192 : ℝ)) (495053956773/500000000000 : ℝ) (990107913549/1000000000000 : ℝ) (518863641641/1000000000000 : ℝ) (10377272833/20000000000 : ℝ) (164634398179/200000000000 : ℝ) (6431031179/7812500000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0492_exp_lower
  have heNumeric : (504758015739/250000000000 : ℝ)/4 ≤ Real.exp (-5469409130421/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504758015739/250000000000 : ℝ)/4 ≤ Real.exp ((4571/32768 : ℝ)-(6431031179/7812500000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4571/32768 : ℝ) (1143/8192 : ℝ) (6431031179/7812500000 : ℝ) (504758015739/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0493; no trusted numerical premise.
theorem cover7_leaf0493_exp_radius : (997511015443507143/1000000000000000000 : ℝ) ≤ Real.exp ((-4573/229376 : ℝ)/8) ∧ Real.exp ((-4573/229376 : ℝ)/8) ≤ (124688876930438393/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4573/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0493_exp_lower : (91809036461084237/100000000000000000 : ℝ) ≤ Real.exp ((-54694052359/80000000000 : ℝ)/8) ∧ Real.exp ((-54694052359/80000000000 : ℝ)/8) ≤ (918090364610842371/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-54694052359/80000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0493_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504758261463/250000000000 : ℝ) ≤ 4*Real.exp (1143/8192 : ℝ)*Real.exp (-mu (radius 7 (4573/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (504758261463/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4573/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0493_exp_radius
  have hrNumeric : (980260723979/1000000000000 : ℝ) ≤ Real.exp (-4573/229376 : ℝ) ∧ Real.exp (-4573/229376 : ℝ) ≤ (49013036199/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980260723979/1000000000000 : ℝ) ≤ (radius 7 (4573/32768 : ℝ)) ∧ (radius 7 (4573/32768 : ℝ)) ≤ (49013036199/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4573/32768 : ℝ)) (980260723979/1000000000000 : ℝ) (49013036199/50000000000 : ℝ) (49427290679/250000000000 : ℝ) (98854581361/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4573/32768 : ℝ)) (980260723979/1000000000000 : ℝ) (49013036199/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4573/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980260723979/1000000000000 : ℝ) (49013036199/50000000000 : ℝ) (990130361989/1000000000000 : ℝ) (99013036199/100000000000 : ℝ) (990081170399/1000000000000 : ℝ) (1237601463/1250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4573/32768 : ℝ)) 1 (990130361989/1000000000000 : ℝ) (99013036199/100000000000 : ℝ) (990081170399/1000000000000 : ℝ) (1237601463/1250000000 : ℝ) (495052883097/500000000000 : ℝ) (198021153239/200000000000 : ℝ) (483450081/488281250 : ℝ) (99010576589/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4573/32768 : ℝ)) 2 (495052883097/500000000000 : ℝ) (198021153239/200000000000 : ℝ) (483450081/488281250 : ℝ) (99010576589/100000000000 : ℝ) (990105766041/1000000000000 : ℝ) (990105766043/1000000000000 : ℝ) (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4573/32768 : ℝ)) 3 (990105766041/1000000000000 : ℝ) (990105766043/1000000000000 : ℝ) (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ) (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ) (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4573/32768 : ℝ)) 4 (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ) (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ) (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ) (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4573/32768 : ℝ)) 5 (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ) (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ) (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ) (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4573/32768 : ℝ)) 6 (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ) (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ) (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ) (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4573/32768 : ℝ)) 7 (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ) (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ) (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ) (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4573/32768 : ℝ))) (49427290679/250000000000 : ℝ) (98854581361/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4573/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49427290679/250000000000 : ℝ) (98854581361/500000000000 : ℝ) (299427290679/500000000000 : ℝ) (598854581361/1000000000000 : ℝ) (222322492517/500000000000 : ℝ) (444644985041/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4573/32768 : ℝ))) 1 (299427290679/500000000000 : ℝ) (598854581361/1000000000000 : ℝ) (222322492517/500000000000 : ℝ) (444644985041/1000000000000 : ℝ) (130437445799/250000000000 : ℝ) (521749783201/1000000000000 : ℝ) (129005253373/250000000000 : ℝ) (258010506749/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4573/32768 : ℝ))) 2 (130437445799/250000000000 : ℝ) (521749783201/1000000000000 : ℝ) (129005253373/250000000000 : ℝ) (258010506749/500000000000 : ℝ) (64860674793/125000000000 : ℝ) (10377707967/20000000000 : ℝ) (259438746101/500000000000 : ℝ) (32429843263/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4573/32768 : ℝ))) 3 (64860674793/125000000000 : ℝ) (10377707967/20000000000 : ℝ) (259438746101/500000000000 : ℝ) (32429843263/62500000000 : ℝ) (518881445273/1000000000000 : ℝ) (518881445279/1000000000000 : ℝ) (518881445257/1000000000000 : ℝ) (32430090329/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4573/32768 : ℝ))) 4 (518881445273/1000000000000 : ℝ) (518881445279/1000000000000 : ℝ) (518881445257/1000000000000 : ℝ) (32430090329/62500000000 : ℝ) (103776289053/200000000000 : ℝ) (64860180659/125000000000 : ℝ) (32430090329/62500000000 : ℝ) (64860180659/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4573/32768 : ℝ))) 5 (103776289053/200000000000 : ℝ) (64860180659/125000000000 : ℝ) (32430090329/62500000000 : ℝ) (64860180659/125000000000 : ℝ) (32430090329/62500000000 : ℝ) (64860180659/125000000000 : ℝ) (32430090329/62500000000 : ℝ) (64860180659/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4573/32768 : ℝ))) 6 (32430090329/62500000000 : ℝ) (64860180659/125000000000 : ℝ) (32430090329/62500000000 : ℝ) (64860180659/125000000000 : ℝ) (32430090329/62500000000 : ℝ) (64860180659/125000000000 : ℝ) (32430090329/62500000000 : ℝ) (64860180659/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4573/32768 : ℝ))) 7 (32430090329/62500000000 : ℝ) (64860180659/125000000000 : ℝ) (32430090329/62500000000 : ℝ) (64860180659/125000000000 : ℝ) (32430090329/62500000000 : ℝ) (64860180659/125000000000 : ℝ) (32430090329/62500000000 : ℝ) (64860180659/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4573/32768 : ℝ)) hmem 8 (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ) (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4573/32768 : ℝ))) hcmem 8 (32430090329/62500000000 : ℝ) (64860180659/125000000000 : ℝ) (32430090329/62500000000 : ℝ) (64860180659/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4573/32768 : ℝ)) (24752644151/25000000000 : ℝ) (990105766043/1000000000000 : ℝ) (32430090329/62500000000 : ℝ) (64860180659/125000000000 : ℝ) (411601010829/500000000000 : ℝ) (32928080867/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0493_exp_lower
  have heNumeric : (504758261463/250000000000 : ℝ)/4 ≤ Real.exp (-54694052359/80000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504758261463/250000000000 : ℝ)/4 ≤ Real.exp ((1143/8192 : ℝ)-(32928080867/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1143/8192 : ℝ) (4573/32768 : ℝ) (32928080867/40000000000 : ℝ) (504758261463/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0494; no trusted numerical premise.
theorem cover7_leaf0494_exp_radius : (997510471843291971/1000000000000000000 : ℝ) ≤ Real.exp ((-2287/114688 : ℝ)/8) ∧ Real.exp ((-2287/114688 : ℝ)/8) ≤ (249377617960822993/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2287/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0494_exp_lower : (918090420980803503/1000000000000000000 : ℝ) ≤ Real.exp ((-1093880261271/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093880261271/1600000000000 : ℝ)/8) ≤ (57380651311300219/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093880261271/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0494_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019034037587/1000000000000 : ℝ) ≤ 4*Real.exp (4573/32768 : ℝ)*Real.exp (-mu (radius 7 (2287/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019034037587/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2287/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0494_exp_radius
  have hrNumeric : (980256450391/1000000000000 : ℝ) ≤ Real.exp (-2287/114688 : ℝ) ∧ Real.exp (-2287/114688 : ℝ) ≤ (122532056299/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980256450391/1000000000000 : ℝ) ≤ (radius 7 (2287/16384 : ℝ)) ∧ (radius 7 (2287/16384 : ℝ)) ≤ (122532056299/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2287/16384 : ℝ)) (980256450391/1000000000000 : ℝ) (122532056299/125000000000 : ℝ) (49432587597/250000000000 : ℝ) (98865175197/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2287/16384 : ℝ)) (980256450391/1000000000000 : ℝ) (122532056299/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2287/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980256450391/1000000000000 : ℝ) (122532056299/125000000000 : ℝ) (198025645039/200000000000 : ℝ) (247532056299/250000000000 : ℝ) (198015802439/200000000000 : ℝ) (990079012197/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2287/16384 : ℝ)) 1 (198025645039/200000000000 : ℝ) (247532056299/250000000000 : ℝ) (198015802439/200000000000 : ℝ) (990079012197/1000000000000 : ℝ) (198020723739/200000000000 : ℝ) (990103618697/1000000000000 : ℝ) (990103618389/1000000000000 : ℝ) (990103618391/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2287/16384 : ℝ)) 2 (198020723739/200000000000 : ℝ) (990103618697/1000000000000 : ℝ) (990103618389/1000000000000 : ℝ) (990103618391/1000000000000 : ℝ) (495051809271/500000000000 : ℝ) (61881476159/62500000000 : ℝ) (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2287/16384 : ℝ)) 3 (495051809271/500000000000 : ℝ) (61881476159/62500000000 : ℝ) (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ) (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ) (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2287/16384 : ℝ)) 4 (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ) (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ) (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ) (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2287/16384 : ℝ)) 5 (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ) (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ) (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ) (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2287/16384 : ℝ)) 6 (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ) (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ) (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ) (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2287/16384 : ℝ)) 7 (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ) (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ) (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ) (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2287/16384 : ℝ))) (49432587597/250000000000 : ℝ) (98865175197/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2287/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49432587597/250000000000 : ℝ) (98865175197/500000000000 : ℝ) (299432587597/500000000000 : ℝ) (598865175197/1000000000000 : ℝ) (27791800611/62500000000 : ℝ) (55583601223/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2287/16384 : ℝ))) 1 (299432587597/500000000000 : ℝ) (598865175197/1000000000000 : ℝ) (27791800611/62500000000 : ℝ) (55583601223/125000000000 : ℝ) (104353398497/200000000000 : ℝ) (521766992491/1000000000000 : ℝ) (103207880449/200000000000 : ℝ) (129009850563/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2287/16384 : ℝ))) 2 (104353398497/200000000000 : ℝ) (521766992491/1000000000000 : ℝ) (103207880449/200000000000 : ℝ) (129009850563/250000000000 : ℝ) (103780639473/200000000000 : ℝ) (129725799343/250000000000 : ℝ) (518895294749/1000000000000 : ℝ) (129723823689/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2287/16384 : ℝ))) 3 (103780639473/200000000000 : ℝ) (129725799343/250000000000 : ℝ) (518895294749/1000000000000 : ℝ) (129723823689/250000000000 : ℝ) (518899246057/1000000000000 : ℝ) (32431202879/62500000000 : ℝ) (518899246041/1000000000000 : ℝ) (518899246049/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2287/16384 : ℝ))) 4 (518899246057/1000000000000 : ℝ) (32431202879/62500000000 : ℝ) (518899246041/1000000000000 : ℝ) (518899246049/1000000000000 : ℝ) (518899246049/1000000000000 : ℝ) (518899246057/1000000000000 : ℝ) (16215601439/31250000000 : ℝ) (518899246057/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2287/16384 : ℝ))) 5 (518899246049/1000000000000 : ℝ) (518899246057/1000000000000 : ℝ) (16215601439/31250000000 : ℝ) (518899246057/1000000000000 : ℝ) (16215601439/31250000000 : ℝ) (518899246057/1000000000000 : ℝ) (16215601439/31250000000 : ℝ) (518899246057/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2287/16384 : ℝ))) 6 (16215601439/31250000000 : ℝ) (518899246057/1000000000000 : ℝ) (16215601439/31250000000 : ℝ) (518899246057/1000000000000 : ℝ) (16215601439/31250000000 : ℝ) (518899246057/1000000000000 : ℝ) (16215601439/31250000000 : ℝ) (518899246057/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2287/16384 : ℝ))) 7 (16215601439/31250000000 : ℝ) (518899246057/1000000000000 : ℝ) (16215601439/31250000000 : ℝ) (518899246057/1000000000000 : ℝ) (16215601439/31250000000 : ℝ) (518899246057/1000000000000 : ℝ) (16215601439/31250000000 : ℝ) (518899246057/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2287/16384 : ℝ)) hmem 8 (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ) (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2287/16384 : ℝ))) hcmem 8 (16215601439/31250000000 : ℝ) (518899246057/1000000000000 : ℝ) (16215601439/31250000000 : ℝ) (518899246057/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2287/16384 : ℝ)) (990103618541/1000000000000 : ℝ) (61881476159/62500000000 : ℝ) (16215601439/31250000000 : ℝ) (518899246057/1000000000000 : ℝ) (823232048043/1000000000000 : ℝ) (41161602403/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0494_exp_lower
  have heNumeric : (2019034037587/1000000000000 : ℝ)/4 ≤ Real.exp (-1093880261271/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019034037587/1000000000000 : ℝ)/4 ≤ Real.exp ((4573/32768 : ℝ)-(41161602403/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4573/32768 : ℝ) (2287/16384 : ℝ) (41161602403/50000000000 : ℝ) (2019034037587/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0495; no trusted numerical premise.
theorem cover7_leaf0495_exp_radius : (997509928243373037/1000000000000000000 : ℝ) ≤ Real.exp ((-4575/229376 : ℝ)/8) ∧ Real.exp ((-4575/229376 : ℝ)/8) ≤ (498754964121686519/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4575/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0495_exp_lower : (918090477852963589/1000000000000000000 : ℝ) ≤ Real.exp ((-2734698670901/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734698670901/4000000000000 : ℝ)/8) ≤ (91809047785296359/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734698670901/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0495_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019035038159/1000000000000 : ℝ) ≤ 4*Real.exp (2287/16384 : ℝ)*Real.exp (-mu (radius 7 (4575/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019035038159/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4575/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0495_exp_radius
  have hrNumeric : (490126088411/500000000000 : ℝ) ≤ Real.exp (-4575/229376 : ℝ) ∧ Real.exp (-4575/229376 : ℝ) ≤ (980252176823/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490126088411/500000000000 : ℝ) ≤ (radius 7 (4575/32768 : ℝ)) ∧ (radius 7 (4575/32768 : ℝ)) ≤ (980252176823/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4575/32768 : ℝ)) (490126088411/500000000000 : ℝ) (980252176823/1000000000000 : ℝ) (49437883901/250000000000 : ℝ) (19775153561/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4575/32768 : ℝ)) (490126088411/500000000000 : ℝ) (980252176823/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4575/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490126088411/500000000000 : ℝ) (980252176823/1000000000000 : ℝ) (990126088411/1000000000000 : ℝ) (247531522103/250000000000 : ℝ) (990076853997/1000000000000 : ℝ) (990076853999/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4575/32768 : ℝ)) 1 (990126088411/1000000000000 : ℝ) (247531522103/250000000000 : ℝ) (990076853997/1000000000000 : ℝ) (990076853999/1000000000000 : ℝ) (247525367801/250000000000 : ℝ) (495050735603/500000000000 : ℝ) (990101470897/1000000000000 : ℝ) (9901014709/10000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4575/32768 : ℝ)) 2 (247525367801/250000000000 : ℝ) (495050735603/500000000000 : ℝ) (990101470897/1000000000000 : ℝ) (9901014709/10000000000 : ℝ) (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ) (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4575/32768 : ℝ)) 3 (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ) (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ) (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ) (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4575/32768 : ℝ)) 4 (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ) (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ) (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ) (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4575/32768 : ℝ)) 5 (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ) (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ) (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ) (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4575/32768 : ℝ)) 6 (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ) (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ) (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ) (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4575/32768 : ℝ)) 7 (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ) (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ) (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ) (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4575/32768 : ℝ))) (49437883901/250000000000 : ℝ) (19775153561/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4575/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49437883901/250000000000 : ℝ) (19775153561/100000000000 : ℝ) (299437883901/500000000000 : ℝ) (119775153561/200000000000 : ℝ) (5558657881/12500000000 : ℝ) (55586578811/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4575/32768 : ℝ))) 1 (299437883901/500000000000 : ℝ) (119775153561/200000000000 : ℝ) (5558657881/12500000000 : ℝ) (55586578811/125000000000 : ℝ) (521784199141/1000000000000 : ℝ) (521784199147/1000000000000 : ℝ) (12901444699/25000000000 : ℝ) (516057787967/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4575/32768 : ℝ))) 2 (521784199141/1000000000000 : ℝ) (521784199147/1000000000000 : ℝ) (12901444699/25000000000 : ℝ) (516057787967/1000000000000 : ℝ) (10378419871/20000000000 : ℝ) (518920993557/1000000000000 : ℝ) (518913094459/1000000000000 : ℝ) (259456547233/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4575/32768 : ℝ))) 3 (10378419871/20000000000 : ℝ) (518920993557/1000000000000 : ℝ) (518913094459/1000000000000 : ℝ) (259456547233/500000000000 : ℝ) (129729261001/250000000000 : ℝ) (129729261003/250000000000 : ℝ) (518917043989/1000000000000 : ℝ) (518917043997/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4575/32768 : ℝ))) 4 (129729261001/250000000000 : ℝ) (129729261003/250000000000 : ℝ) (518917043989/1000000000000 : ℝ) (518917043997/1000000000000 : ℝ) (129729260999/250000000000 : ℝ) (103783408801/200000000000 : ℝ) (129729260999/250000000000 : ℝ) (103783408801/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4575/32768 : ℝ))) 5 (129729260999/250000000000 : ℝ) (103783408801/200000000000 : ℝ) (129729260999/250000000000 : ℝ) (103783408801/200000000000 : ℝ) (129729260999/250000000000 : ℝ) (103783408801/200000000000 : ℝ) (129729260999/250000000000 : ℝ) (103783408801/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4575/32768 : ℝ))) 6 (129729260999/250000000000 : ℝ) (103783408801/200000000000 : ℝ) (129729260999/250000000000 : ℝ) (103783408801/200000000000 : ℝ) (129729260999/250000000000 : ℝ) (103783408801/200000000000 : ℝ) (129729260999/250000000000 : ℝ) (103783408801/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4575/32768 : ℝ))) 7 (129729260999/250000000000 : ℝ) (103783408801/200000000000 : ℝ) (129729260999/250000000000 : ℝ) (103783408801/200000000000 : ℝ) (129729260999/250000000000 : ℝ) (103783408801/200000000000 : ℝ) (129729260999/250000000000 : ℝ) (103783408801/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4575/32768 : ℝ)) hmem 8 (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ) (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4575/32768 : ℝ))) hcmem 8 (129729260999/250000000000 : ℝ) (103783408801/200000000000 : ℝ) (129729260999/250000000000 : ℝ) (103783408801/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4575/32768 : ℝ)) (19802029421/20000000000 : ℝ) (990101471053/1000000000000 : ℝ) (129729260999/250000000000 : ℝ) (103783408801/200000000000 : ℝ) (823262070051/1000000000000 : ℝ) (823262070069/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0495_exp_lower
  have heNumeric : (2019035038159/1000000000000 : ℝ)/4 ≤ Real.exp (-2734698670901/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019035038159/1000000000000 : ℝ)/4 ≤ Real.exp ((2287/16384 : ℝ)-(823262070069/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2287/16384 : ℝ) (4575/32768 : ℝ) (823262070069/1000000000000 : ℝ) (2019035038159/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0496; no trusted numerical premise.
theorem cover7_leaf0496_exp_radius : (997509384643750341/1000000000000000000 : ℝ) ≤ Real.exp ((-143/7168 : ℝ)/8) ∧ Real.exp ((-143/7168 : ℝ)/8) ≤ (498754692321875171/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-143/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0496_exp_lower : (918090535226634153/1000000000000000000 : ℝ) ≤ Real.exp ((-5469393342289/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469393342289/8000000000000 : ℝ)/8) ≤ (459045267613317077/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469393342289/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0496_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019036047553/1000000000000 : ℝ) ≤ 4*Real.exp (4575/32768 : ℝ)*Real.exp (-mu (radius 7 (143/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (2019036047553/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (143/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0496_exp_radius
  have hrNumeric : (980247903271/1000000000000 : ℝ) ≤ Real.exp (-143/7168 : ℝ) ∧ Real.exp (-143/7168 : ℝ) ≤ (122530987909/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980247903271/1000000000000 : ℝ) ≤ (radius 7 (143/1024 : ℝ)) ∧ (radius 7 (143/1024 : ℝ)) ≤ (122530987909/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (143/1024 : ℝ)) (980247903271/1000000000000 : ℝ) (122530987909/125000000000 : ℝ) (6180397449/31250000000 : ℝ) (98886359187/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (143/1024 : ℝ)) (980247903271/1000000000000 : ℝ) (122530987909/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (143/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980247903271/1000000000000 : ℝ) (122530987909/125000000000 : ℝ) (198024790327/200000000000 : ℝ) (247530987909/250000000000 : ℝ) (990074695803/1000000000000 : ℝ) (198014939161/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (143/1024 : ℝ)) 1 (198024790327/200000000000 : ℝ) (247530987909/250000000000 : ℝ) (990074695803/1000000000000 : ℝ) (198014939161/200000000000 : ℝ) (990099323719/1000000000000 : ℝ) (990099323721/1000000000000 : ℝ) (247524830853/250000000000 : ℝ) (198019864683/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (143/1024 : ℝ)) 2 (990099323719/1000000000000 : ℝ) (990099323721/1000000000000 : ℝ) (247524830853/250000000000 : ℝ) (198019864683/200000000000 : ℝ) (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ) (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (143/1024 : ℝ)) 3 (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ) (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ) (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ) (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (143/1024 : ℝ)) 4 (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ) (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ) (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ) (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (143/1024 : ℝ)) 5 (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ) (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ) (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ) (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (143/1024 : ℝ)) 6 (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ) (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ) (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ) (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (143/1024 : ℝ)) 7 (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ) (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ) (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ) (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (143/1024 : ℝ))) (6180397449/31250000000 : ℝ) (98886359187/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (143/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (6180397449/31250000000 : ℝ) (98886359187/500000000000 : ℝ) (37430397449/62500000000 : ℝ) (598886359187/1000000000000 : ℝ) (27794777947/62500000000 : ℝ) (11117911179/25000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (143/1024 : ℝ))) 1 (37430397449/62500000000 : ℝ) (598886359187/1000000000000 : ℝ) (27794777947/62500000000 : ℝ) (11117911179/25000000000 : ℝ) (16306293849/31250000000 : ℝ) (260900701587/500000000000 : ℝ) (516076170641/1000000000000 : ℝ) (64509521331/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (143/1024 : ℝ))) 2 (16306293849/31250000000 : ℝ) (260900701587/500000000000 : ℝ) (516076170641/1000000000000 : ℝ) (64509521331/125000000000 : ℝ) (64867348363/125000000000 : ℝ) (518938786911/1000000000000 : ℝ) (103786178267/200000000000 : ℝ) (259465445671/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (143/1024 : ℝ))) 3 (64867348363/125000000000 : ℝ) (518938786911/1000000000000 : ℝ) (103786178267/200000000000 : ℝ) (259465445671/500000000000 : ℝ) (518934839119/1000000000000 : ℝ) (518934839127/1000000000000 : ℝ) (8108356861/15625000000 : ℝ) (64866854889/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (143/1024 : ℝ))) 4 (518934839119/1000000000000 : ℝ) (518934839127/1000000000000 : ℝ) (8108356861/15625000000 : ℝ) (64866854889/125000000000 : ℝ) (518934839111/1000000000000 : ℝ) (6486685489/12500000000 : ℝ) (518934839111/1000000000000 : ℝ) (6486685489/12500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (143/1024 : ℝ))) 5 (518934839111/1000000000000 : ℝ) (6486685489/12500000000 : ℝ) (518934839111/1000000000000 : ℝ) (6486685489/12500000000 : ℝ) (518934839111/1000000000000 : ℝ) (6486685489/12500000000 : ℝ) (518934839111/1000000000000 : ℝ) (6486685489/12500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (143/1024 : ℝ))) 6 (518934839111/1000000000000 : ℝ) (6486685489/12500000000 : ℝ) (518934839111/1000000000000 : ℝ) (6486685489/12500000000 : ℝ) (518934839111/1000000000000 : ℝ) (6486685489/12500000000 : ℝ) (518934839111/1000000000000 : ℝ) (6486685489/12500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (143/1024 : ℝ))) 7 (518934839111/1000000000000 : ℝ) (6486685489/12500000000 : ℝ) (518934839111/1000000000000 : ℝ) (6486685489/12500000000 : ℝ) (518934839111/1000000000000 : ℝ) (6486685489/12500000000 : ℝ) (518934839111/1000000000000 : ℝ) (6486685489/12500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (143/1024 : ℝ)) hmem 8 (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ) (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (143/1024 : ℝ))) hcmem 8 (518934839111/1000000000000 : ℝ) (6486685489/12500000000 : ℝ) (518934839111/1000000000000 : ℝ) (6486685489/12500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (143/1024 : ℝ)) (198019864713/200000000000 : ℝ) (61881207723/62500000000 : ℝ) (518934839111/1000000000000 : ℝ) (6486685489/12500000000 : ℝ) (82329208769/100000000000 : ℝ) (205823021927/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0496_exp_lower
  have heNumeric : (2019036047553/1000000000000 : ℝ)/4 ≤ Real.exp (-5469393342289/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019036047553/1000000000000 : ℝ)/4 ≤ Real.exp ((4575/32768 : ℝ)-(205823021927/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4575/32768 : ℝ) (143/1024 : ℝ) (205823021927/250000000000 : ℝ) (2019036047553/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0497; no trusted numerical premise.
theorem cover7_leaf0497_exp_radius : (249377210261105971/250000000000000000 : ℝ) ≤ Real.exp ((-4577/229376 : ℝ)/8) ∧ Real.exp ((-4577/229376 : ℝ)/8) ≤ (199501768208884777/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4577/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0497_exp_lower : (183618118620294201/200000000000000000 : ℝ) ≤ Real.exp ((-17091841587/25000000000 : ℝ)/8) ∧ Real.exp ((-17091841587/25000000000 : ℝ)/8) ≤ (459045296550735503/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17091841587/25000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0497_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009518532883/500000000000 : ℝ) ≤ 4*Real.exp (143/1024 : ℝ)*Real.exp (-mu (radius 7 (4577/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009518532883/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4577/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0497_exp_radius
  have hrNumeric : (490121814869/500000000000 : ℝ) ≤ Real.exp (-4577/229376 : ℝ) ∧ Real.exp (-4577/229376 : ℝ) ≤ (980243629739/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490121814869/500000000000 : ℝ) ≤ (radius 7 (4577/32768 : ℝ)) ∧ (radius 7 (4577/32768 : ℝ)) ≤ (980243629739/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4577/32768 : ℝ)) (490121814869/500000000000 : ℝ) (980243629739/1000000000000 : ℝ) (98896949341/500000000000 : ℝ) (3090529667/15625000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4577/32768 : ℝ)) (490121814869/500000000000 : ℝ) (980243629739/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4577/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490121814869/500000000000 : ℝ) (980243629739/1000000000000 : ℝ) (990121814869/1000000000000 : ℝ) (99012181487/100000000000 : ℝ) (495036268807/500000000000 : ℝ) (198014507523/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4577/32768 : ℝ)) 1 (990121814869/1000000000000 : ℝ) (99012181487/100000000000 : ℝ) (495036268807/500000000000 : ℝ) (198014507523/200000000000 : ℝ) (990097176241/1000000000000 : ℝ) (990097176243/1000000000000 : ℝ) (495048587967/500000000000 : ℝ) (7735134187/7812500000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4577/32768 : ℝ)) 2 (990097176241/1000000000000 : ℝ) (990097176243/1000000000000 : ℝ) (495048587967/500000000000 : ℝ) (7735134187/7812500000 : ℝ) (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ) (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4577/32768 : ℝ)) 3 (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ) (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ) (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ) (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4577/32768 : ℝ)) 4 (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ) (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ) (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ) (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4577/32768 : ℝ)) 5 (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ) (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ) (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ) (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4577/32768 : ℝ)) 6 (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ) (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ) (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ) (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4577/32768 : ℝ)) 7 (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ) (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ) (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ) (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4577/32768 : ℝ))) (98896949341/500000000000 : ℝ) (3090529667/15625000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4577/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98896949341/500000000000 : ℝ) (3090529667/15625000000 : ℝ) (598896949341/1000000000000 : ℝ) (18715529667/31250000000 : ℝ) (222370129897/500000000000 : ℝ) (222370129901/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4577/32768 : ℝ))) 1 (598896949341/1000000000000 : ℝ) (18715529667/31250000000 : ℝ) (222370129897/500000000000 : ℝ) (222370129901/500000000000 : ℝ) (521818604567/1000000000000 : ℝ) (521818604573/1000000000000 : ℝ) (51609455029/100000000000 : ℝ) (516094550297/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4577/32768 : ℝ))) 2 (521818604567/1000000000000 : ℝ) (521818604573/1000000000000 : ℝ) (51609455029/100000000000 : ℝ) (516094550297/1000000000000 : ℝ) (129739144357/250000000000 : ℝ) (103791315487/200000000000 : ℝ) (518948685379/1000000000000 : ℝ) (259474342693/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4577/32768 : ℝ))) 3 (129739144357/250000000000 : ℝ) (103791315487/200000000000 : ℝ) (518948685379/1000000000000 : ℝ) (259474342693/500000000000 : ℝ) (518952631403/1000000000000 : ℝ) (518952631411/1000000000000 : ℝ) (129738157847/250000000000 : ℝ) (129738157849/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4577/32768 : ℝ))) 4 (518952631403/1000000000000 : ℝ) (518952631411/1000000000000 : ℝ) (129738157847/250000000000 : ℝ) (129738157849/250000000000 : ℝ) (103790526279/200000000000 : ℝ) (129738157851/250000000000 : ℝ) (103790526279/200000000000 : ℝ) (129738157851/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4577/32768 : ℝ))) 5 (103790526279/200000000000 : ℝ) (129738157851/250000000000 : ℝ) (103790526279/200000000000 : ℝ) (129738157851/250000000000 : ℝ) (103790526279/200000000000 : ℝ) (129738157851/250000000000 : ℝ) (103790526279/200000000000 : ℝ) (129738157851/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4577/32768 : ℝ))) 6 (103790526279/200000000000 : ℝ) (129738157851/250000000000 : ℝ) (103790526279/200000000000 : ℝ) (129738157851/250000000000 : ℝ) (103790526279/200000000000 : ℝ) (129738157851/250000000000 : ℝ) (103790526279/200000000000 : ℝ) (129738157851/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4577/32768 : ℝ))) 7 (103790526279/200000000000 : ℝ) (129738157851/250000000000 : ℝ) (103790526279/200000000000 : ℝ) (129738157851/250000000000 : ℝ) (103790526279/200000000000 : ℝ) (129738157851/250000000000 : ℝ) (103790526279/200000000000 : ℝ) (129738157851/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4577/32768 : ℝ)) hmem 8 (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ) (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4577/32768 : ℝ))) hcmem 8 (103790526279/200000000000 : ℝ) (129738157851/250000000000 : ℝ) (103790526279/200000000000 : ℝ) (129738157851/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4577/32768 : ℝ)) (990097176087/1000000000000 : ℝ) (99009717609/100000000000 : ℝ) (103790526279/200000000000 : ℝ) (129738157851/250000000000 : ℝ) (411661050481/500000000000 : ℝ) (41166105049/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0497_exp_lower
  have heNumeric : (1009518532883/500000000000 : ℝ)/4 ≤ Real.exp (-17091841587/25000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009518532883/500000000000 : ℝ)/4 ≤ Real.exp ((143/1024 : ℝ)-(41166105049/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (143/1024 : ℝ) (4577/32768 : ℝ) (41166105049/50000000000 : ℝ) (1009518532883/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0498; no trusted numerical premise.
theorem cover7_leaf0498_exp_radius : (3896516786896069/3906250000000000 : ℝ) ≤ Real.exp ((-327/16384 : ℝ)/8) ∧ Real.exp ((-327/16384 : ℝ)/8) ≤ (199501659489078733/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-327/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0498_exp_lower : (918090651477818523/1000000000000000000 : ℝ) ≤ Real.exp ((-5469385238431/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469385238431/8000000000000 : ℝ)/8) ≤ (229522662869454631/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469385238431/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0498_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009519046401/500000000000 : ℝ) ≤ 4*Real.exp (4577/32768 : ℝ)*Real.exp (-mu (radius 7 (2289/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (1009519046401/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2289/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0498_exp_radius
  have hrNumeric : (15316239941/15625000000 : ℝ) ≤ Real.exp (-327/16384 : ℝ) ∧ Real.exp (-327/16384 : ℝ) ≤ (39209574249/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (15316239941/15625000000 : ℝ) ≤ (radius 7 (2289/16384 : ℝ)) ∧ (radius 7 (2289/16384 : ℝ)) ≤ (39209574249/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2289/16384 : ℝ)) (15316239941/15625000000 : ℝ) (39209574249/40000000000 : ℝ) (98907538271/500000000000 : ℝ) (49453769137/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2289/16384 : ℝ)) (15316239941/15625000000 : ℝ) (39209574249/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2289/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (15316239941/15625000000 : ℝ) (39209574249/40000000000 : ℝ) (30941239941/31250000000 : ℝ) (990119678113/1000000000000 : ℝ) (990070379429/1000000000000 : ℝ) (990070379431/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2289/16384 : ℝ)) 1 (30941239941/31250000000 : ℝ) (990119678113/1000000000000 : ℝ) (990070379429/1000000000000 : ℝ) (990070379431/1000000000000 : ℝ) (99009502877/100000000000 : ℝ) (247523757193/250000000000 : ℝ) (990095028463/1000000000000 : ℝ) (495047514233/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2289/16384 : ℝ)) 2 (99009502877/100000000000 : ℝ) (247523757193/250000000000 : ℝ) (990095028463/1000000000000 : ℝ) (495047514233/500000000000 : ℝ) (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ) (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2289/16384 : ℝ)) 3 (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ) (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ) (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ) (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2289/16384 : ℝ)) 4 (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ) (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ) (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ) (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2289/16384 : ℝ)) 5 (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ) (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ) (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ) (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2289/16384 : ℝ)) 6 (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ) (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ) (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ) (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2289/16384 : ℝ)) 7 (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ) (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ) (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ) (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2289/16384 : ℝ))) (98907538271/500000000000 : ℝ) (49453769137/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2289/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (98907538271/500000000000 : ℝ) (49453769137/250000000000 : ℝ) (598907538271/1000000000000 : ℝ) (299453769137/500000000000 : ℝ) (222382034201/500000000000 : ℝ) (44476406841/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2289/16384 : ℝ))) 1 (598907538271/1000000000000 : ℝ) (299453769137/500000000000 : ℝ) (222382034201/500000000000 : ℝ) (44476406841/100000000000 : ℝ) (65229475417/125000000000 : ℝ) (260917901671/500000000000 : ℝ) (64514115863/125000000000 : ℝ) (516112926911/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2289/16384 : ℝ))) 2 (65229475417/125000000000 : ℝ) (260917901671/500000000000 : ℝ) (64514115863/125000000000 : ℝ) (516112926911/1000000000000 : ℝ) (1621794891/3125000000 : ℝ) (518974365127/1000000000000 : ℝ) (129741619147/250000000000 : ℝ) (129741619149/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2289/16384 : ℝ))) 3 (1621794891/3125000000 : ℝ) (518974365127/1000000000000 : ℝ) (129741619147/250000000000 : ℝ) (129741619149/250000000000 : ℝ) (259485210427/500000000000 : ℝ) (259485210431/500000000000 : ℝ) (518970420839/1000000000000 : ℝ) (518970420847/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2289/16384 : ℝ))) 4 (259485210427/500000000000 : ℝ) (259485210431/500000000000 : ℝ) (518970420839/1000000000000 : ℝ) (518970420847/1000000000000 : ℝ) (259485210423/500000000000 : ℝ) (103794084171/200000000000 : ℝ) (259485210423/500000000000 : ℝ) (103794084171/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2289/16384 : ℝ))) 5 (259485210423/500000000000 : ℝ) (103794084171/200000000000 : ℝ) (259485210423/500000000000 : ℝ) (103794084171/200000000000 : ℝ) (259485210423/500000000000 : ℝ) (103794084171/200000000000 : ℝ) (259485210423/500000000000 : ℝ) (103794084171/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2289/16384 : ℝ))) 6 (259485210423/500000000000 : ℝ) (103794084171/200000000000 : ℝ) (259485210423/500000000000 : ℝ) (103794084171/200000000000 : ℝ) (259485210423/500000000000 : ℝ) (103794084171/200000000000 : ℝ) (259485210423/500000000000 : ℝ) (103794084171/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2289/16384 : ℝ))) 7 (259485210423/500000000000 : ℝ) (103794084171/200000000000 : ℝ) (259485210423/500000000000 : ℝ) (103794084171/200000000000 : ℝ) (259485210423/500000000000 : ℝ) (103794084171/200000000000 : ℝ) (259485210423/500000000000 : ℝ) (103794084171/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2289/16384 : ℝ)) hmem 8 (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ) (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2289/16384 : ℝ))) hcmem 8 (259485210423/500000000000 : ℝ) (103794084171/200000000000 : ℝ) (259485210423/500000000000 : ℝ) (103794084171/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2289/16384 : ℝ)) (123761878577/125000000000 : ℝ) (990095028619/1000000000000 : ℝ) (259485210423/500000000000 : ℝ) (103794084171/200000000000 : ℝ) (102919013733/125000000000 : ℝ) (411676054941/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0498_exp_lower
  have heNumeric : (1009519046401/500000000000 : ℝ)/4 ≤ Real.exp (-5469385238431/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009519046401/500000000000 : ℝ)/4 ≤ Real.exp ((4577/32768 : ℝ)-(411676054941/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4577/32768 : ℝ) (2289/16384 : ℝ) (411676054941/500000000000 : ℝ) (1009519046401/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0499; no trusted numerical premise.
theorem cover7_leaf0499_exp_radius : (997507753846659683/1000000000000000000 : ℝ) ≤ Real.exp ((-4579/229376 : ℝ)/8) ∧ Real.exp ((-4579/229376 : ℝ)/8) ≤ (249376938461664921/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4579/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0499_exp_lower : (918090710355676803/1000000000000000000 : ℝ) ≤ Real.exp ((-2734690567031/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734690567031/4000000000000 : ℝ)/8) ≤ (229522677588919201/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734690567031/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0499_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009519564331/500000000000 : ℝ) ≤ 4*Real.exp (2289/16384 : ℝ)*Real.exp (-mu (radius 7 (4579/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009519564331/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4579/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0499_exp_radius
  have hrNumeric : (980235082729/1000000000000 : ℝ) ≤ Real.exp (-4579/229376 : ℝ) ∧ Real.exp (-4579/229376 : ℝ) ≤ (98023508273/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980235082729/1000000000000 : ℝ) ≤ (radius 7 (4579/32768 : ℝ)) ∧ (radius 7 (4579/32768 : ℝ)) ≤ (98023508273/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4579/32768 : ℝ)) (980235082729/1000000000000 : ℝ) (98023508273/100000000000 : ℝ) (197836251949/1000000000000 : ℝ) (39567250391/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4579/32768 : ℝ)) (980235082729/1000000000000 : ℝ) (98023508273/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4579/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980235082729/1000000000000 : ℝ) (98023508273/100000000000 : ℝ) (247529385341/250000000000 : ℝ) (198023508273/200000000000 : ℝ) (990068221249/1000000000000 : ℝ) (990068221251/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4579/32768 : ℝ)) 1 (247529385341/250000000000 : ℝ) (198023508273/200000000000 : ℝ) (990068221249/1000000000000 : ℝ) (990068221251/1000000000000 : ℝ) (495046440653/500000000000 : ℝ) (247523220327/250000000000 : ℝ) (990092880999/1000000000000 : ℝ) (990092881001/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4579/32768 : ℝ)) 2 (495046440653/500000000000 : ℝ) (247523220327/250000000000 : ℝ) (990092880999/1000000000000 : ℝ) (990092881001/1000000000000 : ℝ) (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ) (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4579/32768 : ℝ)) 3 (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ) (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ) (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ) (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4579/32768 : ℝ)) 4 (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ) (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ) (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ) (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4579/32768 : ℝ)) 5 (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ) (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ) (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ) (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4579/32768 : ℝ)) 6 (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ) (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ) (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ) (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4579/32768 : ℝ)) 7 (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ) (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ) (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ) (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4579/32768 : ℝ))) (197836251949/1000000000000 : ℝ) (39567250391/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4579/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (197836251949/1000000000000 : ℝ) (39567250391/200000000000 : ℝ) (299459062987/500000000000 : ℝ) (299459062989/500000000000 : ℝ) (222393936489/500000000000 : ℝ) (222393936493/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4579/32768 : ℝ))) 1 (299459062987/500000000000 : ℝ) (299459062989/500000000000 : ℝ) (222393936489/500000000000 : ℝ) (222393936493/500000000000 : ℝ) (130463249869/250000000000 : ℝ) (260926499741/500000000000 : ℝ) (129032825121/250000000000 : ℝ) (516131300491/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4579/32768 : ℝ))) 2 (130463249869/250000000000 : ℝ) (260926499741/500000000000 : ℝ) (129032825121/250000000000 : ℝ) (516131300491/1000000000000 : ℝ) (25949607499/50000000000 : ℝ) (518992149987/1000000000000 : ℝ) (129746066241/250000000000 : ℝ) (129746066243/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4579/32768 : ℝ))) 3 (25949607499/50000000000 : ℝ) (518992149987/1000000000000 : ℝ) (129746066241/250000000000 : ℝ) (129746066243/250000000000 : ℝ) (32436762967/62500000000 : ℝ) (12974705187/25000000000 : ℝ) (518988207457/1000000000000 : ℝ) (103797641493/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4579/32768 : ℝ))) 4 (32436762967/62500000000 : ℝ) (12974705187/25000000000 : ℝ) (518988207457/1000000000000 : ℝ) (103797641493/200000000000 : ℝ) (64873525933/125000000000 : ℝ) (518988207473/1000000000000 : ℝ) (64873525933/125000000000 : ℝ) (518988207473/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4579/32768 : ℝ))) 5 (64873525933/125000000000 : ℝ) (518988207473/1000000000000 : ℝ) (64873525933/125000000000 : ℝ) (518988207473/1000000000000 : ℝ) (64873525933/125000000000 : ℝ) (518988207473/1000000000000 : ℝ) (64873525933/125000000000 : ℝ) (518988207473/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4579/32768 : ℝ))) 6 (64873525933/125000000000 : ℝ) (518988207473/1000000000000 : ℝ) (64873525933/125000000000 : ℝ) (518988207473/1000000000000 : ℝ) (64873525933/125000000000 : ℝ) (518988207473/1000000000000 : ℝ) (64873525933/125000000000 : ℝ) (518988207473/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4579/32768 : ℝ))) 7 (64873525933/125000000000 : ℝ) (518988207473/1000000000000 : ℝ) (64873525933/125000000000 : ℝ) (518988207473/1000000000000 : ℝ) (64873525933/125000000000 : ℝ) (518988207473/1000000000000 : ℝ) (64873525933/125000000000 : ℝ) (518988207473/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4579/32768 : ℝ)) hmem 8 (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ) (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4579/32768 : ℝ))) hcmem 8 (64873525933/125000000000 : ℝ) (518988207473/1000000000000 : ℝ) (64873525933/125000000000 : ℝ) (518988207473/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4579/32768 : ℝ)) (3867550317/3906250000 : ℝ) (198018576231/200000000000 : ℝ) (64873525933/125000000000 : ℝ) (518988207473/1000000000000 : ℝ) (205845528599/250000000000 : ℝ) (411691057207/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0499_exp_lower
  have heNumeric : (1009519564331/500000000000 : ℝ)/4 ≤ Real.exp (-2734690567031/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009519564331/500000000000 : ℝ)/4 ≤ Real.exp ((2289/16384 : ℝ)-(411691057207/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2289/16384 : ℝ) (4579/32768 : ℝ) (411691057207/500000000000 : ℝ) (1009519564331/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0475_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0475_certificate
#check SmaleRate.Proofs.cover7_leaf0476_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0476_certificate
#check SmaleRate.Proofs.cover7_leaf0477_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0477_certificate
#check SmaleRate.Proofs.cover7_leaf0478_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0478_certificate
#check SmaleRate.Proofs.cover7_leaf0479_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0479_certificate
#check SmaleRate.Proofs.cover7_leaf0480_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0480_certificate
#check SmaleRate.Proofs.cover7_leaf0481_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0481_certificate
#check SmaleRate.Proofs.cover7_leaf0482_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0482_certificate
#check SmaleRate.Proofs.cover7_leaf0483_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0483_certificate
#check SmaleRate.Proofs.cover7_leaf0484_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0484_certificate
#check SmaleRate.Proofs.cover7_leaf0485_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0485_certificate
#check SmaleRate.Proofs.cover7_leaf0486_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0486_certificate
#check SmaleRate.Proofs.cover7_leaf0487_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0487_certificate
#check SmaleRate.Proofs.cover7_leaf0488_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0488_certificate
#check SmaleRate.Proofs.cover7_leaf0489_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0489_certificate
#check SmaleRate.Proofs.cover7_leaf0490_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0490_certificate
#check SmaleRate.Proofs.cover7_leaf0491_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0491_certificate
#check SmaleRate.Proofs.cover7_leaf0492_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0492_certificate
#check SmaleRate.Proofs.cover7_leaf0493_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0493_certificate
#check SmaleRate.Proofs.cover7_leaf0494_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0494_certificate
#check SmaleRate.Proofs.cover7_leaf0495_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0495_certificate
#check SmaleRate.Proofs.cover7_leaf0496_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0496_certificate
#check SmaleRate.Proofs.cover7_leaf0497_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0497_certificate
#check SmaleRate.Proofs.cover7_leaf0498_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0498_certificate
#check SmaleRate.Proofs.cover7_leaf0499_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0499_certificate
