/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0575; no trusted numerical premise.
theorem cover7_leaf0575_exp_radius : (199483177983188357/200000000000000000 : ℝ) ≤ Real.exp ((-1187/57344 : ℝ)/8) ∧ Real.exp ((-1187/57344 : ℝ)/8) ≤ (498707944957970893/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1187/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0575_exp_lower : (45904860063307213/50000000000000000 : ℝ) ≤ Real.exp ((-341808040939/500000000000 : ℝ)/8) ∧ Real.exp ((-341808040939/500000000000 : ℝ)/8) ≤ (918097201266144261/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341808040939/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0575_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009576664251/500000000000 : ℝ) ≤ 4*Real.exp (593/4096 : ℝ)*Real.exp (-mu (radius 7 (1187/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (1009576664251/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1187/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0575_exp_radius
  have hrNumeric : (48975656481/50000000000 : ℝ) ≤ Real.exp (-1187/57344 : ℝ) ∧ Real.exp (-1187/57344 : ℝ) ≤ (979513129621/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (48975656481/50000000000 : ℝ) ≤ (radius 7 (1187/8192 : ℝ)) ∧ (radius 7 (1187/8192 : ℝ)) ≤ (979513129621/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1187/8192 : ℝ)) (48975656481/50000000000 : ℝ) (979513129621/1000000000000 : ℝ) (201380309117/1000000000000 : ℝ) (100690154561/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1187/8192 : ℝ)) (48975656481/50000000000 : ℝ) (979513129621/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1187/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (48975656481/50000000000 : ℝ) (979513129621/1000000000000 : ℝ) (98975656481/100000000000 : ℝ) (989756564811/1000000000000 : ℝ) (494851778217/500000000000 : ℝ) (247425889109/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1187/8192 : ℝ)) 1 (98975656481/100000000000 : ℝ) (989756564811/1000000000000 : ℝ) (494851778217/500000000000 : ℝ) (247425889109/250000000000 : ℝ) (494865030311/500000000000 : ℝ) (61858128789/62500000000 : ℝ) (989730060267/1000000000000 : ℝ) (989730060269/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1187/8192 : ℝ)) 2 (494865030311/500000000000 : ℝ) (61858128789/62500000000 : ℝ) (989730060267/1000000000000 : ℝ) (989730060269/1000000000000 : ℝ) (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ) (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1187/8192 : ℝ)) 3 (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ) (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ) (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ) (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1187/8192 : ℝ)) 4 (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ) (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ) (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ) (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1187/8192 : ℝ)) 5 (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ) (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ) (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ) (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1187/8192 : ℝ)) 6 (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ) (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ) (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ) (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1187/8192 : ℝ)) 7 (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ) (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ) (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ) (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1187/8192 : ℝ))) (201380309117/1000000000000 : ℝ) (100690154561/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1187/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (201380309117/1000000000000 : ℝ) (100690154561/500000000000 : ℝ) (300345077279/500000000000 : ℝ) (600690154561/1000000000000 : ℝ) (112188543621/250000000000 : ℝ) (44875417449/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1187/8192 : ℝ))) 1 (300345077279/500000000000 : ℝ) (600690154561/1000000000000 : ℝ) (112188543621/250000000000 : ℝ) (44875417449/100000000000 : ℝ) (524722164521/1000000000000 : ℝ) (262361082263/500000000000 : ℝ) (519193812009/1000000000000 : ℝ) (103838762403/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1187/8192 : ℝ))) 2 (524722164521/1000000000000 : ℝ) (262361082263/500000000000 : ℝ) (519193812009/1000000000000 : ℝ) (103838762403/200000000000 : ℝ) (104391597653/200000000000 : ℝ) (521957988271/1000000000000 : ℝ) (260975334487/500000000000 : ℝ) (521950668981/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1187/8192 : ℝ))) 3 (104391597653/200000000000 : ℝ) (521957988271/1000000000000 : ℝ) (260975334487/500000000000 : ℝ) (521950668981/1000000000000 : ℝ) (521954328619/1000000000000 : ℝ) (260977164313/500000000000 : ℝ) (260977164303/500000000000 : ℝ) (260977164307/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1187/8192 : ℝ))) 4 (521954328619/1000000000000 : ℝ) (260977164313/500000000000 : ℝ) (260977164303/500000000000 : ℝ) (260977164307/500000000000 : ℝ) (130488582153/250000000000 : ℝ) (26097716431/50000000000 : ℝ) (130488582153/250000000000 : ℝ) (26097716431/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1187/8192 : ℝ))) 5 (130488582153/250000000000 : ℝ) (26097716431/50000000000 : ℝ) (130488582153/250000000000 : ℝ) (26097716431/50000000000 : ℝ) (130488582153/250000000000 : ℝ) (26097716431/50000000000 : ℝ) (130488582153/250000000000 : ℝ) (26097716431/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1187/8192 : ℝ))) 6 (130488582153/250000000000 : ℝ) (26097716431/50000000000 : ℝ) (130488582153/250000000000 : ℝ) (26097716431/50000000000 : ℝ) (130488582153/250000000000 : ℝ) (26097716431/50000000000 : ℝ) (130488582153/250000000000 : ℝ) (26097716431/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1187/8192 : ℝ))) 7 (130488582153/250000000000 : ℝ) (26097716431/50000000000 : ℝ) (130488582153/250000000000 : ℝ) (26097716431/50000000000 : ℝ) (130488582153/250000000000 : ℝ) (26097716431/50000000000 : ℝ) (130488582153/250000000000 : ℝ) (26097716431/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1187/8192 : ℝ)) hmem 8 (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ) (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1187/8192 : ℝ))) hcmem 8 (130488582153/250000000000 : ℝ) (26097716431/50000000000 : ℝ) (130488582153/250000000000 : ℝ) (26097716431/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1187/8192 : ℝ)) (247432515111/250000000000 : ℝ) (989730060447/1000000000000 : ℝ) (130488582153/250000000000 : ℝ) (26097716431/50000000000 : ℝ) (828391472487/1000000000000 : ℝ) (828391472503/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0575_exp_lower
  have heNumeric : (1009576664251/500000000000 : ℝ)/4 ≤ Real.exp (-341808040939/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009576664251/500000000000 : ℝ)/4 ≤ Real.exp ((593/4096 : ℝ)-(828391472503/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (593/4096 : ℝ) (1187/8192 : ℝ) (828391472503/1000000000000 : ℝ) (1009576664251/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0576; no trusted numerical premise.
theorem cover7_leaf0576_exp_radius : (997413715724215493/1000000000000000000 : ℝ) ≤ Real.exp ((-297/14336 : ℝ)/8) ∧ Real.exp ((-297/14336 : ℝ)/8) ≤ (498706857862107747/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-297/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0576_exp_lower : (459048884834595791/500000000000000000 : ℝ) ≤ Real.exp ((-1367222258001/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367222258001/2000000000000 : ℝ)/8) ≤ (918097769669191583/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367222258001/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0576_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009581664573/500000000000 : ℝ) ≤ 4*Real.exp (1187/8192 : ℝ)*Real.exp (-mu (radius 7 (297/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (1009581664573/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (297/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0576_exp_radius
  have hrNumeric : (195899209683/200000000000 : ℝ) ≤ Real.exp (-297/14336 : ℝ) ∧ Real.exp (-297/14336 : ℝ) ≤ (30609251513/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (195899209683/200000000000 : ℝ) ≤ (radius 7 (297/2048 : ℝ)) ∧ (radius 7 (297/2048 : ℝ)) ≤ (30609251513/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (297/2048 : ℝ)) (195899209683/200000000000 : ℝ) (30609251513/31250000000 : ℝ) (201463374183/1000000000000 : ℝ) (201463374189/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (297/2048 : ℝ)) (195899209683/200000000000 : ℝ) (30609251513/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (297/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (195899209683/200000000000 : ℝ) (30609251513/31250000000 : ℝ) (989748024207/1000000000000 : ℝ) (61859251513/62500000000 : ℝ) (494847463471/500000000000 : ℝ) (989694926943/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (297/2048 : ℝ)) 1 (989748024207/1000000000000 : ℝ) (61859251513/62500000000 : ℝ) (494847463471/500000000000 : ℝ) (989694926943/1000000000000 : ℝ) (494860737787/500000000000 : ℝ) (123715184447/125000000000 : ℝ) (494860737609/500000000000 : ℝ) (49486073761/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (297/2048 : ℝ)) 2 (494860737787/500000000000 : ℝ) (123715184447/125000000000 : ℝ) (494860737609/500000000000 : ℝ) (49486073761/50000000000 : ℝ) (247430368849/250000000000 : ℝ) (494860737699/500000000000 : ℝ) (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (297/2048 : ℝ)) 3 (247430368849/250000000000 : ℝ) (494860737699/500000000000 : ℝ) (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ) (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ) (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (297/2048 : ℝ)) 4 (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ) (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ) (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ) (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (297/2048 : ℝ)) 5 (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ) (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ) (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ) (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (297/2048 : ℝ)) 6 (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ) (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ) (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ) (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (297/2048 : ℝ)) 7 (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ) (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ) (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ) (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (297/2048 : ℝ))) (201463374183/1000000000000 : ℝ) (201463374189/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (297/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (201463374183/1000000000000 : ℝ) (201463374189/1000000000000 : ℝ) (600731687091/1000000000000 : ℝ) (120146337419/200000000000 : ℝ) (224423357843/500000000000 : ℝ) (224423357847/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (297/2048 : ℝ))) 1 (600731687091/1000000000000 : ℝ) (120146337419/200000000000 : ℝ) (224423357843/500000000000 : ℝ) (224423357847/500000000000 : ℝ) (131197300347/250000000000 : ℝ) (104957840279/200000000000 : ℝ) (103853058647/200000000000 : ℝ) (519265293243/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (297/2048 : ℝ))) 2 (131197300347/250000000000 : ℝ) (104957840279/200000000000 : ℝ) (103853058647/200000000000 : ℝ) (519265293243/1000000000000 : ℝ) (522027247311/1000000000000 : ℝ) (522027247319/1000000000000 : ℝ) (261009970377/500000000000 : ℝ) (261009970381/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (297/2048 : ℝ))) 3 (522027247311/1000000000000 : ℝ) (522027247319/1000000000000 : ℝ) (261009970377/500000000000 : ℝ) (261009970381/500000000000 : ℝ) (32626474627/62500000000 : ℝ) (522023594041/1000000000000 : ℝ) (522023594019/1000000000000 : ℝ) (130505898507/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (297/2048 : ℝ))) 4 (32626474627/62500000000 : ℝ) (522023594041/1000000000000 : ℝ) (522023594019/1000000000000 : ℝ) (130505898507/250000000000 : ℝ) (20880943761/40000000000 : ℝ) (104404718807/200000000000 : ℝ) (20880943761/40000000000 : ℝ) (104404718807/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (297/2048 : ℝ))) 5 (20880943761/40000000000 : ℝ) (104404718807/200000000000 : ℝ) (20880943761/40000000000 : ℝ) (104404718807/200000000000 : ℝ) (20880943761/40000000000 : ℝ) (104404718807/200000000000 : ℝ) (20880943761/40000000000 : ℝ) (104404718807/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (297/2048 : ℝ))) 6 (20880943761/40000000000 : ℝ) (104404718807/200000000000 : ℝ) (20880943761/40000000000 : ℝ) (104404718807/200000000000 : ℝ) (20880943761/40000000000 : ℝ) (104404718807/200000000000 : ℝ) (20880943761/40000000000 : ℝ) (104404718807/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (297/2048 : ℝ))) 7 (20880943761/40000000000 : ℝ) (104404718807/200000000000 : ℝ) (20880943761/40000000000 : ℝ) (104404718807/200000000000 : ℝ) (20880943761/40000000000 : ℝ) (104404718807/200000000000 : ℝ) (20880943761/40000000000 : ℝ) (104404718807/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (297/2048 : ℝ)) hmem 8 (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ) (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (297/2048 : ℝ))) hcmem 8 (20880943761/40000000000 : ℝ) (104404718807/200000000000 : ℝ) (20880943761/40000000000 : ℝ) (104404718807/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (297/2048 : ℝ)) (197944295079/200000000000 : ℝ) (494860737699/500000000000 : ℝ) (20880943761/40000000000 : ℝ) (104404718807/200000000000 : ℝ) (828508589919/1000000000000 : ℝ) (414254294969/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0576_exp_lower
  have heNumeric : (1009581664573/500000000000 : ℝ)/4 ≤ Real.exp (-1367222258001/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009581664573/500000000000 : ℝ)/4 ≤ Real.exp ((1187/8192 : ℝ)-(414254294969/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1187/8192 : ℝ) (297/2048 : ℝ) (414254294969/500000000000 : ℝ) (1009581664573/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0577; no trusted numerical premise.
theorem cover7_leaf0577_exp_radius : (498705770768614279/500000000000000000 : ℝ) ≤ Real.exp ((-1189/57344 : ℝ)/8) ∧ Real.exp ((-1189/57344 : ℝ)/8) ≤ (997411541537228559/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1189/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0577_exp_lower : (918098345586766687/1000000000000000000 : ℝ) ≤ Real.exp ((-683606110647/1000000000000 : ℝ)/8) ∧ Real.exp ((-683606110647/1000000000000 : ℝ)/8) ≤ (28690573299586459/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683606110647/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0577_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019173462047/1000000000000 : ℝ) ≤ 4*Real.exp (297/2048 : ℝ)*Real.exp (-mu (radius 7 (1189/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019173462047/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1189/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0577_exp_radius
  have hrNumeric : (979478967509/1000000000000 : ℝ) ≤ Real.exp (-1189/57344 : ℝ) ∧ Real.exp (-1189/57344 : ℝ) ≤ (97947896751/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979478967509/1000000000000 : ℝ) ≤ (radius 7 (1189/8192 : ℝ)) ∧ (radius 7 (1189/8192 : ℝ)) ≤ (97947896751/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1189/8192 : ℝ)) (979478967509/1000000000000 : ℝ) (97947896751/100000000000 : ℝ) (40309280423/200000000000 : ℝ) (5038660053/25000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1189/8192 : ℝ)) (979478967509/1000000000000 : ℝ) (97947896751/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1189/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979478967509/1000000000000 : ℝ) (97947896751/100000000000 : ℝ) (494869741877/500000000000 : ℝ) (197947896751/200000000000 : ℝ) (39587451901/40000000000 : ℝ) (494843148763/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1189/8192 : ℝ)) 1 (494869741877/500000000000 : ℝ) (197947896751/200000000000 : ℝ) (39587451901/40000000000 : ℝ) (494843148763/500000000000 : ℝ) (989712890639/1000000000000 : ℝ) (989712890641/1000000000000 : ℝ) (494856445141/500000000000 : ℝ) (247428222571/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1189/8192 : ℝ)) 2 (989712890639/1000000000000 : ℝ) (989712890641/1000000000000 : ℝ) (494856445141/500000000000 : ℝ) (247428222571/250000000000 : ℝ) (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ) (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1189/8192 : ℝ)) 3 (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ) (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ) (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ) (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1189/8192 : ℝ)) 4 (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ) (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ) (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ) (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1189/8192 : ℝ)) 5 (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ) (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ) (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ) (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1189/8192 : ℝ)) 6 (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ) (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ) (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ) (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1189/8192 : ℝ)) 7 (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ) (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ) (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ) (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1189/8192 : ℝ))) (40309280423/200000000000 : ℝ) (5038660053/25000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1189/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (40309280423/200000000000 : ℝ) (5038660053/25000000000 : ℝ) (600773201057/1000000000000 : ℝ) (30038660053/50000000000 : ℝ) (56117399557/125000000000 : ℝ) (448939196463/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1189/8192 : ℝ))) 1 (600773201057/1000000000000 : ℝ) (30038660053/50000000000 : ℝ) (56117399557/125000000000 : ℝ) (448939196463/1000000000000 : ℝ) (131214049689/250000000000 : ℝ) (262428099381/500000000000 : ℝ) (129834182261/250000000000 : ℝ) (519336729051/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1189/8192 : ℝ))) 2 (131214049689/250000000000 : ℝ) (262428099381/500000000000 : ℝ) (129834182261/250000000000 : ℝ) (519336729051/1000000000000 : ℝ) (5220964639/10000000000 : ℝ) (522096463907/1000000000000 : ℝ) (522089170047/1000000000000 : ℝ) (261044585027/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1189/8192 : ℝ))) 3 (5220964639/10000000000 : ℝ) (522096463907/1000000000000 : ℝ) (522089170047/1000000000000 : ℝ) (261044585027/500000000000 : ℝ) (522092816973/1000000000000 : ℝ) (522092816981/1000000000000 : ℝ) (1631540053/3125000000 : ℝ) (65261602121/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1189/8192 : ℝ))) 4 (522092816973/1000000000000 : ℝ) (522092816981/1000000000000 : ℝ) (1631540053/3125000000 : ℝ) (65261602121/125000000000 : ℝ) (261046408483/500000000000 : ℝ) (20883712679/40000000000 : ℝ) (261046408483/500000000000 : ℝ) (20883712679/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1189/8192 : ℝ))) 5 (261046408483/500000000000 : ℝ) (20883712679/40000000000 : ℝ) (261046408483/500000000000 : ℝ) (20883712679/40000000000 : ℝ) (261046408483/500000000000 : ℝ) (20883712679/40000000000 : ℝ) (261046408483/500000000000 : ℝ) (20883712679/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1189/8192 : ℝ))) 6 (261046408483/500000000000 : ℝ) (20883712679/40000000000 : ℝ) (261046408483/500000000000 : ℝ) (20883712679/40000000000 : ℝ) (261046408483/500000000000 : ℝ) (20883712679/40000000000 : ℝ) (261046408483/500000000000 : ℝ) (20883712679/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1189/8192 : ℝ))) 7 (261046408483/500000000000 : ℝ) (20883712679/40000000000 : ℝ) (261046408483/500000000000 : ℝ) (20883712679/40000000000 : ℝ) (261046408483/500000000000 : ℝ) (20883712679/40000000000 : ℝ) (261046408483/500000000000 : ℝ) (20883712679/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1189/8192 : ℝ)) hmem 8 (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ) (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1189/8192 : ℝ))) hcmem 8 (261046408483/500000000000 : ℝ) (20883712679/40000000000 : ℝ) (261046408483/500000000000 : ℝ) (20883712679/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1189/8192 : ℝ)) (49485644523/50000000000 : ℝ) (989712890463/1000000000000 : ℝ) (261046408483/500000000000 : ℝ) (20883712679/40000000000 : ℝ) (828625641879/1000000000000 : ℝ) (828625641897/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0577_exp_lower
  have heNumeric : (2019173462047/1000000000000 : ℝ)/4 ≤ Real.exp (-683606110647/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019173462047/1000000000000 : ℝ)/4 ≤ Real.exp ((297/2048 : ℝ)-(828625641897/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (297/2048 : ℝ) (1189/8192 : ℝ) (828625641897/1000000000000 : ℝ) (2019173462047/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0578; no trusted numerical premise.
theorem cover7_leaf0578_exp_radius : (99740936735498097/100000000000000000 : ℝ) ≤ Real.exp ((-85/4096 : ℝ)/8) ∧ Real.exp ((-85/4096 : ℝ)/8) ≤ (997409367354980971/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0578_exp_lower : (183619785801251971/200000000000000000 : ℝ) ≤ Real.exp ((-273440410771/400000000000 : ℝ)/8) ∧ Real.exp ((-273440410771/400000000000 : ℝ)/8) ≤ (57381183062891241/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-273440410771/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0578_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252397965873/125000000000 : ℝ) ≤ 4*Real.exp (1189/8192 : ℝ)*Real.exp (-mu (radius 7 (595/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (252397965873/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (595/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0578_exp_radius
  have hrNumeric : (9794618869/10000000000 : ℝ) ≤ Real.exp (-85/4096 : ℝ) ∧ Real.exp (-85/4096 : ℝ) ≤ (979461886901/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (9794618869/10000000000 : ℝ) ≤ (radius 7 (595/4096 : ℝ)) ∧ (radius 7 (595/4096 : ℝ)) ≤ (979461886901/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (595/4096 : ℝ)) (9794618869/10000000000 : ℝ) (979461886901/1000000000000 : ℝ) (201629392967/1000000000000 : ℝ) (201629392973/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (595/4096 : ℝ)) (9794618869/10000000000 : ℝ) (979461886901/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (595/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (9794618869/10000000000 : ℝ) (979461886901/1000000000000 : ℝ) (19794618869/20000000000 : ℝ) (989730943451/1000000000000 : ℝ) (494838834091/500000000000 : ℝ) (123709708523/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (595/4096 : ℝ)) 1 (19794618869/20000000000 : ℝ) (989730943451/1000000000000 : ℝ) (494838834091/500000000000 : ℝ) (123709708523/125000000000 : ℝ) (123713038227/125000000000 : ℝ) (494852152909/500000000000 : ℝ) (989704305457/1000000000000 : ℝ) (49485215273/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (595/4096 : ℝ)) 2 (123713038227/125000000000 : ℝ) (494852152909/500000000000 : ℝ) (989704305457/1000000000000 : ℝ) (49485215273/50000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (595/4096 : ℝ)) 3 (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (595/4096 : ℝ)) 4 (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (595/4096 : ℝ)) 5 (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (595/4096 : ℝ)) 6 (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (595/4096 : ℝ)) 7 (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (595/4096 : ℝ))) (201629392967/1000000000000 : ℝ) (201629392973/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (595/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (201629392967/1000000000000 : ℝ) (201629392973/1000000000000 : ℝ) (600814696483/1000000000000 : ℝ) (600814696487/1000000000000 : ℝ) (44903161689/100000000000 : ℝ) (449031616897/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (595/4096 : ℝ))) 1 (600814696483/1000000000000 : ℝ) (600814696487/1000000000000 : ℝ) (44903161689/100000000000 : ℝ) (449031616897/1000000000000 : ℝ) (262461578343/500000000000 : ℝ) (131230789173/250000000000 : ℝ) (51940811951/100000000000 : ℝ) (129852029879/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (595/4096 : ℝ))) 2 (262461578343/500000000000 : ℝ) (131230789173/250000000000 : ℝ) (51940811951/100000000000 : ℝ) (129852029879/250000000000 : ℝ) (261082819049/500000000000 : ℝ) (65270704763/125000000000 : ℝ) (13053958923/25000000000 : ℝ) (522158356927/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (595/4096 : ℝ))) 3 (261082819049/500000000000 : ℝ) (65270704763/125000000000 : ℝ) (13053958923/25000000000 : ℝ) (522158356927/1000000000000 : ℝ) (522161997509/1000000000000 : ℝ) (130540499379/250000000000 : ℝ) (65270249687/125000000000 : ℝ) (522161997503/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (595/4096 : ℝ))) 4 (522161997509/1000000000000 : ℝ) (130540499379/250000000000 : ℝ) (65270249687/125000000000 : ℝ) (522161997503/1000000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (595/4096 : ℝ))) 5 (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (595/4096 : ℝ))) 6 (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (595/4096 : ℝ))) 7 (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (595/4096 : ℝ)) hmem 8 (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (595/4096 : ℝ))) hcmem 8 (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (595/4096 : ℝ)) (247426076409/250000000000 : ℝ) (989704305639/1000000000000 : ℝ) (261080998751/500000000000 : ℝ) (52216199751/100000000000 : ℝ) (414371314237/500000000000 : ℝ) (82874262849/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0578_exp_lower
  have heNumeric : (252397965873/125000000000 : ℝ)/4 ≤ Real.exp (-273440410771/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252397965873/125000000000 : ℝ)/4 ≤ Real.exp ((1189/8192 : ℝ)-(82874262849/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1189/8192 : ℝ) (595/4096 : ℝ) (82874262849/100000000000 : ℝ) (252397965873/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0579; no trusted numerical premise.
theorem cover7_leaf0579_exp_radius : (498703596588736359/500000000000000000 : ℝ) ≤ Real.exp ((-1191/57344 : ℝ)/8) ∧ Real.exp ((-1191/57344 : ℝ)/8) ≤ (997407193177472719/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1191/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0579_exp_lower : (229524879979281811/250000000000000000 : ℝ) ≤ Real.exp ((-341797938967/500000000000 : ℝ)/8) ∧ Real.exp ((-341797938967/500000000000 : ℝ)/8) ≤ (183619903983425449/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341797938967/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0579_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (80767764951/40000000000 : ℝ) ≤ 4*Real.exp (595/4096 : ℝ)*Real.exp (-mu (radius 7 (1191/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (80767764951/40000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1191/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0579_exp_radius
  have hrNumeric : (979444806589/1000000000000 : ℝ) ≤ Real.exp (-1191/57344 : ℝ) ∧ Real.exp (-1191/57344 : ℝ) ≤ (97944480659/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979444806589/1000000000000 : ℝ) ≤ (radius 7 (1191/8192 : ℝ)) ∧ (radius 7 (1191/8192 : ℝ)) ≤ (97944480659/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1191/8192 : ℝ)) (979444806589/1000000000000 : ℝ) (97944480659/100000000000 : ℝ) (10085617339/50000000000 : ℝ) (100856173393/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1191/8192 : ℝ)) (979444806589/1000000000000 : ℝ) (97944480659/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1191/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979444806589/1000000000000 : ℝ) (97944480659/100000000000 : ℝ) (494861201647/500000000000 : ℝ) (197944480659/200000000000 : ℝ) (247417259729/250000000000 : ℝ) (989669038917/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1191/8192 : ℝ)) 1 (494861201647/500000000000 : ℝ) (197944480659/200000000000 : ℝ) (247417259729/250000000000 : ℝ) (989669038917/1000000000000 : ℝ) (197939144221/200000000000 : ℝ) (494847860553/500000000000 : ℝ) (197939144149/200000000000 : ℝ) (989695720747/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1191/8192 : ℝ)) 2 (197939144221/200000000000 : ℝ) (494847860553/500000000000 : ℝ) (197939144149/200000000000 : ℝ) (989695720747/1000000000000 : ℝ) (39587828837/40000000000 : ℝ) (989695720927/1000000000000 : ℝ) (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1191/8192 : ℝ)) 3 (39587828837/40000000000 : ℝ) (989695720927/1000000000000 : ℝ) (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ) (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ) (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1191/8192 : ℝ)) 4 (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ) (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ) (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ) (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1191/8192 : ℝ)) 5 (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ) (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ) (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ) (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1191/8192 : ℝ)) 6 (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ) (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ) (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ) (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1191/8192 : ℝ)) 7 (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ) (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ) (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ) (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1191/8192 : ℝ))) (10085617339/50000000000 : ℝ) (100856173393/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1191/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (10085617339/50000000000 : ℝ) (100856173393/500000000000 : ℝ) (60085617339/100000000000 : ℝ) (600856173393/1000000000000 : ℝ) (44912397707/100000000000 : ℝ) (224561988539/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1191/8192 : ℝ))) 1 (60085617339/100000000000 : ℝ) (600856173393/1000000000000 : ℝ) (44912397707/100000000000 : ℝ) (224561988539/500000000000 : ℝ) (52499007523/100000000000 : ℝ) (131247518809/250000000000 : ℝ) (103895892939/200000000000 : ℝ) (259739732351/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1191/8192 : ℝ))) 2 (52499007523/100000000000 : ℝ) (131247518809/250000000000 : ℝ) (103895892939/200000000000 : ℝ) (259739732351/500000000000 : ℝ) (261117384981/500000000000 : ℝ) (522234769969/1000000000000 : ℝ) (52222750143/100000000000 : ℝ) (261113750719/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1191/8192 : ℝ))) 3 (261117384981/500000000000 : ℝ) (522234769969/1000000000000 : ℝ) (52222750143/100000000000 : ℝ) (261113750719/500000000000 : ℝ) (32639445981/62500000000 : ℝ) (65278891963/125000000000 : ℝ) (522231135683/1000000000000 : ℝ) (522231135691/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1191/8192 : ℝ))) 4 (32639445981/62500000000 : ℝ) (65278891963/125000000000 : ℝ) (522231135683/1000000000000 : ℝ) (522231135691/1000000000000 : ℝ) (522231135689/1000000000000 : ℝ) (261115567849/500000000000 : ℝ) (522231135689/1000000000000 : ℝ) (261115567849/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1191/8192 : ℝ))) 5 (522231135689/1000000000000 : ℝ) (261115567849/500000000000 : ℝ) (522231135689/1000000000000 : ℝ) (261115567849/500000000000 : ℝ) (522231135689/1000000000000 : ℝ) (261115567849/500000000000 : ℝ) (522231135689/1000000000000 : ℝ) (261115567849/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1191/8192 : ℝ))) 6 (522231135689/1000000000000 : ℝ) (261115567849/500000000000 : ℝ) (522231135689/1000000000000 : ℝ) (261115567849/500000000000 : ℝ) (522231135689/1000000000000 : ℝ) (261115567849/500000000000 : ℝ) (522231135689/1000000000000 : ℝ) (261115567849/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1191/8192 : ℝ))) 7 (522231135689/1000000000000 : ℝ) (261115567849/500000000000 : ℝ) (522231135689/1000000000000 : ℝ) (261115567849/500000000000 : ℝ) (522231135689/1000000000000 : ℝ) (261115567849/500000000000 : ℝ) (522231135689/1000000000000 : ℝ) (261115567849/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1191/8192 : ℝ)) hmem 8 (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ) (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1191/8192 : ℝ))) hcmem 8 (522231135689/1000000000000 : ℝ) (261115567849/500000000000 : ℝ) (522231135689/1000000000000 : ℝ) (261115567849/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1191/8192 : ℝ)) (247423930231/250000000000 : ℝ) (989695720927/1000000000000 : ℝ) (522231135689/1000000000000 : ℝ) (261115567849/500000000000 : ℝ) (828859549791/1000000000000 : ℝ) (828859549809/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0579_exp_lower
  have heNumeric : (80767764951/40000000000 : ℝ)/4 ≤ Real.exp (-341797938967/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (80767764951/40000000000 : ℝ)/4 ≤ Real.exp ((595/4096 : ℝ)-(828859549809/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (595/4096 : ℝ) (1191/8192 : ℝ) (828859549809/1000000000000 : ℝ) (80767764951/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0580; no trusted numerical premise.
theorem cover7_leaf0580_exp_radius : (997405019004703791/1000000000000000000 : ℝ) ≤ Real.exp ((-149/7168 : ℝ)/8) ∧ Real.exp ((-149/7168 : ℝ)/8) ≤ (62337813687793987/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-149/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0580_exp_lower : (459050059154412583/500000000000000000 : ℝ) ≤ Real.exp ((-1367181327517/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367181327517/2000000000000 : ℝ)/8) ≤ (918100118308825167/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367181327517/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0580_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403840930447/200000000000 : ℝ) ≤ 4*Real.exp (1191/8192 : ℝ)*Real.exp (-mu (radius 7 (149/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (403840930447/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (149/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0580_exp_radius
  have hrNumeric : (61214232911/62500000000 : ℝ) ≤ Real.exp (-149/7168 : ℝ) ∧ Real.exp (-149/7168 : ℝ) ≤ (979427726577/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61214232911/62500000000 : ℝ) ≤ (radius 7 (149/1024 : ℝ)) ∧ (radius 7 (149/1024 : ℝ)) ≤ (979427726577/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (149/1024 : ℝ)) (61214232911/62500000000 : ℝ) (979427726577/1000000000000 : ℝ) (100897631801/500000000000 : ℝ) (201795263607/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (149/1024 : ℝ)) (61214232911/62500000000 : ℝ) (979427726577/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (149/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61214232911/62500000000 : ℝ) (979427726577/1000000000000 : ℝ) (123714232911/125000000000 : ℝ) (989713863289/1000000000000 : ℝ) (247415102431/250000000000 : ℝ) (39586416389/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (149/1024 : ℝ)) 1 (123714232911/125000000000 : ℝ) (989713863289/1000000000000 : ℝ) (247415102431/250000000000 : ℝ) (39586416389/40000000000 : ℝ) (494843568253/500000000000 : ℝ) (989687136507/1000000000000 : ℝ) (197937427229/200000000000 : ℝ) (989687136147/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (149/1024 : ℝ)) 2 (494843568253/500000000000 : ℝ) (989687136507/1000000000000 : ℝ) (197937427229/200000000000 : ℝ) (989687136147/1000000000000 : ℝ) (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ) (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (149/1024 : ℝ)) 3 (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ) (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ) (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ) (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (149/1024 : ℝ)) 4 (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ) (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ) (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ) (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (149/1024 : ℝ)) 5 (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ) (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ) (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ) (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (149/1024 : ℝ)) 6 (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ) (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ) (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ) (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (149/1024 : ℝ)) 7 (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ) (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ) (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ) (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (149/1024 : ℝ))) (100897631801/500000000000 : ℝ) (201795263607/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (149/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (100897631801/500000000000 : ℝ) (201795263607/1000000000000 : ℝ) (600897631801/1000000000000 : ℝ) (150224407951/250000000000 : ℝ) (449216277089/1000000000000 : ℝ) (89843255419/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (149/1024 : ℝ))) 1 (600897631801/1000000000000 : ℝ) (150224407951/250000000000 : ℝ) (449216277089/1000000000000 : ℝ) (89843255419/200000000000 : ℝ) (105011390889/200000000000 : ℝ) (10501139089/20000000000 : ℝ) (51955076467/100000000000 : ℝ) (20782030587/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (149/1024 : ℝ))) 2 (105011390889/200000000000 : ℝ) (10501139089/20000000000 : ℝ) (51955076467/100000000000 : ℝ) (20782030587/40000000000 : ℝ) (522303859557/1000000000000 : ℝ) (522303859563/1000000000000 : ℝ) (522296603643/1000000000000 : ℝ) (522296603649/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (149/1024 : ℝ))) 3 (522303859557/1000000000000 : ℝ) (522303859563/1000000000000 : ℝ) (522296603643/1000000000000 : ℝ) (522296603649/1000000000000 : ℝ) (1305750579/2500000000 : ℝ) (261150115803/500000000000 : ℝ) (522300231587/1000000000000 : ℝ) (261150115797/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (149/1024 : ℝ))) 4 (1305750579/2500000000 : ℝ) (261150115803/500000000000 : ℝ) (522300231587/1000000000000 : ℝ) (261150115797/500000000000 : ℝ) (522300231593/1000000000000 : ℝ) (1305750579/2500000000 : ℝ) (522300231593/1000000000000 : ℝ) (1305750579/2500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (149/1024 : ℝ))) 5 (522300231593/1000000000000 : ℝ) (1305750579/2500000000 : ℝ) (522300231593/1000000000000 : ℝ) (1305750579/2500000000 : ℝ) (522300231593/1000000000000 : ℝ) (1305750579/2500000000 : ℝ) (522300231593/1000000000000 : ℝ) (1305750579/2500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (149/1024 : ℝ))) 6 (522300231593/1000000000000 : ℝ) (1305750579/2500000000 : ℝ) (522300231593/1000000000000 : ℝ) (1305750579/2500000000 : ℝ) (522300231593/1000000000000 : ℝ) (1305750579/2500000000 : ℝ) (522300231593/1000000000000 : ℝ) (1305750579/2500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (149/1024 : ℝ))) 7 (522300231593/1000000000000 : ℝ) (1305750579/2500000000 : ℝ) (522300231593/1000000000000 : ℝ) (1305750579/2500000000 : ℝ) (522300231593/1000000000000 : ℝ) (1305750579/2500000000 : ℝ) (522300231593/1000000000000 : ℝ) (1305750579/2500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (149/1024 : ℝ)) hmem 8 (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ) (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (149/1024 : ℝ))) hcmem 8 (522300231593/1000000000000 : ℝ) (1305750579/2500000000 : ℝ) (522300231593/1000000000000 : ℝ) (1305750579/2500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (149/1024 : ℝ)) (39587485453/40000000000 : ℝ) (989687136327/1000000000000 : ℝ) (522300231593/1000000000000 : ℝ) (1305750579/2500000000 : ℝ) (207244101483/250000000000 : ℝ) (414488202973/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0580_exp_lower
  have heNumeric : (403840930447/200000000000 : ℝ)/4 ≤ Real.exp (-1367181327517/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403840930447/200000000000 : ℝ)/4 ≤ Real.exp ((1191/8192 : ℝ)-(414488202973/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1191/8192 : ℝ) (149/1024 : ℝ) (414488202973/500000000000 : ℝ) (403840930447/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0581; no trusted numerical premise.
theorem cover7_leaf0581_exp_radius : (997402844836674179/1000000000000000000 : ℝ) ≤ Real.exp ((-1193/57344 : ℝ)/8) ∧ Real.exp ((-1193/57344 : ℝ)/8) ≤ (49870142241833709/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1193/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0581_exp_lower : (229525181042472997/250000000000000000 : ℝ) ≤ Real.exp ((-683585384501/1000000000000 : ℝ)/8) ∧ Real.exp ((-683585384501/1000000000000 : ℝ)/8) ≤ (918100724169891989/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683585384501/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0581_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504803828041/250000000000 : ℝ) ≤ 4*Real.exp (149/1024 : ℝ)*Real.exp (-mu (radius 7 (1193/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (504803828041/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1193/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0581_exp_radius
  have hrNumeric : (979410646861/1000000000000 : ℝ) ≤ Real.exp (-1193/57344 : ℝ) ∧ Real.exp (-1193/57344 : ℝ) ≤ (489705323431/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979410646861/1000000000000 : ℝ) ≤ (radius 7 (1193/8192 : ℝ)) ∧ (radius 7 (1193/8192 : ℝ)) ≤ (489705323431/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1193/8192 : ℝ)) (979410646861/1000000000000 : ℝ) (489705323431/500000000000 : ℝ) (50469535869/250000000000 : ℝ) (201878143481/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1193/8192 : ℝ)) (979410646861/1000000000000 : ℝ) (489705323431/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1193/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979410646861/1000000000000 : ℝ) (489705323431/500000000000 : ℝ) (98970532343/100000000000 : ℝ) (989705323431/1000000000000 : ℝ) (966456817/976562500 : ℝ) (989651780609/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1193/8192 : ℝ)) 1 (98970532343/100000000000 : ℝ) (989705323431/1000000000000 : ℝ) (966456817/976562500 : ℝ) (989651780609/1000000000000 : ℝ) (989678552019/1000000000000 : ℝ) (49483927601/50000000000 : ℝ) (123709818957/125000000000 : ℝ) (494839275829/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1193/8192 : ℝ)) 2 (989678552019/1000000000000 : ℝ) (49483927601/50000000000 : ℝ) (123709818957/125000000000 : ℝ) (494839275829/500000000000 : ℝ) (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ) (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1193/8192 : ℝ)) 3 (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ) (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ) (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ) (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1193/8192 : ℝ)) 4 (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ) (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ) (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ) (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1193/8192 : ℝ)) 5 (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ) (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ) (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ) (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1193/8192 : ℝ)) 6 (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ) (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ) (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ) (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1193/8192 : ℝ)) 7 (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ) (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ) (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ) (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1193/8192 : ℝ))) (50469535869/250000000000 : ℝ) (201878143481/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1193/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (50469535869/250000000000 : ℝ) (201878143481/1000000000000 : ℝ) (300469535869/500000000000 : ℝ) (600939071741/1000000000000 : ℝ) (44930851703/100000000000 : ℝ) (112327129259/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1193/8192 : ℝ))) 1 (300469535869/500000000000 : ℝ) (600939071741/1000000000000 : ℝ) (44930851703/100000000000 : ℝ) (112327129259/250000000000 : ℝ) (32820237149/62500000000 : ℝ) (525123794389/1000000000000 : ℝ) (259811009749/500000000000 : ℝ) (32476376219/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1193/8192 : ℝ))) 2 (32820237149/62500000000 : ℝ) (525123794389/1000000000000 : ℝ) (259811009749/500000000000 : ℝ) (32476376219/62500000000 : ℝ) (522372906941/1000000000000 : ℝ) (522372906947/1000000000000 : ℝ) (104473132723/200000000000 : ℝ) (522365663621/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1193/8192 : ℝ))) 3 (522372906941/1000000000000 : ℝ) (522372906947/1000000000000 : ℝ) (104473132723/200000000000 : ℝ) (522365663621/1000000000000 : ℝ) (261184642639/500000000000 : ℝ) (130592321321/250000000000 : ℝ) (104473857053/200000000000 : ℝ) (65296160659/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1193/8192 : ℝ))) 4 (261184642639/500000000000 : ℝ) (130592321321/250000000000 : ℝ) (104473857053/200000000000 : ℝ) (65296160659/125000000000 : ℝ) (522369285271/1000000000000 : ℝ) (261184642639/500000000000 : ℝ) (522369285271/1000000000000 : ℝ) (261184642639/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1193/8192 : ℝ))) 5 (522369285271/1000000000000 : ℝ) (261184642639/500000000000 : ℝ) (522369285271/1000000000000 : ℝ) (261184642639/500000000000 : ℝ) (522369285271/1000000000000 : ℝ) (261184642639/500000000000 : ℝ) (522369285271/1000000000000 : ℝ) (261184642639/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1193/8192 : ℝ))) 6 (522369285271/1000000000000 : ℝ) (261184642639/500000000000 : ℝ) (522369285271/1000000000000 : ℝ) (261184642639/500000000000 : ℝ) (522369285271/1000000000000 : ℝ) (261184642639/500000000000 : ℝ) (522369285271/1000000000000 : ℝ) (261184642639/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1193/8192 : ℝ))) 7 (522369285271/1000000000000 : ℝ) (261184642639/500000000000 : ℝ) (522369285271/1000000000000 : ℝ) (261184642639/500000000000 : ℝ) (522369285271/1000000000000 : ℝ) (261184642639/500000000000 : ℝ) (522369285271/1000000000000 : ℝ) (261184642639/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1193/8192 : ℝ)) hmem 8 (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ) (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1193/8192 : ℝ))) hcmem 8 (522369285271/1000000000000 : ℝ) (261184642639/500000000000 : ℝ) (522369285271/1000000000000 : ℝ) (261184642639/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1193/8192 : ℝ)) (989678551837/1000000000000 : ℝ) (989678551839/1000000000000 : ℝ) (522369285271/1000000000000 : ℝ) (261184642639/500000000000 : ℝ) (829093196987/1000000000000 : ℝ) (829093197001/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0581_exp_lower
  have heNumeric : (504803828041/250000000000 : ℝ)/4 ≤ Real.exp (-683585384501/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504803828041/250000000000 : ℝ)/4 ≤ Real.exp ((149/1024 : ℝ)-(829093197001/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (149/1024 : ℝ) (1193/8192 : ℝ) (829093197001/1000000000000 : ℝ) (504803828041/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0582; no trusted numerical premise.
theorem cover7_leaf0582_exp_radius : (997400670673383873/1000000000000000000 : ℝ) ≤ Real.exp ((-597/28672 : ℝ)/8) ∧ Real.exp ((-597/28672 : ℝ)/8) ≤ (498700335336691937/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-597/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0582_exp_lower : (918101337488751469/1000000000000000000 : ℝ) ≤ Real.exp ((-54686403221/80000000000 : ℝ)/8) ∧ Real.exp ((-54686403221/80000000000 : ℝ)/8) ≤ (91810133748875147/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-54686403221/80000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0582_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019226103361/1000000000000 : ℝ) ≤ 4*Real.exp (1193/8192 : ℝ)*Real.exp (-mu (radius 7 (597/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019226103361/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (597/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0582_exp_radius
  have hrNumeric : (979393567443/1000000000000 : ℝ) ≤ Real.exp (-597/28672 : ℝ) ∧ Real.exp (-597/28672 : ℝ) ≤ (244848391861/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979393567443/1000000000000 : ℝ) ≤ (radius 7 (597/4096 : ℝ)) ∧ (radius 7 (597/4096 : ℝ)) ≤ (244848391861/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (597/4096 : ℝ)) (979393567443/1000000000000 : ℝ) (244848391861/250000000000 : ℝ) (201960986453/1000000000000 : ℝ) (201960986459/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (597/4096 : ℝ)) (979393567443/1000000000000 : ℝ) (244848391861/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (597/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979393567443/1000000000000 : ℝ) (244848391861/250000000000 : ℝ) (989696783721/1000000000000 : ℝ) (494848391861/500000000000 : ℝ) (494821575783/500000000000 : ℝ) (61852696973/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (597/4096 : ℝ)) 1 (989696783721/1000000000000 : ℝ) (494848391861/500000000000 : ℝ) (494821575783/500000000000 : ℝ) (61852696973/62500000000 : ℝ) (989669967643/1000000000000 : ℝ) (197933993529/200000000000 : ℝ) (12370874591/12500000000 : ℝ) (494834983641/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (597/4096 : ℝ)) 2 (989669967643/1000000000000 : ℝ) (197933993529/200000000000 : ℝ) (12370874591/12500000000 : ℝ) (494834983641/500000000000 : ℝ) (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ) (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (597/4096 : ℝ)) 3 (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ) (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ) (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ) (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (597/4096 : ℝ)) 4 (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ) (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ) (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ) (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (597/4096 : ℝ)) 5 (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ) (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ) (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ) (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (597/4096 : ℝ)) 6 (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ) (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ) (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ) (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (597/4096 : ℝ)) 7 (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ) (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ) (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ) (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (597/4096 : ℝ))) (201960986453/1000000000000 : ℝ) (201960986459/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (597/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (201960986453/1000000000000 : ℝ) (201960986459/1000000000000 : ℝ) (300490246613/500000000000 : ℝ) (60098049323/100000000000 : ℝ) (449400696987/1000000000000 : ℝ) (89880139399/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (597/4096 : ℝ))) 1 (300490246613/500000000000 : ℝ) (60098049323/100000000000 : ℝ) (449400696987/1000000000000 : ℝ) (89880139399/200000000000 : ℝ) (262595297553/500000000000 : ℝ) (525190595113/1000000000000 : ℝ) (129923307313/250000000000 : ℝ) (25984661463/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (597/4096 : ℝ))) 2 (262595297553/500000000000 : ℝ) (525190595113/1000000000000 : ℝ) (129923307313/250000000000 : ℝ) (25984661463/50000000000 : ℝ) (522441912179/1000000000000 : ℝ) (522441912187/1000000000000 : ℝ) (522434681413/1000000000000 : ℝ) (522434681421/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (597/4096 : ℝ))) 3 (522441912179/1000000000000 : ℝ) (522441912187/1000000000000 : ℝ) (522434681413/1000000000000 : ℝ) (522434681421/1000000000000 : ℝ) (130609574199/250000000000 : ℝ) (130609574201/250000000000 : ℝ) (522438296783/1000000000000 : ℝ) (65304787099/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (597/4096 : ℝ))) 4 (130609574199/250000000000 : ℝ) (130609574201/250000000000 : ℝ) (522438296783/1000000000000 : ℝ) (65304787099/125000000000 : ℝ) (522438296789/1000000000000 : ℝ) (261219148399/500000000000 : ℝ) (522438296789/1000000000000 : ℝ) (261219148399/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (597/4096 : ℝ))) 5 (522438296789/1000000000000 : ℝ) (261219148399/500000000000 : ℝ) (522438296789/1000000000000 : ℝ) (261219148399/500000000000 : ℝ) (522438296789/1000000000000 : ℝ) (261219148399/500000000000 : ℝ) (522438296789/1000000000000 : ℝ) (261219148399/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (597/4096 : ℝ))) 6 (522438296789/1000000000000 : ℝ) (261219148399/500000000000 : ℝ) (522438296789/1000000000000 : ℝ) (261219148399/500000000000 : ℝ) (522438296789/1000000000000 : ℝ) (261219148399/500000000000 : ℝ) (522438296789/1000000000000 : ℝ) (261219148399/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (597/4096 : ℝ))) 7 (522438296789/1000000000000 : ℝ) (261219148399/500000000000 : ℝ) (522438296789/1000000000000 : ℝ) (261219148399/500000000000 : ℝ) (522438296789/1000000000000 : ℝ) (261219148399/500000000000 : ℝ) (522438296789/1000000000000 : ℝ) (261219148399/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (597/4096 : ℝ)) hmem 8 (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ) (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (597/4096 : ℝ))) hcmem 8 (522438296789/1000000000000 : ℝ) (261219148399/500000000000 : ℝ) (522438296789/1000000000000 : ℝ) (261219148399/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (597/4096 : ℝ)) (989669967461/1000000000000 : ℝ) (123708745933/125000000000 : ℝ) (522438296789/1000000000000 : ℝ) (261219148399/500000000000 : ℝ) (829209923057/1000000000000 : ℝ) (33168396923/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0582_exp_lower
  have heNumeric : (2019226103361/1000000000000 : ℝ)/4 ≤ Real.exp (-54686403221/80000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019226103361/1000000000000 : ℝ)/4 ≤ Real.exp ((1193/8192 : ℝ)-(33168396923/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1193/8192 : ℝ) (597/4096 : ℝ) (33168396923/40000000000 : ℝ) (2019226103361/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0583; no trusted numerical premise.
theorem cover7_leaf0583_exp_radius : (498698161180510567/500000000000000000 : ℝ) ≤ Real.exp ((-299/14336 : ℝ)/8) ∧ Real.exp ((-299/14336 : ℝ)/8) ≤ (199479264472204227/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-299/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0583_exp_lower : (459044288716516141/500000000000000000 : ℝ) ≤ Real.exp ((-42730701719/62500000000 : ℝ)/8) ∧ Real.exp ((-42730701719/62500000000 : ℝ)/8) ≤ (918088577433032283/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42730701719/62500000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0583_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009500801831/500000000000 : ℝ) ≤ 4*Real.exp (597/4096 : ℝ)*Real.exp (-mu (radius 7 (299/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (1009500801831/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (299/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0583_exp_radius
  have hrNumeric : (489679704751/500000000000 : ℝ) ≤ Real.exp (-299/14336 : ℝ) ∧ Real.exp (-299/14336 : ℝ) ≤ (979359409503/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (489679704751/500000000000 : ℝ) ≤ (radius 7 (299/2048 : ℝ)) ∧ (radius 7 (299/2048 : ℝ)) ≤ (979359409503/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (299/2048 : ℝ)) (489679704751/500000000000 : ℝ) (979359409503/1000000000000 : ℝ) (202126561881/1000000000000 : ℝ) (202126561887/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (299/2048 : ℝ)) (489679704751/500000000000 : ℝ) (979359409503/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (299/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (489679704751/500000000000 : ℝ) (979359409503/1000000000000 : ℝ) (989679704751/1000000000000 : ℝ) (61854981547/62500000000 : ℝ) (98962589371/100000000000 : ℝ) (989625893711/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (299/2048 : ℝ)) 1 (989679704751/1000000000000 : ℝ) (61854981547/62500000000 : ℝ) (98962589371/100000000000 : ℝ) (989625893711/1000000000000 : ℝ) (98965279923/100000000000 : ℝ) (3865831247/3906250000 : ℝ) (61853299929/62500000000 : ℝ) (494826399433/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (299/2048 : ℝ)) 2 (98965279923/100000000000 : ℝ) (3865831247/3906250000 : ℝ) (61853299929/62500000000 : ℝ) (494826399433/500000000000 : ℝ) (989652799047/1000000000000 : ℝ) (989652799049/1000000000000 : ℝ) (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (299/2048 : ℝ)) 3 (989652799047/1000000000000 : ℝ) (989652799049/1000000000000 : ℝ) (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ) (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ) (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (299/2048 : ℝ)) 4 (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ) (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ) (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ) (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (299/2048 : ℝ)) 5 (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ) (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ) (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ) (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (299/2048 : ℝ)) 6 (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ) (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ) (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ) (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (299/2048 : ℝ)) 7 (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ) (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ) (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ) (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (299/2048 : ℝ))) (202126561881/1000000000000 : ℝ) (202126561887/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (299/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (202126561881/1000000000000 : ℝ) (202126561887/1000000000000 : ℝ) (30053164047/50000000000 : ℝ) (37566455059/62500000000 : ℝ) (224792438641/500000000000 : ℝ) (44958487729/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (299/2048 : ℝ))) 1 (30053164047/50000000000 : ℝ) (37566455059/62500000000 : ℝ) (224792438641/500000000000 : ℝ) (44958487729/100000000000 : ℝ) (525324079111/1000000000000 : ℝ) (525324079117/1000000000000 : ℝ) (8122429903/15625000000 : ℝ) (2599177569/5000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (299/2048 : ℝ))) 2 (525324079111/1000000000000 : ℝ) (525324079117/1000000000000 : ℝ) (8122429903/15625000000 : ℝ) (2599177569/5000000000 : ℝ) (522579796451/1000000000000 : ℝ) (522579796459/1000000000000 : ℝ) (816519673/1562500000 : ℝ) (65321573841/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (299/2048 : ℝ))) 3 (522579796451/1000000000000 : ℝ) (522579796459/1000000000000 : ℝ) (816519673/1562500000 : ℝ) (65321573841/125000000000 : ℝ) (104515238717/200000000000 : ℝ) (261288096797/500000000000 : ℝ) (522576193573/1000000000000 : ℝ) (261288096791/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (299/2048 : ℝ))) 4 (104515238717/200000000000 : ℝ) (261288096797/500000000000 : ℝ) (522576193573/1000000000000 : ℝ) (261288096791/500000000000 : ℝ) (522576193579/1000000000000 : ℝ) (130644048397/250000000000 : ℝ) (261288096789/500000000000 : ℝ) (130644048397/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (299/2048 : ℝ))) 5 (522576193579/1000000000000 : ℝ) (130644048397/250000000000 : ℝ) (261288096789/500000000000 : ℝ) (130644048397/250000000000 : ℝ) (261288096789/500000000000 : ℝ) (130644048397/250000000000 : ℝ) (261288096789/500000000000 : ℝ) (130644048397/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (299/2048 : ℝ))) 6 (261288096789/500000000000 : ℝ) (130644048397/250000000000 : ℝ) (261288096789/500000000000 : ℝ) (130644048397/250000000000 : ℝ) (261288096789/500000000000 : ℝ) (130644048397/250000000000 : ℝ) (261288096789/500000000000 : ℝ) (130644048397/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (299/2048 : ℝ))) 7 (261288096789/500000000000 : ℝ) (130644048397/250000000000 : ℝ) (261288096789/500000000000 : ℝ) (130644048397/250000000000 : ℝ) (261288096789/500000000000 : ℝ) (130644048397/250000000000 : ℝ) (261288096789/500000000000 : ℝ) (130644048397/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (299/2048 : ℝ)) hmem 8 (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ) (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (299/2048 : ℝ))) hcmem 8 (261288096789/500000000000 : ℝ) (130644048397/250000000000 : ℝ) (261288096789/500000000000 : ℝ) (130644048397/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (299/2048 : ℝ)) (494826399523/500000000000 : ℝ) (989652799049/1000000000000 : ℝ) (261288096789/500000000000 : ℝ) (130644048397/250000000000 : ℝ) (829443180609/1000000000000 : ℝ) (829443180629/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0583_exp_lower
  have heNumeric : (1009500801831/500000000000 : ℝ)/4 ≤ Real.exp (-42730701719/62500000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009500801831/500000000000 : ℝ)/4 ≤ Real.exp ((597/4096 : ℝ)-(829443180629/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (597/4096 : ℝ) (299/2048 : ℝ) (829443180629/1000000000000 : ℝ) (1009500801831/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0584; no trusted numerical premise.
theorem cover7_leaf0584_exp_radius : (997391974067615491/1000000000000000000 : ℝ) ≤ Real.exp ((-599/28672 : ℝ)/8) ∧ Real.exp ((-599/28672 : ℝ)/8) ≤ (249347993516903873/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-599/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0584_exp_lower : (918089856089279961/1000000000000000000 : ℝ) ≤ Real.exp ((-683680085613/1000000000000 : ℝ)/8) ∧ Real.exp ((-683680085613/1000000000000 : ℝ)/8) ≤ (459044928044639981/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683680085613/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0584_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019024099283/1000000000000 : ℝ) ≤ 4*Real.exp (299/2048 : ℝ)*Real.exp (-mu (radius 7 (599/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019024099283/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (599/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0584_exp_radius
  have hrNumeric : (979325252753/1000000000000 : ℝ) ≤ Real.exp (-599/28672 : ℝ) ∧ Real.exp (-599/28672 : ℝ) ≤ (489662626377/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979325252753/1000000000000 : ℝ) ≤ (radius 7 (599/4096 : ℝ)) ∧ (radius 7 (599/4096 : ℝ)) ≤ (489662626377/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (599/4096 : ℝ)) (979325252753/1000000000000 : ℝ) (489662626377/500000000000 : ℝ) (202291990247/1000000000000 : ℝ) (202291990253/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (599/4096 : ℝ)) (979325252753/1000000000000 : ℝ) (489662626377/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (599/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979325252753/1000000000000 : ℝ) (489662626377/500000000000 : ℝ) (123707828297/125000000000 : ℝ) (989662626377/1000000000000 : ℝ) (197921727231/200000000000 : ℝ) (247402159039/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (599/4096 : ℝ)) 1 (123707828297/125000000000 : ℝ) (989662626377/1000000000000 : ℝ) (197921727231/200000000000 : ℝ) (247402159039/250000000000 : ℝ) (197927126253/200000000000 : ℝ) (989635631267/1000000000000 : ℝ) (989635630897/1000000000000 : ℝ) (989635630899/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (599/4096 : ℝ)) 2 (197927126253/200000000000 : ℝ) (989635631267/1000000000000 : ℝ) (989635630897/1000000000000 : ℝ) (989635630899/1000000000000 : ℝ) (989635631081/1000000000000 : ℝ) (989635631083/1000000000000 : ℝ) (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (599/4096 : ℝ)) 3 (989635631081/1000000000000 : ℝ) (989635631083/1000000000000 : ℝ) (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ) (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ) (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (599/4096 : ℝ)) 4 (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ) (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ) (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ) (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (599/4096 : ℝ)) 5 (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ) (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ) (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ) (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (599/4096 : ℝ)) 6 (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ) (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ) (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ) (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (599/4096 : ℝ)) 7 (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ) (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ) (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ) (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (599/4096 : ℝ))) (202291990247/1000000000000 : ℝ) (202291990253/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (599/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (202291990247/1000000000000 : ℝ) (202291990253/1000000000000 : ℝ) (601145995123/1000000000000 : ℝ) (601145995127/1000000000000 : ℝ) (449768818669/1000000000000 : ℝ) (112442204669/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (599/4096 : ℝ))) 1 (601145995123/1000000000000 : ℝ) (601145995127/1000000000000 : ℝ) (449768818669/1000000000000 : ℝ) (112442204669/250000000000 : ℝ) (32841087931/62500000000 : ℝ) (262728703451/500000000000 : ℝ) (25998880941/50000000000 : ℝ) (519977618827/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (599/4096 : ℝ))) 2 (32841087931/62500000000 : ℝ) (262728703451/500000000000 : ℝ) (25998880941/50000000000 : ℝ) (519977618827/1000000000000 : ℝ) (261358756429/500000000000 : ℝ) (104543502573/200000000000 : ℝ) (522710332047/1000000000000 : ℝ) (261355166027/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (599/4096 : ℝ))) 3 (261358756429/500000000000 : ℝ) (104543502573/200000000000 : ℝ) (522710332047/1000000000000 : ℝ) (261355166027/500000000000 : ℝ) (130678480613/250000000000 : ℝ) (26135696123/50000000000 : ℝ) (13067848061/25000000000 : ℝ) (32669620153/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (599/4096 : ℝ))) 4 (130678480613/250000000000 : ℝ) (26135696123/50000000000 : ℝ) (13067848061/25000000000 : ℝ) (32669620153/62500000000 : ℝ) (261356961223/500000000000 : ℝ) (261356961227/500000000000 : ℝ) (104542784489/200000000000 : ℝ) (261356961227/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (599/4096 : ℝ))) 5 (261356961223/500000000000 : ℝ) (261356961227/500000000000 : ℝ) (104542784489/200000000000 : ℝ) (261356961227/500000000000 : ℝ) (104542784489/200000000000 : ℝ) (261356961227/500000000000 : ℝ) (104542784489/200000000000 : ℝ) (261356961227/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (599/4096 : ℝ))) 6 (104542784489/200000000000 : ℝ) (261356961227/500000000000 : ℝ) (104542784489/200000000000 : ℝ) (261356961227/500000000000 : ℝ) (104542784489/200000000000 : ℝ) (261356961227/500000000000 : ℝ) (104542784489/200000000000 : ℝ) (261356961227/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (599/4096 : ℝ))) 7 (104542784489/200000000000 : ℝ) (261356961227/500000000000 : ℝ) (104542784489/200000000000 : ℝ) (261356961227/500000000000 : ℝ) (104542784489/200000000000 : ℝ) (261356961227/500000000000 : ℝ) (104542784489/200000000000 : ℝ) (261356961227/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (599/4096 : ℝ)) hmem 8 (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ) (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (599/4096 : ℝ))) hcmem 8 (104542784489/200000000000 : ℝ) (261356961227/500000000000 : ℝ) (104542784489/200000000000 : ℝ) (261356961227/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (599/4096 : ℝ)) (24740890777/25000000000 : ℝ) (989635631083/1000000000000 : ℝ) (104542784489/200000000000 : ℝ) (261356961227/500000000000 : ℝ) (165935235869/200000000000 : ℝ) (829676179363/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0584_exp_lower
  have heNumeric : (2019024099283/1000000000000 : ℝ)/4 ≤ Real.exp (-683680085613/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019024099283/1000000000000 : ℝ)/4 ≤ Real.exp ((299/2048 : ℝ)-(829676179363/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (299/2048 : ℝ) (599/4096 : ℝ) (829676179363/1000000000000 : ℝ) (2019024099283/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0585; no trusted numerical premise.
theorem cover7_leaf0585_exp_radius : (498693812896583431/500000000000000000 : ℝ) ≤ Real.exp ((-75/3584 : ℝ)/8) ∧ Real.exp ((-75/3584 : ℝ)/8) ≤ (997387625793166863/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-75/3584 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0585_exp_lower : (918091164361256591/1000000000000000000 : ℝ) ≤ Real.exp ((-341834342837/500000000000 : ℝ)/8) ∧ Real.exp ((-341834342837/500000000000 : ℝ)/8) ≤ (57380697772578537/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341834342837/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0585_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009523558083/500000000000 : ℝ) ≤ 4*Real.exp (599/4096 : ℝ)*Real.exp (-mu (radius 7 (75/512 : ℝ))) ∧ (2019/1000 : ℝ) < (1009523558083/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (75/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0585_exp_radius
  have hrNumeric : (489645548597/500000000000 : ℝ) ≤ Real.exp (-75/3584 : ℝ) ∧ Real.exp (-75/3584 : ℝ) ≤ (195858219439/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (489645548597/500000000000 : ℝ) ≤ (radius 7 (75/512 : ℝ)) ∧ (radius 7 (75/512 : ℝ)) ≤ (195858219439/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (75/512 : ℝ)) (489645548597/500000000000 : ℝ) (195858219439/200000000000 : ℝ) (202457271923/1000000000000 : ℝ) (202457271929/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (75/512 : ℝ)) (489645548597/500000000000 : ℝ) (195858219439/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (75/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (489645548597/500000000000 : ℝ) (195858219439/200000000000 : ℝ) (989645548597/1000000000000 : ℝ) (494822774299/500000000000 : ℝ) (9895913789/10000000000 : ℝ) (989591378901/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (75/512 : ℝ)) 1 (989645548597/1000000000000 : ℝ) (494822774299/500000000000 : ℝ) (9895913789/10000000000 : ℝ) (989591378901/1000000000000 : ℝ) (247404615937/250000000000 : ℝ) (791694771/800000000 : ℝ) (989618463377/1000000000000 : ℝ) (989618463379/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (75/512 : ℝ)) 2 (247404615937/250000000000 : ℝ) (791694771/800000000 : ℝ) (989618463377/1000000000000 : ℝ) (989618463379/1000000000000 : ℝ) (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ) (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (75/512 : ℝ)) 3 (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ) (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ) (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ) (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (75/512 : ℝ)) 4 (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ) (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ) (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ) (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (75/512 : ℝ)) 5 (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ) (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ) (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ) (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (75/512 : ℝ)) 6 (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ) (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ) (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ) (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (75/512 : ℝ)) 7 (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ) (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ) (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ) (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (75/512 : ℝ))) (202457271923/1000000000000 : ℝ) (202457271929/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (75/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (202457271923/1000000000000 : ℝ) (202457271929/1000000000000 : ℝ) (601228635961/1000000000000 : ℝ) (120245727193/200000000000 : ℝ) (224976260927/500000000000 : ℝ) (449952521861/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (75/512 : ℝ))) 1 (601228635961/1000000000000 : ℝ) (120245727193/200000000000 : ℝ) (224976260927/500000000000 : ℝ) (449952521861/1000000000000 : ℝ) (525590578907/1000000000000 : ℝ) (525590578913/1000000000000 : ℝ) (4160956359/8000000000 : ℝ) (260059772441/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (75/512 : ℝ))) 2 (525590578907/1000000000000 : ℝ) (525590578913/1000000000000 : ℝ) (4160956359/8000000000 : ℝ) (260059772441/500000000000 : ℝ) (522855061891/1000000000000 : ℝ) (261427530949/500000000000 : ℝ) (16338997059/31250000000 : ℝ) (104569581179/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (75/512 : ℝ))) 3 (522855061891/1000000000000 : ℝ) (261427530949/500000000000 : ℝ) (16338997059/31250000000 : ℝ) (104569581179/200000000000 : ℝ) (522851483889/1000000000000 : ℝ) (522851483897/1000000000000 : ℝ) (522851483877/1000000000000 : ℝ) (104570296777/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (75/512 : ℝ))) 4 (522851483889/1000000000000 : ℝ) (522851483897/1000000000000 : ℝ) (522851483877/1000000000000 : ℝ) (104570296777/200000000000 : ℝ) (522851483883/1000000000000 : ℝ) (522851483891/1000000000000 : ℝ) (261425741941/500000000000 : ℝ) (522851483891/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (75/512 : ℝ))) 5 (522851483883/1000000000000 : ℝ) (522851483891/1000000000000 : ℝ) (261425741941/500000000000 : ℝ) (522851483891/1000000000000 : ℝ) (261425741941/500000000000 : ℝ) (522851483891/1000000000000 : ℝ) (261425741941/500000000000 : ℝ) (522851483891/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (75/512 : ℝ))) 6 (261425741941/500000000000 : ℝ) (522851483891/1000000000000 : ℝ) (261425741941/500000000000 : ℝ) (522851483891/1000000000000 : ℝ) (261425741941/500000000000 : ℝ) (522851483891/1000000000000 : ℝ) (261425741941/500000000000 : ℝ) (522851483891/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (75/512 : ℝ))) 7 (261425741941/500000000000 : ℝ) (522851483891/1000000000000 : ℝ) (261425741941/500000000000 : ℝ) (522851483891/1000000000000 : ℝ) (261425741941/500000000000 : ℝ) (522851483891/1000000000000 : ℝ) (261425741941/500000000000 : ℝ) (522851483891/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (75/512 : ℝ)) hmem 8 (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ) (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (75/512 : ℝ))) hcmem 8 (261425741941/500000000000 : ℝ) (522851483891/1000000000000 : ℝ) (261425741941/500000000000 : ℝ) (522851483891/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (75/512 : ℝ)) (494809231781/500000000000 : ℝ) (197923692713/200000000000 : ℝ) (261425741941/500000000000 : ℝ) (522851483891/1000000000000 : ℝ) (25934653751/31250000000 : ℝ) (829908920049/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0585_exp_lower
  have heNumeric : (1009523558083/500000000000 : ℝ)/4 ≤ Real.exp (-341834342837/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009523558083/500000000000 : ℝ)/4 ≤ Real.exp ((599/4096 : ℝ)-(829908920049/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (599/4096 : ℝ) (75/512 : ℝ) (829908920049/1000000000000 : ℝ) (1009523558083/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0586; no trusted numerical premise.
theorem cover7_leaf0586_exp_radius : (997383277537675163/1000000000000000000 : ℝ) ≤ Real.exp ((-601/28672 : ℝ)/8) ∧ Real.exp ((-601/28672 : ℝ)/8) ≤ (249345819384418791/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-601/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0586_exp_lower : (918092502164279981/1000000000000000000 : ℝ) ≤ Real.exp ((-341828514213/500000000000 : ℝ)/8) ∧ Real.exp ((-341828514213/500000000000 : ℝ)/8) ≤ (459046251082139991/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341828514213/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0586_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504767663209/250000000000 : ℝ) ≤ 4*Real.exp (75/512 : ℝ)*Real.exp (-mu (radius 7 (601/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (504767663209/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (601/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0586_exp_radius
  have hrNumeric : (979256942827/1000000000000 : ℝ) ≤ Real.exp (-601/28672 : ℝ) ∧ Real.exp (-601/28672 : ℝ) ≤ (244814235707/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979256942827/1000000000000 : ℝ) ≤ (radius 7 (601/4096 : ℝ)) ∧ (radius 7 (601/4096 : ℝ)) ≤ (244814235707/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (601/4096 : ℝ)) (979256942827/1000000000000 : ℝ) (244814235707/250000000000 : ℝ) (101311203629/500000000000 : ℝ) (6331950227/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (601/4096 : ℝ)) (979256942827/1000000000000 : ℝ) (244814235707/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (601/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979256942827/1000000000000 : ℝ) (244814235707/250000000000 : ℝ) (989628471413/1000000000000 : ℝ) (494814235707/500000000000 : ℝ) (494787060973/500000000000 : ℝ) (247393530487/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (601/4096 : ℝ)) 1 (989628471413/1000000000000 : ℝ) (494814235707/500000000000 : ℝ) (494787060973/500000000000 : ℝ) (247393530487/250000000000 : ℝ) (989601296679/1000000000000 : ℝ) (989601296681/1000000000000 : ℝ) (494800648153/500000000000 : ℝ) (247400324077/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (601/4096 : ℝ)) 2 (989601296679/1000000000000 : ℝ) (989601296681/1000000000000 : ℝ) (494800648153/500000000000 : ℝ) (247400324077/250000000000 : ℝ) (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ) (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (601/4096 : ℝ)) 3 (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ) (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ) (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ) (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (601/4096 : ℝ)) 4 (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ) (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ) (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ) (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (601/4096 : ℝ)) 5 (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ) (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ) (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ) (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (601/4096 : ℝ)) 6 (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ) (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ) (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ) (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (601/4096 : ℝ)) 7 (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ) (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ) (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ) (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (601/4096 : ℝ))) (101311203629/500000000000 : ℝ) (6331950227/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (601/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (101311203629/500000000000 : ℝ) (6331950227/31250000000 : ℝ) (601311203629/1000000000000 : ℝ) (37581950227/62500000000 : ℝ) (450135987517/1000000000000 : ℝ) (112533996881/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (601/4096 : ℝ))) 1 (601311203629/1000000000000 : ℝ) (37581950227/62500000000 : ℝ) (450135987517/1000000000000 : ℝ) (112533996881/250000000000 : ℝ) (525723595573/1000000000000 : ℝ) (262861797789/500000000000 : ℝ) (520261292477/1000000000000 : ℝ) (130065323121/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (601/4096 : ℝ))) 2 (525723595573/1000000000000 : ℝ) (262861797789/500000000000 : ℝ) (520261292477/1000000000000 : ℝ) (130065323121/250000000000 : ℝ) (20919697761/40000000000 : ℝ) (522992444031/1000000000000 : ℝ) (522985312717/1000000000000 : ℝ) (130746328181/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (601/4096 : ℝ))) 3 (20919697761/40000000000 : ℝ) (522992444031/1000000000000 : ℝ) (522985312717/1000000000000 : ℝ) (130746328181/250000000000 : ℝ) (522988878371/1000000000000 : ℝ) (261494439189/500000000000 : ℝ) (261494439179/500000000000 : ℝ) (261494439183/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (601/4096 : ℝ))) 4 (522988878371/1000000000000 : ℝ) (261494439189/500000000000 : ℝ) (261494439179/500000000000 : ℝ) (261494439183/500000000000 : ℝ) (130747219591/250000000000 : ℝ) (130747219593/250000000000 : ℝ) (130747219591/250000000000 : ℝ) (130747219593/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (601/4096 : ℝ))) 5 (130747219591/250000000000 : ℝ) (130747219593/250000000000 : ℝ) (130747219591/250000000000 : ℝ) (130747219593/250000000000 : ℝ) (130747219591/250000000000 : ℝ) (130747219593/250000000000 : ℝ) (130747219591/250000000000 : ℝ) (130747219593/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (601/4096 : ℝ))) 6 (130747219591/250000000000 : ℝ) (130747219593/250000000000 : ℝ) (130747219591/250000000000 : ℝ) (130747219593/250000000000 : ℝ) (130747219591/250000000000 : ℝ) (130747219593/250000000000 : ℝ) (130747219591/250000000000 : ℝ) (130747219593/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (601/4096 : ℝ))) 7 (130747219591/250000000000 : ℝ) (130747219593/250000000000 : ℝ) (130747219591/250000000000 : ℝ) (130747219593/250000000000 : ℝ) (130747219591/250000000000 : ℝ) (130747219593/250000000000 : ℝ) (130747219591/250000000000 : ℝ) (130747219593/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (601/4096 : ℝ)) hmem 8 (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ) (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (601/4096 : ℝ))) hcmem 8 (130747219591/250000000000 : ℝ) (130747219593/250000000000 : ℝ) (130747219591/250000000000 : ℝ) (130747219593/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (601/4096 : ℝ)) (247400324123/250000000000 : ℝ) (197920259299/200000000000 : ℝ) (130747219591/250000000000 : ℝ) (130747219593/250000000000 : ℝ) (83014140341/100000000000 : ℝ) (415070701713/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0586_exp_lower
  have heNumeric : (504767663209/250000000000 : ℝ)/4 ≤ Real.exp (-341828514213/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504767663209/250000000000 : ℝ)/4 ≤ Real.exp ((75/512 : ℝ)-(415070701713/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (75/512 : ℝ) (601/4096 : ℝ) (415070701713/500000000000 : ℝ) (504767663209/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0587; no trusted numerical premise.
theorem cover7_leaf0587_exp_radius : (997378929301140313/1000000000000000000 : ℝ) ≤ Real.exp ((-43/2048 : ℝ)/8) ∧ Real.exp ((-43/2048 : ℝ)/8) ≤ (498689464650570157/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-43/2048 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0587_exp_lower : (918093869411948871/1000000000000000000 : ℝ) ≤ Real.exp ((-683645114623/1000000000000 : ℝ)/8) ∧ Real.exp ((-683645114623/1000000000000 : ℝ)/8) ≤ (114761733676493609/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683645114623/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0587_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019094707789/1000000000000 : ℝ) ≤ 4*Real.exp (601/4096 : ℝ)*Real.exp (-mu (radius 7 (301/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (2019094707789/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (301/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0587_exp_radius
  have hrNumeric : (979222789651/1000000000000 : ℝ) ≤ Real.exp (-43/2048 : ℝ) ∧ Real.exp (-43/2048 : ℝ) ≤ (244805697413/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979222789651/1000000000000 : ℝ) ≤ (radius 7 (301/2048 : ℝ)) ∧ (radius 7 (301/2048 : ℝ)) ≤ (244805697413/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (301/2048 : ℝ)) (979222789651/1000000000000 : ℝ) (244805697413/250000000000 : ℝ) (40557479323/200000000000 : ℝ) (202787396621/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (301/2048 : ℝ)) (979222789651/1000000000000 : ℝ) (244805697413/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (301/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979222789651/1000000000000 : ℝ) (244805697413/250000000000 : ℝ) (39584455793/40000000000 : ℝ) (494805697413/500000000000 : ℝ) (494778432647/500000000000 : ℝ) (197911373059/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (301/2048 : ℝ)) 1 (39584455793/40000000000 : ℝ) (494805697413/500000000000 : ℝ) (494778432647/500000000000 : ℝ) (197911373059/200000000000 : ℝ) (989584130059/1000000000000 : ℝ) (989584130061/1000000000000 : ℝ) (989584129683/1000000000000 : ℝ) (197916825937/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (301/2048 : ℝ)) 2 (989584130059/1000000000000 : ℝ) (989584130061/1000000000000 : ℝ) (989584129683/1000000000000 : ℝ) (197916825937/200000000000 : ℝ) (989584129871/1000000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (301/2048 : ℝ)) 3 (989584129871/1000000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (301/2048 : ℝ)) 4 (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (301/2048 : ℝ)) 5 (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (301/2048 : ℝ)) 6 (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (301/2048 : ℝ)) 7 (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (301/2048 : ℝ))) (40557479323/200000000000 : ℝ) (202787396621/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (301/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (40557479323/200000000000 : ℝ) (202787396621/1000000000000 : ℝ) (601393698307/1000000000000 : ℝ) (601393698311/1000000000000 : ℝ) (450319216351/1000000000000 : ℝ) (225159608179/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (301/2048 : ℝ))) 1 (601393698307/1000000000000 : ℝ) (601393698311/1000000000000 : ℝ) (450319216351/1000000000000 : ℝ) (225159608179/500000000000 : ℝ) (525856457329/1000000000000 : ℝ) (105171291467/200000000000 : ℝ) (104080572431/200000000000 : ℝ) (260201431081/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (301/2048 : ℝ))) 2 (525856457329/1000000000000 : ℝ) (105171291467/200000000000 : ℝ) (104080572431/200000000000 : ℝ) (260201431081/500000000000 : ℝ) (261564829871/500000000000 : ℝ) (523129659749/1000000000000 : ℝ) (261561276509/500000000000 : ℝ) (261561276513/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (301/2048 : ℝ))) 3 (261564829871/500000000000 : ℝ) (523129659749/1000000000000 : ℝ) (261561276509/500000000000 : ℝ) (261561276513/500000000000 : ℝ) (26156305319/50000000000 : ℝ) (130781526597/250000000000 : ℝ) (523126106367/1000000000000 : ℝ) (65390763297/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (301/2048 : ℝ))) 4 (26156305319/50000000000 : ℝ) (130781526597/250000000000 : ℝ) (523126106367/1000000000000 : ℝ) (65390763297/125000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (301/2048 : ℝ))) 5 (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (301/2048 : ℝ))) 6 (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (301/2048 : ℝ))) 7 (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (301/2048 : ℝ)) hmem 8 (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (301/2048 : ℝ))) hcmem 8 (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (301/2048 : ℝ)) (98958412987/100000000000 : ℝ) (989584129873/1000000000000 : ℝ) (523126106373/1000000000000 : ℝ) (261563053191/500000000000 : ℝ) (83037363023/100000000000 : ℝ) (103796703781/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0587_exp_lower
  have heNumeric : (2019094707789/1000000000000 : ℝ)/4 ≤ Real.exp (-683645114623/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019094707789/1000000000000 : ℝ)/4 ≤ Real.exp ((601/4096 : ℝ)-(103796703781/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (601/4096 : ℝ) (301/2048 : ℝ) (103796703781/125000000000 : ℝ) (2019094707789/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0588; no trusted numerical premise.
theorem cover7_leaf0588_exp_radius : (249343645270890557/250000000000000000 : ℝ) ≤ Real.exp ((-603/28672 : ℝ)/8) ∧ Real.exp ((-603/28672 : ℝ)/8) ≤ (997374581083562229/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-603/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0588_exp_lower : (918095266019241469/1000000000000000000 : ℝ) ≤ Real.exp ((-683632945007/1000000000000 : ℝ)/8) ∧ Real.exp ((-683632945007/1000000000000 : ℝ)/8) ≤ (91809526601924147/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683632945007/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0588_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009559639773/500000000000 : ℝ) ≤ 4*Real.exp (301/2048 : ℝ)*Real.exp (-mu (radius 7 (603/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (1009559639773/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (603/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0588_exp_radius
  have hrNumeric : (489594318833/500000000000 : ℝ) ≤ Real.exp (-603/28672 : ℝ) ∧ Real.exp (-603/28672 : ℝ) ≤ (979188637667/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (489594318833/500000000000 : ℝ) ≤ (radius 7 (603/4096 : ℝ)) ∧ (radius 7 (603/4096 : ℝ)) ≤ (979188637667/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (603/4096 : ℝ)) (489594318833/500000000000 : ℝ) (979188637667/1000000000000 : ℝ) (202952240351/1000000000000 : ℝ) (202952240357/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (603/4096 : ℝ)) (489594318833/500000000000 : ℝ) (979188637667/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (603/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (489594318833/500000000000 : ℝ) (979188637667/1000000000000 : ℝ) (989594318833/1000000000000 : ℝ) (494797159417/500000000000 : ℝ) (494769804471/500000000000 : ℝ) (989539608943/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (603/4096 : ℝ)) 1 (989594318833/1000000000000 : ℝ) (494797159417/500000000000 : ℝ) (494769804471/500000000000 : ℝ) (989539608943/1000000000000 : ℝ) (989566963887/1000000000000 : ℝ) (989566963889/1000000000000 : ℝ) (989566963509/1000000000000 : ℝ) (989566963511/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (603/4096 : ℝ)) 2 (989566963887/1000000000000 : ℝ) (989566963889/1000000000000 : ℝ) (989566963509/1000000000000 : ℝ) (989566963511/1000000000000 : ℝ) (494783481849/500000000000 : ℝ) (9895669637/10000000000 : ℝ) (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (603/4096 : ℝ)) 3 (494783481849/500000000000 : ℝ) (9895669637/10000000000 : ℝ) (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ) (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ) (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (603/4096 : ℝ)) 4 (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ) (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ) (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ) (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (603/4096 : ℝ)) 5 (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ) (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ) (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ) (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (603/4096 : ℝ)) 6 (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ) (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ) (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ) (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (603/4096 : ℝ)) 7 (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ) (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ) (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ) (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (603/4096 : ℝ))) (202952240351/1000000000000 : ℝ) (202952240357/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (603/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (202952240351/1000000000000 : ℝ) (202952240357/1000000000000 : ℝ) (24059044807/40000000000 : ℝ) (601476120179/1000000000000 : ℝ) (450502209041/1000000000000 : ℝ) (56312776131/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (603/4096 : ℝ))) 1 (24059044807/40000000000 : ℝ) (601476120179/1000000000000 : ℝ) (450502209041/1000000000000 : ℝ) (56312776131/125000000000 : ℝ) (8218580697/15625000000 : ℝ) (262994582307/500000000000 : ℝ) (520544254433/1000000000000 : ℝ) (13013606361/25000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (603/4096 : ℝ))) 2 (8218580697/15625000000 : ℝ) (262994582307/500000000000 : ℝ) (520544254433/1000000000000 : ℝ) (13013606361/25000000000 : ℝ) (6540833869/12500000000 : ℝ) (523266709527/1000000000000 : ℝ) (523259627269/1000000000000 : ℝ) (523259627277/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (603/4096 : ℝ))) 3 (6540833869/12500000000 : ℝ) (523266709527/1000000000000 : ℝ) (523259627269/1000000000000 : ℝ) (523259627277/1000000000000 : ℝ) (261631584197/500000000000 : ℝ) (261631584201/500000000000 : ℝ) (261631584191/500000000000 : ℝ) (523263168391/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (603/4096 : ℝ))) 4 (261631584197/500000000000 : ℝ) (261631584201/500000000000 : ℝ) (261631584191/500000000000 : ℝ) (523263168391/1000000000000 : ℝ) (130815792097/250000000000 : ℝ) (523263168397/1000000000000 : ℝ) (523263168387/1000000000000 : ℝ) (523263168397/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (603/4096 : ℝ))) 5 (130815792097/250000000000 : ℝ) (523263168397/1000000000000 : ℝ) (523263168387/1000000000000 : ℝ) (523263168397/1000000000000 : ℝ) (523263168387/1000000000000 : ℝ) (523263168397/1000000000000 : ℝ) (523263168387/1000000000000 : ℝ) (523263168397/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (603/4096 : ℝ))) 6 (523263168387/1000000000000 : ℝ) (523263168397/1000000000000 : ℝ) (523263168387/1000000000000 : ℝ) (523263168397/1000000000000 : ℝ) (523263168387/1000000000000 : ℝ) (523263168397/1000000000000 : ℝ) (523263168387/1000000000000 : ℝ) (523263168397/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (603/4096 : ℝ))) 7 (523263168387/1000000000000 : ℝ) (523263168397/1000000000000 : ℝ) (523263168387/1000000000000 : ℝ) (523263168397/1000000000000 : ℝ) (523263168387/1000000000000 : ℝ) (523263168397/1000000000000 : ℝ) (523263168387/1000000000000 : ℝ) (523263168397/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (603/4096 : ℝ)) hmem 8 (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ) (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (603/4096 : ℝ))) hcmem 8 (523263168387/1000000000000 : ℝ) (523263168397/1000000000000 : ℝ) (523263168387/1000000000000 : ℝ) (523263168397/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (603/4096 : ℝ)) (989566963697/1000000000000 : ℝ) (9895669637/10000000000 : ℝ) (523263168387/1000000000000 : ℝ) (523263168397/1000000000000 : ℝ) (415302800619/500000000000 : ℝ) (830605601257/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0588_exp_lower
  have heNumeric : (1009559639773/500000000000 : ℝ)/4 ≤ Real.exp (-683632945007/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009559639773/500000000000 : ℝ)/4 ≤ Real.exp ((301/2048 : ℝ)-(830605601257/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (301/2048 : ℝ) (603/4096 : ℝ) (830605601257/1000000000000 : ℝ) (1009559639773/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0589; no trusted numerical premise.
theorem cover7_leaf0589_exp_radius : (498685116442470413/500000000000000000 : ℝ) ≤ Real.exp ((-151/7168 : ℝ)/8) ∧ Real.exp ((-151/7168 : ℝ)/8) ≤ (997370232884940827/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-151/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0589_exp_lower : (229524172975255881/250000000000000000 : ℝ) ≤ Real.exp ((-683620520321/1000000000000 : ℝ)/8) ∧ Real.exp ((-683620520321/1000000000000 : ℝ)/8) ≤ (36723867676040941/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683620520321/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0589_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (16153154933/8000000000 : ℝ) ≤ 4*Real.exp (603/4096 : ℝ)*Real.exp (-mu (radius 7 (151/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (16153154933/8000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (151/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0589_exp_radius
  have hrNumeric : (122394310859/125000000000 : ℝ) ≤ Real.exp (-151/7168 : ℝ) ∧ Real.exp (-151/7168 : ℝ) ≤ (979154486873/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122394310859/125000000000 : ℝ) ≤ (radius 7 (151/1024 : ℝ)) ∧ (radius 7 (151/1024 : ℝ)) ≤ (979154486873/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (151/1024 : ℝ)) (122394310859/125000000000 : ℝ) (979154486873/1000000000000 : ℝ) (101558469411/500000000000 : ℝ) (203116938827/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (151/1024 : ℝ)) (122394310859/125000000000 : ℝ) (979154486873/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (151/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122394310859/125000000000 : ℝ) (979154486873/1000000000000 : ℝ) (247394310859/250000000000 : ℝ) (989577243437/1000000000000 : ℝ) (989522352891/1000000000000 : ℝ) (989522352893/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (151/1024 : ℝ)) 1 (247394310859/250000000000 : ℝ) (989577243437/1000000000000 : ℝ) (989522352891/1000000000000 : ℝ) (989522352893/1000000000000 : ℝ) (989549798163/1000000000000 : ℝ) (197909959633/200000000000 : ℝ) (494774898891/500000000000 : ℝ) (197909959557/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (151/1024 : ℝ)) 2 (989549798163/1000000000000 : ℝ) (197909959633/200000000000 : ℝ) (494774898891/500000000000 : ℝ) (197909959557/200000000000 : ℝ) (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ) (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (151/1024 : ℝ)) 3 (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ) (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ) (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ) (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (151/1024 : ℝ)) 4 (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ) (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ) (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ) (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (151/1024 : ℝ)) 5 (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ) (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ) (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ) (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (151/1024 : ℝ)) 6 (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ) (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ) (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ) (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (151/1024 : ℝ)) 7 (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ) (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ) (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ) (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (151/1024 : ℝ))) (101558469411/500000000000 : ℝ) (203116938827/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (151/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (101558469411/500000000000 : ℝ) (203116938827/1000000000000 : ℝ) (601558469411/1000000000000 : ℝ) (300779234707/500000000000 : ℝ) (45068496627/100000000000 : ℝ) (112671241569/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (151/1024 : ℝ))) 1 (601558469411/1000000000000 : ℝ) (300779234707/500000000000 : ℝ) (45068496627/100000000000 : ℝ) (112671241569/250000000000 : ℝ) (6576521473/12500000000 : ℝ) (105224343569/200000000000 : ℝ) (520685469833/1000000000000 : ℝ) (520685469839/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (151/1024 : ℝ))) 2 (6576521473/12500000000 : ℝ) (105224343569/200000000000 : ℝ) (520685469833/1000000000000 : ℝ) (520685469839/1000000000000 : ℝ) (130850898459/250000000000 : ℝ) (261701796921/500000000000 : ℝ) (130849133987/250000000000 : ℝ) (261698267977/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (151/1024 : ℝ))) 3 (130850898459/250000000000 : ℝ) (261701796921/500000000000 : ℝ) (130849133987/250000000000 : ℝ) (261698267977/500000000000 : ℝ) (130850016223/250000000000 : ℝ) (261700032449/500000000000 : ℝ) (6542500811/12500000000 : ℝ) (523400064887/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (151/1024 : ℝ))) 4 (130850016223/250000000000 : ℝ) (261700032449/500000000000 : ℝ) (6542500811/12500000000 : ℝ) (523400064887/1000000000000 : ℝ) (261700032443/500000000000 : ℝ) (523400064893/1000000000000 : ℝ) (104680012977/200000000000 : ℝ) (523400064893/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (151/1024 : ℝ))) 5 (261700032443/500000000000 : ℝ) (523400064893/1000000000000 : ℝ) (104680012977/200000000000 : ℝ) (523400064893/1000000000000 : ℝ) (104680012977/200000000000 : ℝ) (523400064893/1000000000000 : ℝ) (104680012977/200000000000 : ℝ) (523400064893/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (151/1024 : ℝ))) 6 (104680012977/200000000000 : ℝ) (523400064893/1000000000000 : ℝ) (104680012977/200000000000 : ℝ) (523400064893/1000000000000 : ℝ) (104680012977/200000000000 : ℝ) (523400064893/1000000000000 : ℝ) (104680012977/200000000000 : ℝ) (523400064893/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (151/1024 : ℝ))) 7 (104680012977/200000000000 : ℝ) (523400064893/1000000000000 : ℝ) (104680012977/200000000000 : ℝ) (523400064893/1000000000000 : ℝ) (104680012977/200000000000 : ℝ) (523400064893/1000000000000 : ℝ) (104680012977/200000000000 : ℝ) (523400064893/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (151/1024 : ℝ)) hmem 8 (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ) (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (151/1024 : ℝ))) hcmem 8 (104680012977/200000000000 : ℝ) (523400064893/1000000000000 : ℝ) (104680012977/200000000000 : ℝ) (523400064893/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (151/1024 : ℝ)) (247387449493/250000000000 : ℝ) (39581991919/40000000000 : ℝ) (104680012977/200000000000 : ℝ) (523400064893/1000000000000 : ℝ) (41541865859/50000000000 : ℝ) (207709329299/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0589_exp_lower
  have heNumeric : (16153154933/8000000000 : ℝ)/4 ≤ Real.exp (-683620520321/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (16153154933/8000000000 : ℝ)/4 ≤ Real.exp ((603/4096 : ℝ)-(207709329299/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (603/4096 : ℝ) (151/1024 : ℝ) (207709329299/250000000000 : ℝ) (16153154933/8000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0590; no trusted numerical premise.
theorem cover7_leaf0590_exp_radius : (39894635388211041/40000000000000000 : ℝ) ≤ Real.exp ((-605/28672 : ℝ)/8) ∧ Real.exp ((-605/28672 : ℝ)/8) ≤ (498682942352638013/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-605/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0590_exp_lower : (918098146972736873/1000000000000000000 : ℝ) ≤ Real.exp ((-683607841303/1000000000000 : ℝ)/8) ∧ Real.exp ((-683607841303/1000000000000 : ℝ)/8) ≤ (459049073486368437/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683607841303/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0590_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403833993511/200000000000 : ℝ) ≤ 4*Real.exp (151/1024 : ℝ)*Real.exp (-mu (radius 7 (605/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (403833993511/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (605/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0590_exp_radius
  have hrNumeric : (979120337269/1000000000000 : ℝ) ≤ Real.exp (-605/28672 : ℝ) ∧ Real.exp (-605/28672 : ℝ) ≤ (97912033727/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979120337269/1000000000000 : ℝ) ≤ (radius 7 (605/4096 : ℝ)) ∧ (radius 7 (605/4096 : ℝ)) ≤ (97912033727/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (605/4096 : ℝ)) (979120337269/1000000000000 : ℝ) (97912033727/100000000000 : ℝ) (10164074619/50000000000 : ℝ) (40656298477/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (605/4096 : ℝ)) (979120337269/1000000000000 : ℝ) (97912033727/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (605/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979120337269/1000000000000 : ℝ) (97912033727/100000000000 : ℝ) (494780084317/500000000000 : ℝ) (197912033727/200000000000 : ℝ) (989505097141/1000000000000 : ℝ) (989505097143/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (605/4096 : ℝ)) 1 (494780084317/500000000000 : ℝ) (197912033727/200000000000 : ℝ) (989505097141/1000000000000 : ℝ) (989505097143/1000000000000 : ℝ) (989532632887/1000000000000 : ℝ) (989532632889/1000000000000 : ℝ) (123691579063/125000000000 : ℝ) (494766316253/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (605/4096 : ℝ)) 2 (989532632887/1000000000000 : ℝ) (989532632889/1000000000000 : ℝ) (123691579063/125000000000 : ℝ) (494766316253/500000000000 : ℝ) (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ) (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (605/4096 : ℝ)) 3 (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ) (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ) (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ) (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (605/4096 : ℝ)) 4 (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ) (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ) (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ) (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (605/4096 : ℝ)) 5 (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ) (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ) (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ) (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (605/4096 : ℝ)) 6 (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ) (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ) (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ) (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (605/4096 : ℝ)) 7 (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ) (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ) (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ) (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (605/4096 : ℝ))) (10164074619/50000000000 : ℝ) (40656298477/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (605/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (10164074619/50000000000 : ℝ) (40656298477/200000000000 : ℝ) (60164074619/100000000000 : ℝ) (601640746193/1000000000000 : ℝ) (225433744357/500000000000 : ℝ) (450867488721/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (605/4096 : ℝ))) 1 (60164074619/100000000000 : ℝ) (601640746193/1000000000000 : ℝ) (225433744357/500000000000 : ℝ) (450867488721/1000000000000 : ℝ) (131563529363/250000000000 : ℝ) (526254117457/1000000000000 : ℝ) (52082650887/100000000000 : ℝ) (520826508877/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (605/4096 : ℝ))) 2 (131563529363/250000000000 : ℝ) (526254117457/1000000000000 : ℝ) (52082650887/100000000000 : ℝ) (520826508877/1000000000000 : ℝ) (523540313161/1000000000000 : ℝ) (523540313167/1000000000000 : ℝ) (20941331181/40000000000 : ℝ) (130883319883/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (605/4096 : ℝ))) 3 (523540313161/1000000000000 : ℝ) (523540313167/1000000000000 : ℝ) (20941331181/40000000000 : ℝ) (130883319883/250000000000 : ℝ) (523536796343/1000000000000 : ℝ) (10470735927/20000000000 : ℝ) (523536796331/1000000000000 : ℝ) (261768398169/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (605/4096 : ℝ))) 4 (523536796343/1000000000000 : ℝ) (10470735927/20000000000 : ℝ) (523536796331/1000000000000 : ℝ) (261768398169/500000000000 : ℝ) (523536796337/1000000000000 : ℝ) (65442099543/125000000000 : ℝ) (32721049771/62500000000 : ℝ) (65442099543/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (605/4096 : ℝ))) 5 (523536796337/1000000000000 : ℝ) (65442099543/125000000000 : ℝ) (32721049771/62500000000 : ℝ) (65442099543/125000000000 : ℝ) (32721049771/62500000000 : ℝ) (65442099543/125000000000 : ℝ) (32721049771/62500000000 : ℝ) (65442099543/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (605/4096 : ℝ))) 6 (32721049771/62500000000 : ℝ) (65442099543/125000000000 : ℝ) (32721049771/62500000000 : ℝ) (65442099543/125000000000 : ℝ) (32721049771/62500000000 : ℝ) (65442099543/125000000000 : ℝ) (32721049771/62500000000 : ℝ) (65442099543/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (605/4096 : ℝ))) 7 (32721049771/62500000000 : ℝ) (65442099543/125000000000 : ℝ) (32721049771/62500000000 : ℝ) (65442099543/125000000000 : ℝ) (32721049771/62500000000 : ℝ) (65442099543/125000000000 : ℝ) (32721049771/62500000000 : ℝ) (65442099543/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (605/4096 : ℝ)) hmem 8 (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ) (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (605/4096 : ℝ))) hcmem 8 (32721049771/62500000000 : ℝ) (65442099543/125000000000 : ℝ) (32721049771/62500000000 : ℝ) (65442099543/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (605/4096 : ℝ)) (197906526539/200000000000 : ℝ) (494766316349/500000000000 : ℝ) (32721049771/62500000000 : ℝ) (65442099543/125000000000 : ℝ) (831068778787/1000000000000 : ℝ) (831068778803/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0590_exp_lower
  have heNumeric : (403833993511/200000000000 : ℝ)/4 ≤ Real.exp (-683607841303/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403833993511/200000000000 : ℝ)/4 ≤ Real.exp ((151/1024 : ℝ)-(831068778803/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (151/1024 : ℝ) (605/4096 : ℝ) (831068778803/1000000000000 : ℝ) (403833993511/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0591; no trusted numerical premise.
theorem cover7_leaf0591_exp_radius : (997361536544567741/1000000000000000000 : ℝ) ≤ Real.exp ((-303/14336 : ℝ)/8) ∧ Real.exp ((-303/14336 : ℝ)/8) ≤ (498680768272283871/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-303/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0591_exp_lower : (229524907787542473/250000000000000000 : ℝ) ≤ Real.exp ((-42724681793/62500000000 : ℝ)/8) ∧ Real.exp ((-42724681793/62500000000 : ℝ)/8) ≤ (918099631150169893/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42724681793/62500000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0591_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252399510109/125000000000 : ℝ) ≤ 4*Real.exp (605/4096 : ℝ)*Real.exp (-mu (radius 7 (303/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (252399510109/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (303/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0591_exp_radius
  have hrNumeric : (979086188857/1000000000000 : ℝ) ≤ Real.exp (-303/14336 : ℝ) ∧ Real.exp (-303/14336 : ℝ) ≤ (489543094429/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979086188857/1000000000000 : ℝ) ≤ (radius 7 (303/2048 : ℝ)) ∧ (radius 7 (303/2048 : ℝ)) ≤ (489543094429/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (303/2048 : ℝ)) (979086188857/1000000000000 : ℝ) (489543094429/500000000000 : ℝ) (101722950689/500000000000 : ℝ) (203445901383/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (303/2048 : ℝ)) (979086188857/1000000000000 : ℝ) (489543094429/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (303/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979086188857/1000000000000 : ℝ) (489543094429/500000000000 : ℝ) (247385773607/250000000000 : ℝ) (989543094429/1000000000000 : ℝ) (247371960423/250000000000 : ℝ) (989487841693/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (303/2048 : ℝ)) 1 (247385773607/250000000000 : ℝ) (989543094429/1000000000000 : ℝ) (247371960423/250000000000 : ℝ) (989487841693/1000000000000 : ℝ) (49475773403/50000000000 : ℝ) (989515468061/1000000000000 : ℝ) (494757733837/500000000000 : ℝ) (247378866919/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (303/2048 : ℝ)) 2 (49475773403/50000000000 : ℝ) (989515468061/1000000000000 : ℝ) (494757733837/500000000000 : ℝ) (247378866919/250000000000 : ℝ) (989515467867/1000000000000 : ℝ) (989515467869/1000000000000 : ℝ) (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (303/2048 : ℝ)) 3 (989515467867/1000000000000 : ℝ) (989515467869/1000000000000 : ℝ) (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ) (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ) (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (303/2048 : ℝ)) 4 (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ) (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ) (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ) (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (303/2048 : ℝ)) 5 (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ) (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ) (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ) (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (303/2048 : ℝ)) 6 (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ) (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ) (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ) (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (303/2048 : ℝ)) 7 (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ) (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ) (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ) (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (303/2048 : ℝ))) (101722950689/500000000000 : ℝ) (203445901383/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (303/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (101722950689/500000000000 : ℝ) (203445901383/1000000000000 : ℝ) (601722950689/1000000000000 : ℝ) (150430737673/250000000000 : ℝ) (451049777051/1000000000000 : ℝ) (451049777057/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (303/2048 : ℝ))) 1 (601722950689/1000000000000 : ℝ) (150430737673/250000000000 : ℝ) (451049777051/1000000000000 : ℝ) (451049777057/1000000000000 : ℝ) (52638636387/100000000000 : ℝ) (4211090911/8000000000 : ℝ) (520967372063/1000000000000 : ℝ) (520967372069/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (303/2048 : ℝ))) 2 (52638636387/100000000000 : ℝ) (4211090911/8000000000 : ℝ) (520967372063/1000000000000 : ℝ) (520967372069/1000000000000 : ℝ) (261838433983/500000000000 : ℝ) (130919216993/250000000000 : ℝ) (261834929237/500000000000 : ℝ) (523669858481/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (303/2048 : ℝ))) 3 (261838433983/500000000000 : ℝ) (130919216993/250000000000 : ℝ) (261834929237/500000000000 : ℝ) (523669858481/1000000000000 : ℝ) (26183668161/50000000000 : ℝ) (523673363227/1000000000000 : ℝ) (65459170401/125000000000 : ℝ) (104734672643/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (303/2048 : ℝ))) 4 (26183668161/50000000000 : ℝ) (523673363227/1000000000000 : ℝ) (65459170401/125000000000 : ℝ) (104734672643/200000000000 : ℝ) (261836681607/500000000000 : ℝ) (523673363221/1000000000000 : ℝ) (523673363213/1000000000000 : ℝ) (523673363221/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (303/2048 : ℝ))) 5 (261836681607/500000000000 : ℝ) (523673363221/1000000000000 : ℝ) (523673363213/1000000000000 : ℝ) (523673363221/1000000000000 : ℝ) (523673363213/1000000000000 : ℝ) (523673363221/1000000000000 : ℝ) (523673363213/1000000000000 : ℝ) (523673363221/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (303/2048 : ℝ))) 6 (523673363213/1000000000000 : ℝ) (523673363221/1000000000000 : ℝ) (523673363213/1000000000000 : ℝ) (523673363221/1000000000000 : ℝ) (523673363213/1000000000000 : ℝ) (523673363221/1000000000000 : ℝ) (523673363213/1000000000000 : ℝ) (523673363221/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (303/2048 : ℝ))) 7 (523673363213/1000000000000 : ℝ) (523673363221/1000000000000 : ℝ) (523673363213/1000000000000 : ℝ) (523673363221/1000000000000 : ℝ) (523673363213/1000000000000 : ℝ) (523673363221/1000000000000 : ℝ) (523673363213/1000000000000 : ℝ) (523673363221/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (303/2048 : ℝ)) hmem 8 (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ) (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (303/2048 : ℝ))) hcmem 8 (523673363213/1000000000000 : ℝ) (523673363221/1000000000000 : ℝ) (523673363213/1000000000000 : ℝ) (523673363221/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (303/2048 : ℝ)) (494757733933/500000000000 : ℝ) (989515467869/1000000000000 : ℝ) (523673363213/1000000000000 : ℝ) (523673363221/1000000000000 : ℝ) (831299986797/1000000000000 : ℝ) (831299986813/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0591_exp_lower
  have heNumeric : (252399510109/125000000000 : ℝ)/4 ≤ Real.exp (-42724681793/62500000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252399510109/125000000000 : ℝ)/4 ≤ Real.exp ((605/4096 : ℝ)-(831299986813/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (605/4096 : ℝ) (303/2048 : ℝ) (831299986813/1000000000000 : ℝ) (252399510109/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0592; no trusted numerical premise.
theorem cover7_leaf0592_exp_radius : (249339297100703973/250000000000000000 : ℝ) ≤ Real.exp ((-607/28672 : ℝ)/8) ∧ Real.exp ((-607/28672 : ℝ)/8) ≤ (997357188402815893/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-607/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0592_exp_lower : (918101144349687001/1000000000000000000 : ℝ) ≤ Real.exp ((-341790861603/500000000000 : ℝ)/8) ∧ Real.exp ((-341790861603/500000000000 : ℝ)/8) ≤ (459050572174843501/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341790861603/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0592_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019222705121/1000000000000 : ℝ) ≤ 4*Real.exp (303/2048 : ℝ)*Real.exp (-mu (radius 7 (607/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019222705121/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (607/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0592_exp_radius
  have hrNumeric : (244763010409/250000000000 : ℝ) ≤ Real.exp (-607/28672 : ℝ) ∧ Real.exp (-607/28672 : ℝ) ≤ (979052041637/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (244763010409/250000000000 : ℝ) ≤ (radius 7 (607/4096 : ℝ)) ∧ (radius 7 (607/4096 : ℝ)) ≤ (979052041637/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (607/4096 : ℝ)) (244763010409/250000000000 : ℝ) (979052041637/1000000000000 : ℝ) (101805083083/500000000000 : ℝ) (50902541543/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (607/4096 : ℝ)) (244763010409/250000000000 : ℝ) (979052041637/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (607/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (244763010409/250000000000 : ℝ) (979052041637/1000000000000 : ℝ) (494763010409/500000000000 : ℝ) (989526020819/1000000000000 : ℝ) (61841911659/62500000000 : ℝ) (197894117309/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (607/4096 : ℝ)) 1 (494763010409/500000000000 : ℝ) (989526020819/1000000000000 : ℝ) (61841911659/62500000000 : ℝ) (197894117309/200000000000 : ℝ) (989498303681/1000000000000 : ℝ) (494749151841/500000000000 : ℝ) (247374575823/250000000000 : ℝ) (494749151647/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (607/4096 : ℝ)) 2 (989498303681/1000000000000 : ℝ) (494749151841/500000000000 : ℝ) (247374575823/250000000000 : ℝ) (494749151647/500000000000 : ℝ) (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ) (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (607/4096 : ℝ)) 3 (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ) (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ) (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ) (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (607/4096 : ℝ)) 4 (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ) (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ) (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ) (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (607/4096 : ℝ)) 5 (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ) (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ) (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ) (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (607/4096 : ℝ)) 6 (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ) (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ) (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ) (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (607/4096 : ℝ)) 7 (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ) (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ) (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ) (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (607/4096 : ℝ))) (101805083083/500000000000 : ℝ) (50902541543/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (607/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (101805083083/500000000000 : ℝ) (50902541543/250000000000 : ℝ) (601805083083/1000000000000 : ℝ) (300902541543/500000000000 : ℝ) (451231831951/1000000000000 : ℝ) (225615915979/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (607/4096 : ℝ))) 1 (601805083083/1000000000000 : ℝ) (300902541543/500000000000 : ℝ) (451231831951/1000000000000 : ℝ) (225615915979/500000000000 : ℝ) (526518457517/1000000000000 : ℝ) (263259228761/500000000000 : ℝ) (521108059923/1000000000000 : ℝ) (521108059929/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (607/4096 : ℝ))) 2 (526518457517/1000000000000 : ℝ) (263259228761/500000000000 : ℝ) (521108059923/1000000000000 : ℝ) (521108059929/1000000000000 : ℝ) (3273832867/6250000000 : ℝ) (261906629363/500000000000 : ℝ) (523806273263/1000000000000 : ℝ) (52380627327/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (607/4096 : ℝ))) 3 (3273832867/6250000000 : ℝ) (261906629363/500000000000 : ℝ) (523806273263/1000000000000 : ℝ) (52380627327/100000000000 : ℝ) (523809765991/1000000000000 : ℝ) (261904882999/500000000000 : ℝ) (523809765979/1000000000000 : ℝ) (523809765987/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (607/4096 : ℝ))) 4 (523809765991/1000000000000 : ℝ) (261904882999/500000000000 : ℝ) (523809765979/1000000000000 : ℝ) (523809765987/1000000000000 : ℝ) (104761953197/200000000000 : ℝ) (523809765993/1000000000000 : ℝ) (16369055187/31250000000 : ℝ) (523809765993/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (607/4096 : ℝ))) 5 (104761953197/200000000000 : ℝ) (523809765993/1000000000000 : ℝ) (16369055187/31250000000 : ℝ) (523809765993/1000000000000 : ℝ) (16369055187/31250000000 : ℝ) (523809765993/1000000000000 : ℝ) (16369055187/31250000000 : ℝ) (523809765993/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (607/4096 : ℝ))) 6 (16369055187/31250000000 : ℝ) (523809765993/1000000000000 : ℝ) (16369055187/31250000000 : ℝ) (523809765993/1000000000000 : ℝ) (16369055187/31250000000 : ℝ) (523809765993/1000000000000 : ℝ) (16369055187/31250000000 : ℝ) (523809765993/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (607/4096 : ℝ))) 7 (16369055187/31250000000 : ℝ) (523809765993/1000000000000 : ℝ) (16369055187/31250000000 : ℝ) (523809765993/1000000000000 : ℝ) (16369055187/31250000000 : ℝ) (523809765993/1000000000000 : ℝ) (16369055187/31250000000 : ℝ) (523809765993/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (607/4096 : ℝ)) hmem 8 (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ) (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (607/4096 : ℝ))) hcmem 8 (16369055187/31250000000 : ℝ) (523809765993/1000000000000 : ℝ) (16369055187/31250000000 : ℝ) (523809765993/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (607/4096 : ℝ)) (494749151743/500000000000 : ℝ) (966306937/976562500 : ℝ) (16369055187/31250000000 : ℝ) (523809765993/1000000000000 : ℝ) (831530941939/1000000000000 : ℝ) (207882735489/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0592_exp_lower
  have heNumeric : (2019222705121/1000000000000 : ℝ)/4 ≤ Real.exp (-341790861603/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019222705121/1000000000000 : ℝ)/4 ≤ Real.exp ((303/2048 : ℝ)-(207882735489/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (303/2048 : ℝ) (607/4096 : ℝ) (207882735489/250000000000 : ℝ) (2019222705121/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0593; no trusted numerical premise.
theorem cover7_leaf0593_exp_radius : (199470568056004079/200000000000000000 : ℝ) ≤ Real.exp ((-19/896 : ℝ)/8) ∧ Real.exp ((-19/896 : ℝ)/8) ≤ (249338210070005099/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-19/896 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0593_exp_lower : (918102686487884347/1000000000000000000 : ℝ) ≤ Real.exp ((-136713657117/200000000000 : ℝ)/8) ∧ Real.exp ((-136713657117/200000000000 : ℝ)/8) ≤ (229525671621971087/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-136713657117/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0593_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504812459713/250000000000 : ℝ) ≤ 4*Real.exp (607/4096 : ℝ)*Real.exp (-mu (radius 7 (19/128 : ℝ))) ∧ (2019/1000 : ℝ) < (504812459713/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (19/128 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0593_exp_radius
  have hrNumeric : (489508947803/500000000000 : ℝ) ≤ Real.exp (-19/896 : ℝ) ∧ Real.exp (-19/896 : ℝ) ≤ (979017895607/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (489508947803/500000000000 : ℝ) ≤ (radius 7 (19/128 : ℝ)) ∧ (radius 7 (19/128 : ℝ)) ≤ (979017895607/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (19/128 : ℝ)) (489508947803/500000000000 : ℝ) (979017895607/1000000000000 : ℝ) (40754857419/200000000000 : ℝ) (203774287101/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (19/128 : ℝ)) (489508947803/500000000000 : ℝ) (979017895607/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (19/128 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (489508947803/500000000000 : ℝ) (979017895607/1000000000000 : ℝ) (989508947803/1000000000000 : ℝ) (247377236951/250000000000 : ℝ) (61840833231/62500000000 : ℝ) (494726665849/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (19/128 : ℝ)) 1 (989508947803/1000000000000 : ℝ) (247377236951/250000000000 : ℝ) (61840833231/62500000000 : ℝ) (494726665849/500000000000 : ℝ) (989481139749/1000000000000 : ℝ) (989481139751/1000000000000 : ℝ) (494740569679/500000000000 : ℝ) (989481139361/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (19/128 : ℝ)) 2 (989481139749/1000000000000 : ℝ) (989481139751/1000000000000 : ℝ) (494740569679/500000000000 : ℝ) (989481139361/1000000000000 : ℝ) (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ) (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (19/128 : ℝ)) 3 (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ) (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ) (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ) (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (19/128 : ℝ)) 4 (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ) (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ) (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ) (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (19/128 : ℝ)) 5 (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ) (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ) (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ) (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (19/128 : ℝ)) 6 (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ) (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ) (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ) (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (19/128 : ℝ)) 7 (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ) (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ) (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ) (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (19/128 : ℝ))) (40754857419/200000000000 : ℝ) (203774287101/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (19/128 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (40754857419/200000000000 : ℝ) (203774287101/1000000000000 : ℝ) (601887143547/1000000000000 : ℝ) (601887143551/1000000000000 : ℝ) (90282730817/200000000000 : ℝ) (451413654093/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (19/128 : ℝ))) 1 (601887143547/1000000000000 : ℝ) (601887143551/1000000000000 : ℝ) (90282730817/200000000000 : ℝ) (451413654093/1000000000000 : ℝ) (16457824963/31250000000 : ℝ) (263325199411/500000000000 : ℝ) (260624286481/500000000000 : ℝ) (521248572969/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (19/128 : ℝ))) 2 (16457824963/31250000000 : ℝ) (263325199411/500000000000 : ℝ) (260624286481/500000000000 : ℝ) (521248572969/1000000000000 : ℝ) (523949485889/1000000000000 : ℝ) (65493685737/125000000000 : ℝ) (523942524359/1000000000000 : ℝ) (523942524367/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (19/128 : ℝ))) 3 (523949485889/1000000000000 : ℝ) (65493685737/125000000000 : ℝ) (523942524359/1000000000000 : ℝ) (523942524367/1000000000000 : ℝ) (130986501281/250000000000 : ℝ) (130986501283/250000000000 : ℝ) (65493250639/125000000000 : ℝ) (818665633/1562500000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (19/128 : ℝ))) 4 (130986501281/250000000000 : ℝ) (130986501283/250000000000 : ℝ) (65493250639/125000000000 : ℝ) (818665633/1562500000 : ℝ) (261973002559/500000000000 : ℝ) (261973002563/500000000000 : ℝ) (523946005117/1000000000000 : ℝ) (261973002563/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (19/128 : ℝ))) 5 (261973002559/500000000000 : ℝ) (261973002563/500000000000 : ℝ) (523946005117/1000000000000 : ℝ) (261973002563/500000000000 : ℝ) (523946005117/1000000000000 : ℝ) (261973002563/500000000000 : ℝ) (523946005117/1000000000000 : ℝ) (261973002563/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (19/128 : ℝ))) 6 (523946005117/1000000000000 : ℝ) (261973002563/500000000000 : ℝ) (523946005117/1000000000000 : ℝ) (261973002563/500000000000 : ℝ) (523946005117/1000000000000 : ℝ) (261973002563/500000000000 : ℝ) (523946005117/1000000000000 : ℝ) (261973002563/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (19/128 : ℝ))) 7 (523946005117/1000000000000 : ℝ) (261973002563/500000000000 : ℝ) (523946005117/1000000000000 : ℝ) (261973002563/500000000000 : ℝ) (523946005117/1000000000000 : ℝ) (261973002563/500000000000 : ℝ) (523946005117/1000000000000 : ℝ) (261973002563/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (19/128 : ℝ)) hmem 8 (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ) (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (19/128 : ℝ))) hcmem 8 (523946005117/1000000000000 : ℝ) (261973002563/500000000000 : ℝ) (523946005117/1000000000000 : ℝ) (261973002563/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (19/128 : ℝ)) (989481139553/1000000000000 : ℝ) (247370284889/250000000000 : ℝ) (523946005117/1000000000000 : ℝ) (261973002563/500000000000 : ℝ) (415880822471/500000000000 : ℝ) (5198510281/6250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0593_exp_lower
  have heNumeric : (504812459713/250000000000 : ℝ)/4 ≤ Real.exp (-136713657117/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504812459713/250000000000 : ℝ)/4 ≤ Real.exp ((607/4096 : ℝ)-(5198510281/6250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (607/4096 : ℝ) (19/128 : ℝ) (5198510281/6250000000 : ℝ) (504812459713/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0594; no trusted numerical premise.
theorem cover7_leaf0594_exp_radius : (62334280761011323/62500000000000000 : ℝ) ≤ Real.exp ((-87/4096 : ℝ)/8) ∧ Real.exp ((-87/4096 : ℝ)/8) ≤ (997348492176181169/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-87/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0594_exp_lower : (57381516092613707/62500000000000000 : ℝ) ≤ Real.exp ((-683554596549/1000000000000 : ℝ)/8) ∧ Real.exp ((-683554596549/1000000000000 : ℝ)/8) ≤ (918104257481819313/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683554596549/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0594_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (3230843969/1600000000 : ℝ) ≤ 4*Real.exp (19/128 : ℝ)*Real.exp (-mu (radius 7 (609/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (3230843969/1600000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (609/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0594_exp_radius
  have hrNumeric : (978983750767/1000000000000 : ℝ) ≤ Real.exp (-87/4096 : ℝ) ∧ Real.exp (-87/4096 : ℝ) ≤ (61186484423/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (978983750767/1000000000000 : ℝ) ≤ (radius 7 (609/4096 : ℝ)) ∧ (radius 7 (609/4096 : ℝ)) ≤ (61186484423/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (609/4096 : ℝ)) (978983750767/1000000000000 : ℝ) (61186484423/62500000000 : ℝ) (3186535383/15625000000 : ℝ) (203938264517/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (609/4096 : ℝ)) (978983750767/1000000000000 : ℝ) (61186484423/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (609/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (978983750767/1000000000000 : ℝ) (61186484423/62500000000 : ℝ) (989491875383/1000000000000 : ℝ) (123686484423/125000000000 : ℝ) (19788721543/20000000000 : ℝ) (30919877411/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (609/4096 : ℝ)) 1 (989491875383/1000000000000 : ℝ) (123686484423/125000000000 : ℝ) (19788721543/20000000000 : ℝ) (30919877411/31250000000 : ℝ) (494731988133/500000000000 : ℝ) (247365994067/250000000000 : ℝ) (989463975873/1000000000000 : ℝ) (7915711807/8000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (609/4096 : ℝ)) 2 (494731988133/500000000000 : ℝ) (247365994067/250000000000 : ℝ) (989463975873/1000000000000 : ℝ) (7915711807/8000000000 : ℝ) (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ) (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (609/4096 : ℝ)) 3 (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ) (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ) (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ) (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (609/4096 : ℝ)) 4 (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ) (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ) (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ) (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (609/4096 : ℝ)) 5 (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ) (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ) (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ) (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (609/4096 : ℝ)) 6 (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ) (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ) (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ) (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (609/4096 : ℝ)) 7 (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ) (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ) (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ) (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (609/4096 : ℝ))) (3186535383/15625000000 : ℝ) (203938264517/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (609/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3186535383/15625000000 : ℝ) (203938264517/1000000000000 : ℝ) (18811535383/31250000000 : ℝ) (601969132259/1000000000000 : ℝ) (11289881103/25000000000 : ℝ) (225797622063/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (609/4096 : ℝ))) 1 (18811535383/31250000000 : ℝ) (601969132259/1000000000000 : ℝ) (11289881103/25000000000 : ℝ) (225797622063/500000000000 : ℝ) (131695547047/250000000000 : ℝ) (526782188193/1000000000000 : ℝ) (52138891169/100000000000 : ℝ) (32586806981/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (609/4096 : ℝ))) 2 (131695547047/250000000000 : ℝ) (526782188193/1000000000000 : ℝ) (52138891169/100000000000 : ℝ) (32586806981/62500000000 : ℝ) (524085549939/1000000000000 : ℝ) (104817109989/200000000000 : ℝ) (52407861223/100000000000 : ℝ) (131019653059/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (609/4096 : ℝ))) 3 (524085549939/1000000000000 : ℝ) (104817109989/200000000000 : ℝ) (52407861223/100000000000 : ℝ) (131019653059/250000000000 : ℝ) (131020520271/250000000000 : ℝ) (524082081091/1000000000000 : ℝ) (524082081073/1000000000000 : ℝ) (13102052027/25000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (609/4096 : ℝ))) 4 (131020520271/250000000000 : ℝ) (524082081091/1000000000000 : ℝ) (524082081073/1000000000000 : ℝ) (13102052027/25000000000 : ℝ) (262041040539/500000000000 : ℝ) (262041040543/500000000000 : ℝ) (262041040539/500000000000 : ℝ) (262041040543/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (609/4096 : ℝ))) 5 (262041040539/500000000000 : ℝ) (262041040543/500000000000 : ℝ) (262041040539/500000000000 : ℝ) (262041040543/500000000000 : ℝ) (262041040539/500000000000 : ℝ) (262041040543/500000000000 : ℝ) (262041040539/500000000000 : ℝ) (262041040543/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (609/4096 : ℝ))) 6 (262041040539/500000000000 : ℝ) (262041040543/500000000000 : ℝ) (262041040539/500000000000 : ℝ) (262041040543/500000000000 : ℝ) (262041040539/500000000000 : ℝ) (262041040543/500000000000 : ℝ) (262041040539/500000000000 : ℝ) (262041040543/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (609/4096 : ℝ))) 7 (262041040539/500000000000 : ℝ) (262041040543/500000000000 : ℝ) (262041040539/500000000000 : ℝ) (262041040543/500000000000 : ℝ) (262041040539/500000000000 : ℝ) (262041040543/500000000000 : ℝ) (262041040539/500000000000 : ℝ) (262041040543/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (609/4096 : ℝ)) hmem 8 (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ) (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (609/4096 : ℝ))) hcmem 8 (262041040539/500000000000 : ℝ) (262041040543/500000000000 : ℝ) (262041040539/500000000000 : ℝ) (262041040543/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (609/4096 : ℝ)) (989463976069/1000000000000 : ℝ) (123682997009/125000000000 : ℝ) (262041040539/500000000000 : ℝ) (262041040543/500000000000 : ℝ) (831992096533/1000000000000 : ℝ) (831992096549/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0594_exp_lower
  have heNumeric : (3230843969/1600000000 : ℝ)/4 ≤ Real.exp (-683554596549/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (3230843969/1600000000 : ℝ)/4 ≤ Real.exp ((19/128 : ℝ)-(831992096549/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (19/128 : ℝ) (609/4096 : ℝ) (831992096549/1000000000000 : ℝ) (3230843969/1600000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0595; no trusted numerical premise.
theorem cover7_leaf0595_exp_radius : (62334009005706133/62500000000000000 : ℝ) ≤ Real.exp ((-305/14336 : ℝ)/8) ∧ Real.exp ((-305/14336 : ℝ)/8) ≤ (997344144091298129/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-305/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0595_exp_lower : (459052928624390481/500000000000000000 : ℝ) ≤ Real.exp ((-34177032841/50000000000 : ℝ)/8) ∧ Real.exp ((-34177032841/50000000000 : ℝ)/8) ≤ (918105857248780963/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-34177032841/50000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0595_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009652814501/500000000000 : ℝ) ≤ 4*Real.exp (609/4096 : ℝ)*Real.exp (-mu (radius 7 (305/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (1009652814501/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (305/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0595_exp_radius
  have hrNumeric : (978949607119/1000000000000 : ℝ) ≤ Real.exp (-305/14336 : ℝ) ∧ Real.exp (-305/14336 : ℝ) ≤ (12236870089/12500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (978949607119/1000000000000 : ℝ) ≤ (radius 7 (305/2048 : ℝ)) ∧ (radius 7 (305/2048 : ℝ)) ≤ (12236870089/12500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (305/2048 : ℝ)) (978949607119/1000000000000 : ℝ) (12236870089/12500000000 : ℝ) (204102098763/1000000000000 : ℝ) (204102098769/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (305/2048 : ℝ)) (978949607119/1000000000000 : ℝ) (12236870089/12500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (305/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (978949607119/1000000000000 : ℝ) (12236870089/12500000000 : ℝ) (989474803559/1000000000000 : ℝ) (24736870089/25000000000 : ℝ) (197883764581/200000000000 : ℝ) (494709411453/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (305/2048 : ℝ)) 1 (989474803559/1000000000000 : ℝ) (24736870089/25000000000 : ℝ) (197883764581/200000000000 : ℝ) (494709411453/500000000000 : ℝ) (61840425827/62500000000 : ℝ) (989446813233/1000000000000 : ℝ) (247361703209/250000000000 : ℝ) (494723406419/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (305/2048 : ℝ)) 2 (61840425827/62500000000 : ℝ) (989446813233/1000000000000 : ℝ) (247361703209/250000000000 : ℝ) (494723406419/500000000000 : ℝ) (494723406517/500000000000 : ℝ) (247361703259/250000000000 : ℝ) (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (305/2048 : ℝ)) 3 (494723406517/500000000000 : ℝ) (247361703259/250000000000 : ℝ) (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ) (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ) (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (305/2048 : ℝ)) 4 (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ) (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ) (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ) (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (305/2048 : ℝ)) 5 (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ) (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ) (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ) (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (305/2048 : ℝ)) 6 (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ) (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ) (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ) (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (305/2048 : ℝ)) 7 (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ) (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ) (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ) (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (305/2048 : ℝ))) (204102098763/1000000000000 : ℝ) (204102098769/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (305/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (204102098763/1000000000000 : ℝ) (204102098769/1000000000000 : ℝ) (602051049381/1000000000000 : ℝ) (120410209877/200000000000 : ℝ) (451776602717/1000000000000 : ℝ) (18071064109/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (305/2048 : ℝ))) 1 (602051049381/1000000000000 : ℝ) (120410209877/200000000000 : ℝ) (451776602717/1000000000000 : ℝ) (18071064109/40000000000 : ℝ) (526913826049/1000000000000 : ℝ) (105382765211/200000000000 : ℝ) (521529076611/1000000000000 : ℝ) (521529076619/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (305/2048 : ℝ))) 2 (526913826049/1000000000000 : ℝ) (105382765211/200000000000 : ℝ) (521529076611/1000000000000 : ℝ) (521529076619/1000000000000 : ℝ) (52422145133/100000000000 : ℝ) (524221451337/1000000000000 : ℝ) (262107268667/500000000000 : ℝ) (262107268671/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (305/2048 : ℝ))) 3 (52422145133/100000000000 : ℝ) (524221451337/1000000000000 : ℝ) (262107268667/500000000000 : ℝ) (262107268671/500000000000 : ℝ) (131054498583/250000000000 : ℝ) (26210899717/50000000000 : ℝ) (6552724929/12500000000 : ℝ) (524217994329/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (305/2048 : ℝ))) 4 (131054498583/250000000000 : ℝ) (26210899717/50000000000 : ℝ) (6552724929/12500000000 : ℝ) (524217994329/1000000000000 : ℝ) (262108997163/500000000000 : ℝ) (104843598867/200000000000 : ℝ) (20968719773/40000000000 : ℝ) (104843598867/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (305/2048 : ℝ))) 5 (262108997163/500000000000 : ℝ) (104843598867/200000000000 : ℝ) (20968719773/40000000000 : ℝ) (104843598867/200000000000 : ℝ) (20968719773/40000000000 : ℝ) (104843598867/200000000000 : ℝ) (20968719773/40000000000 : ℝ) (104843598867/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (305/2048 : ℝ))) 6 (20968719773/40000000000 : ℝ) (104843598867/200000000000 : ℝ) (20968719773/40000000000 : ℝ) (104843598867/200000000000 : ℝ) (20968719773/40000000000 : ℝ) (104843598867/200000000000 : ℝ) (20968719773/40000000000 : ℝ) (104843598867/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (305/2048 : ℝ))) 7 (20968719773/40000000000 : ℝ) (104843598867/200000000000 : ℝ) (20968719773/40000000000 : ℝ) (104843598867/200000000000 : ℝ) (20968719773/40000000000 : ℝ) (104843598867/200000000000 : ℝ) (20968719773/40000000000 : ℝ) (104843598867/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (305/2048 : ℝ)) hmem 8 (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ) (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (305/2048 : ℝ))) hcmem 8 (20968719773/40000000000 : ℝ) (104843598867/200000000000 : ℝ) (20968719773/40000000000 : ℝ) (104843598867/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (305/2048 : ℝ)) (989446813033/1000000000000 : ℝ) (247361703259/250000000000 : ℝ) (20968719773/40000000000 : ℝ) (104843598867/200000000000 : ℝ) (33288891897/40000000000 : ℝ) (166444459489/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0595_exp_lower
  have heNumeric : (1009652814501/500000000000 : ℝ)/4 ≤ Real.exp (-34177032841/50000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009652814501/500000000000 : ℝ)/4 ≤ Real.exp ((609/4096 : ℝ)-(166444459489/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (609/4096 : ℝ) (305/2048 : ℝ) (166444459489/200000000000 : ℝ) (1009652814501/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0596; no trusted numerical premise.
theorem cover7_leaf0596_exp_radius : (997339796025371193/1000000000000000000 : ℝ) ≤ Real.exp ((-611/28672 : ℝ)/8) ∧ Real.exp ((-611/28672 : ℝ)/8) ≤ (498669898012685597/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-611/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0596_exp_lower : (459053742853489301/500000000000000000 : ℝ) ≤ Real.exp ((-85440808389/125000000000 : ℝ)/8) ∧ Real.exp ((-85440808389/125000000000 : ℝ)/8) ≤ (918107485706978603/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85440808389/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0596_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019334282563/1000000000000 : ℝ) ≤ 4*Real.exp (305/2048 : ℝ)*Real.exp (-mu (radius 7 (611/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019334282563/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (611/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0596_exp_radius
  have hrNumeric : (489457732331/500000000000 : ℝ) ≤ Real.exp (-611/28672 : ℝ) ∧ Real.exp (-611/28672 : ℝ) ≤ (978915464663/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (489457732331/500000000000 : ℝ) ≤ (radius 7 (611/4096 : ℝ)) ∧ (radius 7 (611/4096 : ℝ)) ≤ (978915464663/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (611/4096 : ℝ)) (489457732331/500000000000 : ℝ) (978915464663/1000000000000 : ℝ) (102132895097/500000000000 : ℝ) (204265790199/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (611/4096 : ℝ)) (489457732331/500000000000 : ℝ) (978915464663/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (611/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (489457732331/500000000000 : ℝ) (978915464663/1000000000000 : ℝ) (989457732331/1000000000000 : ℝ) (247364433083/250000000000 : ℝ) (3091879903/3125000000 : ℝ) (494700784481/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (611/4096 : ℝ)) 1 (989457732331/1000000000000 : ℝ) (247364433083/250000000000 : ℝ) (3091879903/3125000000 : ℝ) (494700784481/500000000000 : ℝ) (197885930129/200000000000 : ℝ) (989429650647/1000000000000 : ℝ) (494714825123/500000000000 : ℝ) (989429650249/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (611/4096 : ℝ)) 2 (197885930129/200000000000 : ℝ) (989429650647/1000000000000 : ℝ) (494714825123/500000000000 : ℝ) (989429650249/1000000000000 : ℝ) (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ) (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (611/4096 : ℝ)) 3 (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ) (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ) (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ) (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (611/4096 : ℝ)) 4 (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ) (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ) (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ) (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (611/4096 : ℝ)) 5 (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ) (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ) (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ) (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (611/4096 : ℝ)) 6 (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ) (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ) (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ) (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (611/4096 : ℝ)) 7 (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ) (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ) (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ) (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (611/4096 : ℝ))) (102132895097/500000000000 : ℝ) (204265790199/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (611/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (102132895097/500000000000 : ℝ) (204265790199/1000000000000 : ℝ) (602132895097/1000000000000 : ℝ) (6021328951/10000000000 : ℝ) (451957730539/1000000000000 : ℝ) (90391546109/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (611/4096 : ℝ))) 1 (602132895097/1000000000000 : ℝ) (6021328951/10000000000 : ℝ) (451957730539/1000000000000 : ℝ) (90391546109/200000000000 : ℝ) (263522656409/500000000000 : ℝ) (527045312823/1000000000000 : ℝ) (65208633529/125000000000 : ℝ) (260834534119/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (611/4096 : ℝ))) 2 (263522656409/500000000000 : ℝ) (527045312823/1000000000000 : ℝ) (65208633529/125000000000 : ℝ) (260834534119/500000000000 : ℝ) (20974287621/40000000000 : ℝ) (524357190531/1000000000000 : ℝ) (524350300137/1000000000000 : ℝ) (524350300143/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (611/4096 : ℝ))) 3 (20974287621/40000000000 : ℝ) (524357190531/1000000000000 : ℝ) (524350300137/1000000000000 : ℝ) (524350300143/1000000000000 : ℝ) (524353745331/1000000000000 : ℝ) (524353745337/1000000000000 : ℝ) (524353745319/1000000000000 : ℝ) (262176872663/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (611/4096 : ℝ))) 4 (524353745331/1000000000000 : ℝ) (524353745337/1000000000000 : ℝ) (524353745319/1000000000000 : ℝ) (262176872663/500000000000 : ℝ) (20974149813/40000000000 : ℝ) (131088436333/250000000000 : ℝ) (131088436331/250000000000 : ℝ) (131088436333/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (611/4096 : ℝ))) 5 (20974149813/40000000000 : ℝ) (131088436333/250000000000 : ℝ) (131088436331/250000000000 : ℝ) (131088436333/250000000000 : ℝ) (131088436331/250000000000 : ℝ) (131088436333/250000000000 : ℝ) (131088436331/250000000000 : ℝ) (131088436333/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (611/4096 : ℝ))) 6 (131088436331/250000000000 : ℝ) (131088436333/250000000000 : ℝ) (131088436331/250000000000 : ℝ) (131088436333/250000000000 : ℝ) (131088436331/250000000000 : ℝ) (131088436333/250000000000 : ℝ) (131088436331/250000000000 : ℝ) (131088436333/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (611/4096 : ℝ))) 7 (131088436331/250000000000 : ℝ) (131088436333/250000000000 : ℝ) (131088436331/250000000000 : ℝ) (131088436333/250000000000 : ℝ) (131088436331/250000000000 : ℝ) (131088436333/250000000000 : ℝ) (131088436331/250000000000 : ℝ) (131088436333/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (611/4096 : ℝ)) hmem 8 (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ) (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (611/4096 : ℝ))) hcmem 8 (131088436331/250000000000 : ℝ) (131088436333/250000000000 : ℝ) (131088436331/250000000000 : ℝ) (131088436333/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (611/4096 : ℝ)) (197885930089/200000000000 : ℝ) (61839353153/62500000000 : ℝ) (131088436331/250000000000 : ℝ) (131088436333/250000000000 : ℝ) (416226124173/500000000000 : ℝ) (416226124181/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0596_exp_lower
  have heNumeric : (2019334282563/1000000000000 : ℝ)/4 ≤ Real.exp (-85440808389/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019334282563/1000000000000 : ℝ)/4 ≤ Real.exp ((305/2048 : ℝ)-(416226124181/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (305/2048 : ℝ) (611/4096 : ℝ) (416226124181/500000000000 : ℝ) (2019334282563/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0597; no trusted numerical premise.
theorem cover7_leaf0597_exp_radius : (997335447978400279/1000000000000000000 : ℝ) ≤ Real.exp ((-153/7168 : ℝ)/8) ∧ Real.exp ((-153/7168 : ℝ)/8) ≤ (24933386199460007/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-153/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0597_exp_lower : (114763642846655811/125000000000000000 : ℝ) ≤ Real.exp ((-683512028151/1000000000000 : ℝ)/8) ∧ Real.exp ((-683512028151/1000000000000 : ℝ)/8) ≤ (918109142773246489/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683512028151/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0597_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009681719931/500000000000 : ℝ) ≤ 4*Real.exp (611/4096 : ℝ)*Real.exp (-mu (radius 7 (153/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (1009681719931/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (153/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0597_exp_radius
  have hrNumeric : (195776264679/200000000000 : ℝ) ≤ Real.exp (-153/7168 : ℝ) ∧ Real.exp (-153/7168 : ℝ) ≤ (244720330849/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (195776264679/200000000000 : ℝ) ≤ (radius 7 (153/1024 : ℝ)) ∧ (radius 7 (153/1024 : ℝ)) ≤ (244720330849/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (153/1024 : ℝ)) (195776264679/200000000000 : ℝ) (244720330849/250000000000 : ℝ) (12776833697/62500000000 : ℝ) (102214669579/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (153/1024 : ℝ)) (195776264679/200000000000 : ℝ) (244720330849/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (153/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (195776264679/200000000000 : ℝ) (244720330849/250000000000 : ℝ) (989440661697/1000000000000 : ℝ) (494720330849/500000000000 : ℝ) (247346078829/250000000000 : ℝ) (494692157659/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (153/1024 : ℝ)) 1 (989440661697/1000000000000 : ℝ) (494720330849/500000000000 : ℝ) (247346078829/250000000000 : ℝ) (494692157659/500000000000 : ℝ) (494706244253/500000000000 : ℝ) (247353122127/250000000000 : ℝ) (197882497621/200000000000 : ℝ) (989412488107/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (153/1024 : ℝ)) 2 (494706244253/500000000000 : ℝ) (247353122127/250000000000 : ℝ) (197882497621/200000000000 : ℝ) (989412488107/1000000000000 : ℝ) (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ) (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (153/1024 : ℝ)) 3 (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ) (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ) (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ) (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (153/1024 : ℝ)) 4 (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ) (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ) (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ) (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (153/1024 : ℝ)) 5 (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ) (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ) (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ) (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (153/1024 : ℝ)) 6 (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ) (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ) (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ) (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (153/1024 : ℝ)) 7 (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ) (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ) (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ) (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (153/1024 : ℝ))) (12776833697/62500000000 : ℝ) (102214669579/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (153/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (12776833697/62500000000 : ℝ) (102214669579/500000000000 : ℝ) (75276833697/125000000000 : ℝ) (602214669579/1000000000000 : ℝ) (90427725649/200000000000 : ℝ) (452138628253/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (153/1024 : ℝ))) 1 (75276833697/125000000000 : ℝ) (602214669579/1000000000000 : ℝ) (90427725649/200000000000 : ℝ) (452138628253/1000000000000 : ℝ) (52717664891/100000000000 : ℝ) (131794162229/250000000000 : ℝ) (32613055441/62500000000 : ℝ) (521808887063/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (153/1024 : ℝ))) 2 (52717664891/100000000000 : ℝ) (131794162229/250000000000 : ℝ) (32613055441/62500000000 : ℝ) (521808887063/1000000000000 : ℝ) (524492767983/1000000000000 : ℝ) (52449276799/100000000000 : ℝ) (524485901097/1000000000000 : ℝ) (32780368819/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (153/1024 : ℝ))) 3 (524492767983/1000000000000 : ℝ) (52449276799/100000000000 : ℝ) (524485901097/1000000000000 : ℝ) (32780368819/62500000000 : ℝ) (26224466727/50000000000 : ℝ) (524489334547/1000000000000 : ℝ) (2048786463/3906250000 : ℝ) (65561166817/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (153/1024 : ℝ))) 4 (26224466727/50000000000 : ℝ) (524489334547/1000000000000 : ℝ) (2048786463/3906250000 : ℝ) (65561166817/125000000000 : ℝ) (262244667267/500000000000 : ℝ) (262244667271/500000000000 : ℝ) (524489334533/1000000000000 : ℝ) (262244667271/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (153/1024 : ℝ))) 5 (262244667267/500000000000 : ℝ) (262244667271/500000000000 : ℝ) (524489334533/1000000000000 : ℝ) (262244667271/500000000000 : ℝ) (524489334533/1000000000000 : ℝ) (262244667271/500000000000 : ℝ) (524489334533/1000000000000 : ℝ) (262244667271/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (153/1024 : ℝ))) 6 (524489334533/1000000000000 : ℝ) (262244667271/500000000000 : ℝ) (524489334533/1000000000000 : ℝ) (262244667271/500000000000 : ℝ) (524489334533/1000000000000 : ℝ) (262244667271/500000000000 : ℝ) (524489334533/1000000000000 : ℝ) (262244667271/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (153/1024 : ℝ))) 7 (524489334533/1000000000000 : ℝ) (262244667271/500000000000 : ℝ) (524489334533/1000000000000 : ℝ) (262244667271/500000000000 : ℝ) (524489334533/1000000000000 : ℝ) (262244667271/500000000000 : ℝ) (524489334533/1000000000000 : ℝ) (262244667271/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (153/1024 : ℝ)) hmem 8 (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ) (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (153/1024 : ℝ))) hcmem 8 (524489334533/1000000000000 : ℝ) (262244667271/500000000000 : ℝ) (524489334533/1000000000000 : ℝ) (262244667271/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (153/1024 : ℝ)) (197882497661/200000000000 : ℝ) (247353122077/250000000000 : ℝ) (524489334533/1000000000000 : ℝ) (262244667271/500000000000 : ℝ) (104085243751/125000000000 : ℝ) (416340975013/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0597_exp_lower
  have heNumeric : (1009681719931/500000000000 : ℝ)/4 ≤ Real.exp (-683512028151/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009681719931/500000000000 : ℝ)/4 ≤ Real.exp ((611/4096 : ℝ)-(416340975013/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (611/4096 : ℝ) (153/1024 : ℝ) (416340975013/500000000000 : ℝ) (1009681719931/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0598; no trusted numerical premise.
theorem cover7_leaf0598_exp_radius : (124666387493798163/125000000000000000 : ℝ) ≤ Real.exp ((-613/28672 : ℝ)/8) ∧ Real.exp ((-613/28672 : ℝ)/8) ≤ (199466219990077061/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-613/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0598_exp_lower : (57381926772984319/62500000000000000 : ℝ) ≤ Real.exp ((-341748670317/500000000000 : ℝ)/8) ∧ Real.exp ((-341748670317/500000000000 : ℝ)/8) ≤ (183622165673549821/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341748670317/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0598_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403878619903/200000000000 : ℝ) ≤ 4*Real.exp (153/1024 : ℝ)*Real.exp (-mu (radius 7 (613/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (403878619903/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (613/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0598_exp_radius
  have hrNumeric : (24471179583/25000000000 : ℝ) ≤ Real.exp (-613/28672 : ℝ) ∧ Real.exp (-613/28672 : ℝ) ≤ (978847183321/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24471179583/25000000000 : ℝ) ≤ (radius 7 (613/4096 : ℝ)) ∧ (radius 7 (613/4096 : ℝ)) ≤ (978847183321/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (613/4096 : ℝ)) (24471179583/25000000000 : ℝ) (978847183321/1000000000000 : ℝ) (51148186493/250000000000 : ℝ) (102296372989/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (613/4096 : ℝ)) (24471179583/25000000000 : ℝ) (978847183321/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (613/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24471179583/25000000000 : ℝ) (978847183321/1000000000000 : ℝ) (49471179583/50000000000 : ℝ) (989423591661/1000000000000 : ℝ) (494683530987/500000000000 : ℝ) (39574682479/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (613/4096 : ℝ)) 1 (49471179583/50000000000 : ℝ) (989423591661/1000000000000 : ℝ) (494683530987/500000000000 : ℝ) (39574682479/40000000000 : ℝ) (989395326817/1000000000000 : ℝ) (494697663409/500000000000 : ℝ) (989395326413/1000000000000 : ℝ) (197879065283/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (613/4096 : ℝ)) 2 (989395326817/1000000000000 : ℝ) (494697663409/500000000000 : ℝ) (989395326413/1000000000000 : ℝ) (197879065283/200000000000 : ℝ) (197879065323/200000000000 : ℝ) (989395326617/1000000000000 : ℝ) (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (613/4096 : ℝ)) 3 (197879065323/200000000000 : ℝ) (989395326617/1000000000000 : ℝ) (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ) (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ) (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (613/4096 : ℝ)) 4 (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ) (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ) (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ) (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (613/4096 : ℝ)) 5 (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ) (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ) (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ) (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (613/4096 : ℝ)) 6 (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ) (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ) (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ) (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (613/4096 : ℝ)) 7 (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ) (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ) (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ) (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (613/4096 : ℝ))) (51148186493/250000000000 : ℝ) (102296372989/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (613/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (51148186493/250000000000 : ℝ) (102296372989/500000000000 : ℝ) (301148186493/500000000000 : ℝ) (602296372989/1000000000000 : ℝ) (113079824121/250000000000 : ℝ) (452319296491/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (613/4096 : ℝ))) 1 (301148186493/500000000000 : ℝ) (602296372989/1000000000000 : ℝ) (113079824121/250000000000 : ℝ) (452319296491/1000000000000 : ℝ) (105461566947/200000000000 : ℝ) (26365391737/50000000000 : ℝ) (521948533577/1000000000000 : ℝ) (32621783349/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (613/4096 : ℝ))) 2 (105461566947/200000000000 : ℝ) (26365391737/50000000000 : ℝ) (521948533577/1000000000000 : ℝ) (32621783349/62500000000 : ℝ) (131157046039/250000000000 : ℝ) (262314092081/500000000000 : ℝ) (524621340667/1000000000000 : ℝ) (262310670337/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (613/4096 : ℝ))) 3 (131157046039/250000000000 : ℝ) (262314092081/500000000000 : ℝ) (524621340667/1000000000000 : ℝ) (262310670337/500000000000 : ℝ) (524624762411/1000000000000 : ℝ) (262312381209/500000000000 : ℝ) (655780953/1250000000 : ℝ) (524624762407/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (613/4096 : ℝ))) 4 (524624762411/1000000000000 : ℝ) (262312381209/500000000000 : ℝ) (655780953/1250000000 : ℝ) (524624762407/1000000000000 : ℝ) (104924952481/200000000000 : ℝ) (524624762413/1000000000000 : ℝ) (104924952481/200000000000 : ℝ) (524624762413/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (613/4096 : ℝ))) 5 (104924952481/200000000000 : ℝ) (524624762413/1000000000000 : ℝ) (104924952481/200000000000 : ℝ) (524624762413/1000000000000 : ℝ) (104924952481/200000000000 : ℝ) (524624762413/1000000000000 : ℝ) (104924952481/200000000000 : ℝ) (524624762413/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (613/4096 : ℝ))) 6 (104924952481/200000000000 : ℝ) (524624762413/1000000000000 : ℝ) (104924952481/200000000000 : ℝ) (524624762413/1000000000000 : ℝ) (104924952481/200000000000 : ℝ) (524624762413/1000000000000 : ℝ) (104924952481/200000000000 : ℝ) (524624762413/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (613/4096 : ℝ))) 7 (104924952481/200000000000 : ℝ) (524624762413/1000000000000 : ℝ) (104924952481/200000000000 : ℝ) (524624762413/1000000000000 : ℝ) (104924952481/200000000000 : ℝ) (524624762413/1000000000000 : ℝ) (104924952481/200000000000 : ℝ) (524624762413/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (613/4096 : ℝ)) hmem 8 (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ) (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (613/4096 : ℝ))) hcmem 8 (104924952481/200000000000 : ℝ) (524624762413/1000000000000 : ℝ) (104924952481/200000000000 : ℝ) (524624762413/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (613/4096 : ℝ)) (494697663307/500000000000 : ℝ) (989395326617/1000000000000 : ℝ) (104924952481/200000000000 : ℝ) (524624762413/1000000000000 : ℝ) (416455701559/500000000000 : ℝ) (416455701567/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0598_exp_lower
  have heNumeric : (403878619903/200000000000 : ℝ)/4 ≤ Real.exp (-341748670317/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403878619903/200000000000 : ℝ)/4 ≤ Real.exp ((153/1024 : ℝ)-(416455701567/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (153/1024 : ℝ) (613/4096 : ℝ) (416455701567/500000000000 : ℝ) (403878619903/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0599; no trusted numerical premise.
theorem cover7_leaf0599_exp_radius : (498663375970663093/500000000000000000 : ℝ) ≤ Real.exp ((-307/14336 : ℝ)/8) ∧ Real.exp ((-307/14336 : ℝ)/8) ≤ (997326751941326187/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-307/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0599_exp_lower : (114764067800972989/125000000000000000 : ℝ) ≤ Real.exp ((-683482405283/1000000000000 : ℝ)/8) ∧ Real.exp ((-683482405283/1000000000000 : ℝ)/8) ≤ (918112542407783913/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683482405283/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0599_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403884652017/200000000000 : ℝ) ≤ 4*Real.exp (613/4096 : ℝ)*Real.exp (-mu (radius 7 (307/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (403884652017/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (307/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0599_exp_radius
  have hrNumeric : (195762608887/200000000000 : ℝ) ≤ Real.exp (-307/14336 : ℝ) ∧ Real.exp (-307/14336 : ℝ) ≤ (244703261109/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (195762608887/200000000000 : ℝ) ≤ (radius 7 (307/2048 : ℝ)) ∧ (radius 7 (307/2048 : ℝ)) ≤ (244703261109/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (307/2048 : ℝ)) (195762608887/200000000000 : ℝ) (244703261109/250000000000 : ℝ) (204756011003/1000000000000 : ℝ) (99978521/488281250 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (307/2048 : ℝ)) (195762608887/200000000000 : ℝ) (244703261109/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (307/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (195762608887/200000000000 : ℝ) (244703261109/250000000000 : ℝ) (989406522217/1000000000000 : ℝ) (494703261109/500000000000 : ℝ) (247337452233/250000000000 : ℝ) (494674904467/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (307/2048 : ℝ)) 1 (989406522217/1000000000000 : ℝ) (494703261109/500000000000 : ℝ) (247337452233/250000000000 : ℝ) (494674904467/500000000000 : ℝ) (494689082787/500000000000 : ℝ) (123672270697/125000000000 : ℝ) (61836135323/62500000000 : ℝ) (98937816517/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (307/2048 : ℝ)) 2 (494689082787/500000000000 : ℝ) (123672270697/125000000000 : ℝ) (61836135323/62500000000 : ℝ) (98937816517/100000000000 : ℝ) (989378165371/1000000000000 : ℝ) (989378165373/1000000000000 : ℝ) (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (307/2048 : ℝ)) 3 (989378165371/1000000000000 : ℝ) (989378165373/1000000000000 : ℝ) (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ) (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ) (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (307/2048 : ℝ)) 4 (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ) (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ) (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ) (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (307/2048 : ℝ)) 5 (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ) (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ) (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ) (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (307/2048 : ℝ)) 6 (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ) (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ) (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ) (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (307/2048 : ℝ)) 7 (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ) (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ) (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ) (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (307/2048 : ℝ))) (204756011003/1000000000000 : ℝ) (99978521/488281250 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (307/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (204756011003/1000000000000 : ℝ) (99978521/488281250 : ℝ) (602378005501/1000000000000 : ℝ) (588259771/976562500 : ℝ) (226249867957/500000000000 : ℝ) (452499735921/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (307/2048 : ℝ))) 1 (602378005501/1000000000000 : ℝ) (588259771/976562500 : ℝ) (226249867957/500000000000 : ℝ) (452499735921/1000000000000 : ℝ) (527438870707/1000000000000 : ℝ) (527438870713/1000000000000 : ℝ) (261044004149/500000000000 : ℝ) (104417601661/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (307/2048 : ℝ))) 2 (527438870707/1000000000000 : ℝ) (527438870713/1000000000000 : ℝ) (261044004149/500000000000 : ℝ) (104417601661/200000000000 : ℝ) (262381719751/500000000000 : ℝ) (524763439509/1000000000000 : ℝ) (262378309653/500000000000 : ℝ) (262378309657/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (307/2048 : ℝ))) 3 (262381719751/500000000000 : ℝ) (524763439509/1000000000000 : ℝ) (262378309653/500000000000 : ℝ) (262378309657/500000000000 : ℝ) (131190007351/250000000000 : ℝ) (131190007353/250000000000 : ℝ) (32797501837/62500000000 : ℝ) (524760029401/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (307/2048 : ℝ))) 4 (131190007351/250000000000 : ℝ) (131190007353/250000000000 : ℝ) (32797501837/62500000000 : ℝ) (524760029401/1000000000000 : ℝ) (262380014699/500000000000 : ℝ) (524760029407/1000000000000 : ℝ) (524760029397/1000000000000 : ℝ) (524760029407/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (307/2048 : ℝ))) 5 (262380014699/500000000000 : ℝ) (524760029407/1000000000000 : ℝ) (524760029397/1000000000000 : ℝ) (524760029407/1000000000000 : ℝ) (524760029397/1000000000000 : ℝ) (524760029407/1000000000000 : ℝ) (524760029397/1000000000000 : ℝ) (524760029407/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (307/2048 : ℝ))) 6 (524760029397/1000000000000 : ℝ) (524760029407/1000000000000 : ℝ) (524760029397/1000000000000 : ℝ) (524760029407/1000000000000 : ℝ) (524760029397/1000000000000 : ℝ) (524760029407/1000000000000 : ℝ) (524760029397/1000000000000 : ℝ) (524760029407/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (307/2048 : ℝ))) 7 (524760029397/1000000000000 : ℝ) (524760029407/1000000000000 : ℝ) (524760029397/1000000000000 : ℝ) (524760029407/1000000000000 : ℝ) (524760029397/1000000000000 : ℝ) (524760029407/1000000000000 : ℝ) (524760029397/1000000000000 : ℝ) (524760029407/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (307/2048 : ℝ)) hmem 8 (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ) (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (307/2048 : ℝ))) hcmem 8 (524760029397/1000000000000 : ℝ) (524760029407/1000000000000 : ℝ) (524760029397/1000000000000 : ℝ) (524760029407/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (307/2048 : ℝ)) (98937816537/100000000000 : ℝ) (989378165373/1000000000000 : ℝ) (524760029397/1000000000000 : ℝ) (524760029407/1000000000000 : ℝ) (208285152097/250000000000 : ℝ) (104142576051/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0599_exp_lower
  have heNumeric : (403884652017/200000000000 : ℝ)/4 ≤ Real.exp (-683482405283/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403884652017/200000000000 : ℝ)/4 ≤ Real.exp ((613/4096 : ℝ)-(104142576051/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (613/4096 : ℝ) (307/2048 : ℝ) (104142576051/125000000000 : ℝ) (403884652017/200000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0575_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0575_certificate
#check SmaleRate.Proofs.cover7_leaf0576_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0576_certificate
#check SmaleRate.Proofs.cover7_leaf0577_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0577_certificate
#check SmaleRate.Proofs.cover7_leaf0578_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0578_certificate
#check SmaleRate.Proofs.cover7_leaf0579_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0579_certificate
#check SmaleRate.Proofs.cover7_leaf0580_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0580_certificate
#check SmaleRate.Proofs.cover7_leaf0581_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0581_certificate
#check SmaleRate.Proofs.cover7_leaf0582_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0582_certificate
#check SmaleRate.Proofs.cover7_leaf0583_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0583_certificate
#check SmaleRate.Proofs.cover7_leaf0584_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0584_certificate
#check SmaleRate.Proofs.cover7_leaf0585_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0585_certificate
#check SmaleRate.Proofs.cover7_leaf0586_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0586_certificate
#check SmaleRate.Proofs.cover7_leaf0587_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0587_certificate
#check SmaleRate.Proofs.cover7_leaf0588_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0588_certificate
#check SmaleRate.Proofs.cover7_leaf0589_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0589_certificate
#check SmaleRate.Proofs.cover7_leaf0590_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0590_certificate
#check SmaleRate.Proofs.cover7_leaf0591_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0591_certificate
#check SmaleRate.Proofs.cover7_leaf0592_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0592_certificate
#check SmaleRate.Proofs.cover7_leaf0593_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0593_certificate
#check SmaleRate.Proofs.cover7_leaf0594_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0594_certificate
#check SmaleRate.Proofs.cover7_leaf0595_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0595_certificate
#check SmaleRate.Proofs.cover7_leaf0596_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0596_certificate
#check SmaleRate.Proofs.cover7_leaf0597_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0597_certificate
#check SmaleRate.Proofs.cover7_leaf0598_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0598_certificate
#check SmaleRate.Proofs.cover7_leaf0599_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0599_certificate
