/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0525; no trusted numerical premise.
theorem cover7_leaf0525_exp_radius : (997489815254626687/1000000000000000000 : ℝ) ≤ Real.exp ((-1153/57344 : ℝ)/8) ∧ Real.exp ((-1153/57344 : ℝ)/8) ≤ (7792889181676771/7812500000000000 : ℝ) := by
  have h := exp_small_bounds ((-1153/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0525_exp_lower : (114761178878977649/125000000000000000 : ℝ) ≤ Real.exp ((-2734735157823/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734735157823/4000000000000 : ℝ)/8) ≤ (918089431031821193/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734735157823/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0525_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019016621149/1000000000000 : ℝ) ≤ 4*Real.exp (2305/16384 : ℝ)*Real.exp (-mu (radius 7 (1153/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019016621149/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1153/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0525_exp_radius
  have hrNumeric : (980094067841/1000000000000 : ℝ) ≤ Real.exp (-1153/57344 : ℝ) ∧ Real.exp (-1153/57344 : ℝ) ≤ (490047033921/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980094067841/1000000000000 : ℝ) ≤ (radius 7 (1153/8192 : ℝ)) ∧ (radius 7 (1153/8192 : ℝ)) ≤ (490047033921/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1153/8192 : ℝ)) (980094067841/1000000000000 : ℝ) (490047033921/500000000000 : ℝ) (775522149/3906250000 : ℝ) (3970673403/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1153/8192 : ℝ)) (980094067841/1000000000000 : ℝ) (490047033921/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1153/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980094067841/1000000000000 : ℝ) (490047033921/500000000000 : ℝ) (3093896981/3125000000 : ℝ) (990047033921/1000000000000 : ℝ) (197999400791/200000000000 : ℝ) (989997003957/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1153/8192 : ℝ)) 1 (3093896981/3125000000 : ℝ) (990047033921/1000000000000 : ℝ) (197999400791/200000000000 : ℝ) (989997003957/1000000000000 : ℝ) (990022018937/1000000000000 : ℝ) (990022018939/1000000000000 : ℝ) (990022018621/1000000000000 : ℝ) (990022018623/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1153/8192 : ℝ)) 2 (990022018937/1000000000000 : ℝ) (990022018939/1000000000000 : ℝ) (990022018621/1000000000000 : ℝ) (990022018623/1000000000000 : ℝ) (990022018779/1000000000000 : ℝ) (990022018781/1000000000000 : ℝ) (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1153/8192 : ℝ)) 3 (990022018779/1000000000000 : ℝ) (990022018781/1000000000000 : ℝ) (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ) (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ) (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1153/8192 : ℝ)) 4 (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ) (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ) (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ) (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1153/8192 : ℝ)) 5 (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ) (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ) (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ) (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1153/8192 : ℝ)) 6 (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ) (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ) (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ) (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1153/8192 : ℝ)) 7 (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ) (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ) (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ) (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1153/8192 : ℝ))) (775522149/3906250000 : ℝ) (3970673403/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1153/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (775522149/3906250000 : ℝ) (3970673403/20000000000 : ℝ) (4681772149/7812500000 : ℝ) (23970673403/40000000000 : ℝ) (445571172927/1000000000000 : ℝ) (89114234587/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1153/8192 : ℝ))) 1 (4681772149/7812500000 : ℝ) (23970673403/40000000000 : ℝ) (445571172927/1000000000000 : ℝ) (89114234587/200000000000 : ℝ) (522419003999/1000000000000 : ℝ) (104483800801/200000000000 : ℝ) (129183983769/250000000000 : ℝ) (516735935083/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1153/8192 : ℝ))) 2 (522419003999/1000000000000 : ℝ) (104483800801/200000000000 : ℝ) (129183983769/250000000000 : ℝ) (516735935083/1000000000000 : ℝ) (519577469537/1000000000000 : ℝ) (64947183693/125000000000 : ℝ) (259784849699/500000000000 : ℝ) (103913939881/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1153/8192 : ℝ))) 3 (519577469537/1000000000000 : ℝ) (64947183693/125000000000 : ℝ) (259784849699/500000000000 : ℝ) (103913939881/200000000000 : ℝ) (519573584467/1000000000000 : ℝ) (20782943379/40000000000 : ℝ) (129893396113/250000000000 : ℝ) (25978679223/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1153/8192 : ℝ))) 4 (519573584467/1000000000000 : ℝ) (20782943379/40000000000 : ℝ) (129893396113/250000000000 : ℝ) (25978679223/50000000000 : ℝ) (519573584459/1000000000000 : ℝ) (129893396117/250000000000 : ℝ) (519573584459/1000000000000 : ℝ) (129893396117/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1153/8192 : ℝ))) 5 (519573584459/1000000000000 : ℝ) (129893396117/250000000000 : ℝ) (519573584459/1000000000000 : ℝ) (129893396117/250000000000 : ℝ) (519573584459/1000000000000 : ℝ) (129893396117/250000000000 : ℝ) (519573584459/1000000000000 : ℝ) (129893396117/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1153/8192 : ℝ))) 6 (519573584459/1000000000000 : ℝ) (129893396117/250000000000 : ℝ) (519573584459/1000000000000 : ℝ) (129893396117/250000000000 : ℝ) (519573584459/1000000000000 : ℝ) (129893396117/250000000000 : ℝ) (519573584459/1000000000000 : ℝ) (129893396117/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1153/8192 : ℝ))) 7 (519573584459/1000000000000 : ℝ) (129893396117/250000000000 : ℝ) (519573584459/1000000000000 : ℝ) (129893396117/250000000000 : ℝ) (519573584459/1000000000000 : ℝ) (129893396117/250000000000 : ℝ) (519573584459/1000000000000 : ℝ) (129893396117/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1153/8192 : ℝ)) hmem 8 (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ) (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1153/8192 : ℝ))) hcmem 8 (519573584459/1000000000000 : ℝ) (129893396117/250000000000 : ℝ) (519573584459/1000000000000 : ℝ) (129893396117/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1153/8192 : ℝ)) (495011009389/500000000000 : ℝ) (990022018781/1000000000000 : ℝ) (519573584459/1000000000000 : ℝ) (129893396117/250000000000 : ℝ) (164873964919/200000000000 : ℝ) (206092456153/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0525_exp_lower
  have heNumeric : (2019016621149/1000000000000 : ℝ)/4 ≤ Real.exp (-2734735157823/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019016621149/1000000000000 : ℝ)/4 ≤ Real.exp ((2305/16384 : ℝ)-(206092456153/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2305/16384 : ℝ) (1153/8192 : ℝ) (206092456153/250000000000 : ℝ) (2019016621149/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0526; no trusted numerical premise.
theorem cover7_leaf0526_exp_radius : (49874436403879947/50000000000000000 : ℝ) ≤ Real.exp ((-2307/114688 : ℝ)/8) ∧ Real.exp ((-2307/114688 : ℝ)/8) ≤ (997488728077598941/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2307/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0526_exp_lower : (918089583139312759/1000000000000000000 : ℝ) ≤ Real.exp ((-1367364928059/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367364928059/2000000000000 : ℝ)/8) ≤ (22952239578482819/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367364928059/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0526_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019019297209/1000000000000 : ℝ) ≤ 4*Real.exp (1153/8192 : ℝ)*Real.exp (-mu (radius 7 (2307/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019019297209/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2307/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0526_exp_radius
  have hrNumeric : (122510690267/125000000000 : ℝ) ≤ Real.exp (-2307/114688 : ℝ) ∧ Real.exp (-2307/114688 : ℝ) ≤ (980085522137/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122510690267/125000000000 : ℝ) ≤ (radius 7 (2307/16384 : ℝ)) ∧ (radius 7 (2307/16384 : ℝ)) ≤ (980085522137/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2307/16384 : ℝ)) (122510690267/125000000000 : ℝ) (980085522137/1000000000000 : ℝ) (39715170551/200000000000 : ℝ) (198575852761/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2307/16384 : ℝ)) (122510690267/125000000000 : ℝ) (980085522137/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2307/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122510690267/125000000000 : ℝ) (980085522137/1000000000000 : ℝ) (247510690267/250000000000 : ℝ) (990042761069/1000000000000 : ℝ) (12374908599/12500000000 : ℝ) (989992687921/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2307/16384 : ℝ)) 1 (247510690267/250000000000 : ℝ) (990042761069/1000000000000 : ℝ) (12374908599/12500000000 : ℝ) (989992687921/1000000000000 : ℝ) (495008862247/500000000000 : ℝ) (198003544899/200000000000 : ℝ) (990017724177/1000000000000 : ℝ) (990017724179/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2307/16384 : ℝ)) 2 (495008862247/500000000000 : ℝ) (198003544899/200000000000 : ℝ) (990017724177/1000000000000 : ℝ) (990017724179/1000000000000 : ℝ) (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ) (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2307/16384 : ℝ)) 3 (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ) (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ) (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ) (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2307/16384 : ℝ)) 4 (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ) (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ) (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ) (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2307/16384 : ℝ)) 5 (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ) (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ) (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ) (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2307/16384 : ℝ)) 6 (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ) (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ) (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ) (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2307/16384 : ℝ)) 7 (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ) (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ) (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ) (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2307/16384 : ℝ))) (39715170551/200000000000 : ℝ) (198575852761/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2307/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39715170551/200000000000 : ℝ) (198575852761/1000000000000 : ℝ) (599287926377/1000000000000 : ℝ) (599287926381/1000000000000 : ℝ) (55702313231/125000000000 : ℝ) (3481394577/7812500000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2307/16384 : ℝ))) 1 (599287926377/1000000000000 : ℝ) (599287926381/1000000000000 : ℝ) (55702313231/125000000000 : ℝ) (3481394577/7812500000 : ℝ) (32653326007/62500000000 : ℝ) (522453216119/1000000000000 : ℝ) (258386237213/500000000000 : ℝ) (516772474433/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2307/16384 : ℝ))) 2 (32653326007/62500000000 : ℝ) (522453216119/1000000000000 : ℝ) (258386237213/500000000000 : ℝ) (516772474433/1000000000000 : ℝ) (519612845269/1000000000000 : ℝ) (129903211319/250000000000 : ℝ) (25980254101/50000000000 : ℝ) (129901270507/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2307/16384 : ℝ))) 3 (519612845269/1000000000000 : ℝ) (129903211319/250000000000 : ℝ) (25980254101/50000000000 : ℝ) (129901270507/250000000000 : ℝ) (129902240911/250000000000 : ℝ) (129902240913/250000000000 : ℝ) (51960896363/100000000000 : ℝ) (259804481819/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2307/16384 : ℝ))) 4 (129902240911/250000000000 : ℝ) (129902240913/250000000000 : ℝ) (51960896363/100000000000 : ℝ) (259804481819/500000000000 : ℝ) (519608963637/1000000000000 : ℝ) (103921792729/200000000000 : ℝ) (129902240909/250000000000 : ℝ) (103921792729/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2307/16384 : ℝ))) 5 (519608963637/1000000000000 : ℝ) (103921792729/200000000000 : ℝ) (129902240909/250000000000 : ℝ) (103921792729/200000000000 : ℝ) (129902240909/250000000000 : ℝ) (103921792729/200000000000 : ℝ) (129902240909/250000000000 : ℝ) (103921792729/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2307/16384 : ℝ))) 6 (129902240909/250000000000 : ℝ) (103921792729/200000000000 : ℝ) (129902240909/250000000000 : ℝ) (103921792729/200000000000 : ℝ) (129902240909/250000000000 : ℝ) (103921792729/200000000000 : ℝ) (129902240909/250000000000 : ℝ) (103921792729/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2307/16384 : ℝ))) 7 (129902240909/250000000000 : ℝ) (103921792729/200000000000 : ℝ) (129902240909/250000000000 : ℝ) (103921792729/200000000000 : ℝ) (129902240909/250000000000 : ℝ) (103921792729/200000000000 : ℝ) (129902240909/250000000000 : ℝ) (103921792729/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2307/16384 : ℝ)) hmem 8 (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ) (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2307/16384 : ℝ))) hcmem 8 (129902240909/250000000000 : ℝ) (103921792729/200000000000 : ℝ) (129902240909/250000000000 : ℝ) (103921792729/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2307/16384 : ℝ)) (198003544867/200000000000 : ℝ) (990017724337/1000000000000 : ℝ) (129902240909/250000000000 : ℝ) (103921792729/200000000000 : ℝ) (32977181373/40000000000 : ℝ) (412214767171/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0526_exp_lower
  have heNumeric : (2019019297209/1000000000000 : ℝ)/4 ≤ Real.exp (-1367364928059/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019019297209/1000000000000 : ℝ)/4 ≤ Real.exp ((1153/8192 : ℝ)-(412214767171/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1153/8192 : ℝ) (2307/16384 : ℝ) (412214767171/500000000000 : ℝ) (2019019297209/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0527; no trusted numerical premise.
theorem cover7_leaf0527_exp_radius : (997487640901756121/1000000000000000000 : ℝ) ≤ Real.exp ((-577/28672 : ℝ)/8) ∧ Real.exp ((-577/28672 : ℝ)/8) ≤ (498743820450878061/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-577/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0527_exp_lower : (459044868612312171/500000000000000000 : ℝ) ≤ Real.exp ((-2734724485477/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734724485477/4000000000000 : ℝ)/8) ≤ (918089737224624343/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734724485477/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0527_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019022008067/1000000000000 : ℝ) ≤ 4*Real.exp (2307/16384 : ℝ)*Real.exp (-mu (radius 7 (577/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019022008067/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (577/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0527_exp_radius
  have hrNumeric : (490038488253/500000000000 : ℝ) ≤ Real.exp (-577/28672 : ℝ) ∧ Real.exp (-577/28672 : ℝ) ≤ (980076976507/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490038488253/500000000000 : ℝ) ≤ (radius 7 (577/4096 : ℝ)) ∧ (radius 7 (577/4096 : ℝ)) ≤ (980076976507/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (577/4096 : ℝ)) (490038488253/500000000000 : ℝ) (980076976507/1000000000000 : ℝ) (198618025669/1000000000000 : ℝ) (7944721027/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (577/4096 : ℝ)) (490038488253/500000000000 : ℝ) (980076976507/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (577/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490038488253/500000000000 : ℝ) (980076976507/1000000000000 : ℝ) (990038488253/1000000000000 : ℝ) (495019244127/500000000000 : ℝ) (15468568311/15625000000 : ℝ) (197997674381/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (577/4096 : ℝ)) 1 (990038488253/1000000000000 : ℝ) (495019244127/500000000000 : ℝ) (15468568311/15625000000 : ℝ) (197997674381/200000000000 : ℝ) (495006715039/500000000000 : ℝ) (3093791969/3125000000 : ℝ) (990013429761/1000000000000 : ℝ) (990013429763/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (577/4096 : ℝ)) 2 (495006715039/500000000000 : ℝ) (3093791969/3125000000 : ℝ) (990013429761/1000000000000 : ℝ) (990013429763/1000000000000 : ℝ) (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ) (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (577/4096 : ℝ)) 3 (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ) (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ) (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ) (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (577/4096 : ℝ)) 4 (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ) (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ) (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ) (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (577/4096 : ℝ)) 5 (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ) (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ) (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ) (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (577/4096 : ℝ)) 6 (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ) (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ) (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ) (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (577/4096 : ℝ)) 7 (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ) (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ) (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ) (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (577/4096 : ℝ))) (198618025669/1000000000000 : ℝ) (7944721027/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (577/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (198618025669/1000000000000 : ℝ) (7944721027/40000000000 : ℝ) (299654506417/500000000000 : ℝ) (299654506419/500000000000 : ℝ) (445665822863/1000000000000 : ℝ) (445665822871/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (577/4096 : ℝ))) 1 (299654506417/500000000000 : ℝ) (299654506419/500000000000 : ℝ) (445665822863/1000000000000 : ℝ) (445665822871/1000000000000 : ℝ) (65310927231/125000000000 : ℝ) (104497483571/200000000000 : ℝ) (516809001811/1000000000000 : ℝ) (516809001819/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (577/4096 : ℝ))) 2 (65310927231/125000000000 : ℝ) (104497483571/200000000000 : ℝ) (516809001811/1000000000000 : ℝ) (516809001819/1000000000000 : ℝ) (519648209829/1000000000000 : ℝ) (519648209837/1000000000000 : ℝ) (64955056683/125000000000 : ℝ) (519640453473/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (577/4096 : ℝ))) 3 (519648209829/1000000000000 : ℝ) (519648209837/1000000000000 : ℝ) (64955056683/125000000000 : ℝ) (519640453473/1000000000000 : ℝ) (259822165823/500000000000 : ℝ) (103928866331/200000000000 : ℝ) (32477770727/62500000000 : ℝ) (519644331641/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (577/4096 : ℝ))) 4 (259822165823/500000000000 : ℝ) (103928866331/200000000000 : ℝ) (32477770727/62500000000 : ℝ) (519644331641/1000000000000 : ℝ) (519644331639/1000000000000 : ℝ) (4059721341/7812500000 : ℝ) (259822165819/500000000000 : ℝ) (4059721341/7812500000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (577/4096 : ℝ))) 5 (519644331639/1000000000000 : ℝ) (4059721341/7812500000 : ℝ) (259822165819/500000000000 : ℝ) (4059721341/7812500000 : ℝ) (259822165819/500000000000 : ℝ) (4059721341/7812500000 : ℝ) (259822165819/500000000000 : ℝ) (4059721341/7812500000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (577/4096 : ℝ))) 6 (259822165819/500000000000 : ℝ) (4059721341/7812500000 : ℝ) (259822165819/500000000000 : ℝ) (4059721341/7812500000 : ℝ) (259822165819/500000000000 : ℝ) (4059721341/7812500000 : ℝ) (259822165819/500000000000 : ℝ) (4059721341/7812500000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (577/4096 : ℝ))) 7 (259822165819/500000000000 : ℝ) (4059721341/7812500000 : ℝ) (259822165819/500000000000 : ℝ) (4059721341/7812500000 : ℝ) (259822165819/500000000000 : ℝ) (4059721341/7812500000 : ℝ) (259822165819/500000000000 : ℝ) (4059721341/7812500000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (577/4096 : ℝ)) hmem 8 (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ) (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (577/4096 : ℝ))) hcmem 8 (259822165819/500000000000 : ℝ) (4059721341/7812500000 : ℝ) (259822165819/500000000000 : ℝ) (4059721341/7812500000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (577/4096 : ℝ)) (990013429919/1000000000000 : ℝ) (495006714961/500000000000 : ℝ) (259822165819/500000000000 : ℝ) (4059721341/7812500000 : ℝ) (412244613409/500000000000 : ℝ) (412244613419/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0527_exp_lower
  have heNumeric : (2019022008067/1000000000000 : ℝ)/4 ≤ Real.exp (-2734724485477/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019022008067/1000000000000 : ℝ)/4 ≤ Real.exp ((2307/16384 : ℝ)-(412244613419/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2307/16384 : ℝ) (577/4096 : ℝ) (412244613419/500000000000 : ℝ) (2019022008067/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0528; no trusted numerical premise.
theorem cover7_leaf0528_exp_radius : (997486553727098229/1000000000000000000 : ℝ) ≤ Real.exp ((-2309/114688 : ℝ)/8) ∧ Real.exp ((-2309/114688 : ℝ)/8) ≤ (99748655372709823/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2309/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0528_exp_lower : (183617978657161199/200000000000000000 : ℝ) ≤ Real.exp ((-170919940373/250000000000 : ℝ)/8) ∧ Real.exp ((-170919940373/250000000000 : ℝ)/8) ≤ (229522473321451499/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-170919940373/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0528_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019024753691/1000000000000 : ℝ) ≤ 4*Real.exp (577/4096 : ℝ)*Real.exp (-mu (radius 7 (2309/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019024753691/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2309/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0528_exp_radius
  have hrNumeric : (19601368619/20000000000 : ℝ) ≤ Real.exp (-2309/114688 : ℝ) ∧ Real.exp (-2309/114688 : ℝ) ≤ (980068430951/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (19601368619/20000000000 : ℝ) ≤ (radius 7 (2309/16384 : ℝ)) ∧ (radius 7 (2309/16384 : ℝ)) ≤ (980068430951/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2309/16384 : ℝ)) (19601368619/20000000000 : ℝ) (980068430951/1000000000000 : ℝ) (99330094449/500000000000 : ℝ) (24832523613/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2309/16384 : ℝ)) (19601368619/20000000000 : ℝ) (980068430951/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2309/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (19601368619/20000000000 : ℝ) (980068430951/1000000000000 : ℝ) (39601368619/40000000000 : ℝ) (247508553869/250000000000 : ℝ) (494992027953/500000000000 : ℝ) (247496013977/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2309/16384 : ℝ)) 1 (39601368619/40000000000 : ℝ) (247508553869/250000000000 : ℝ) (494992027953/500000000000 : ℝ) (247496013977/250000000000 : ℝ) (99000913569/100000000000 : ℝ) (247502283923/250000000000 : ℝ) (247502283843/250000000000 : ℝ) (7920073083/8000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2309/16384 : ℝ)) 2 (99000913569/100000000000 : ℝ) (247502283923/250000000000 : ℝ) (247502283843/250000000000 : ℝ) (7920073083/8000000000 : ℝ) (990009135531/1000000000000 : ℝ) (495004567767/500000000000 : ℝ) (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2309/16384 : ℝ)) 3 (990009135531/1000000000000 : ℝ) (495004567767/500000000000 : ℝ) (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ) (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ) (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2309/16384 : ℝ)) 4 (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ) (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ) (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ) (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2309/16384 : ℝ)) 5 (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ) (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ) (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ) (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2309/16384 : ℝ)) 6 (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ) (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ) (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ) (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2309/16384 : ℝ)) 7 (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ) (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ) (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ) (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2309/16384 : ℝ))) (99330094449/500000000000 : ℝ) (24832523613/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2309/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (99330094449/500000000000 : ℝ) (24832523613/125000000000 : ℝ) (599330094449/1000000000000 : ℝ) (149832523613/250000000000 : ℝ) (445713123991/1000000000000 : ℝ) (222856561999/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2309/16384 : ℝ))) 1 (599330094449/1000000000000 : ℝ) (149832523613/250000000000 : ℝ) (445713123991/1000000000000 : ℝ) (222856561999/500000000000 : ℝ) (26126080461/50000000000 : ℝ) (20900864369/40000000000 : ℝ) (516845517247/1000000000000 : ℝ) (516845517253/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2309/16384 : ℝ))) 2 (26126080461/50000000000 : ℝ) (20900864369/40000000000 : ℝ) (516845517247/1000000000000 : ℝ) (516845517253/1000000000000 : ℝ) (519683563233/1000000000000 : ℝ) (519683563239/1000000000000 : ℝ) (519675813743/1000000000000 : ℝ) (415740651/800000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2309/16384 : ℝ))) 3 (519683563233/1000000000000 : ℝ) (519683563239/1000000000000 : ℝ) (519675813743/1000000000000 : ℝ) (415740651/800000000 : ℝ) (64959961061/125000000000 : ℝ) (103935937699/200000000000 : ℝ) (519679688473/1000000000000 : ℝ) (519679688481/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2309/16384 : ℝ))) 4 (64959961061/125000000000 : ℝ) (103935937699/200000000000 : ℝ) (519679688473/1000000000000 : ℝ) (519679688481/1000000000000 : ℝ) (3247998053/6250000000 : ℝ) (64959961061/125000000000 : ℝ) (3247998053/6250000000 : ℝ) (64959961061/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2309/16384 : ℝ))) 5 (3247998053/6250000000 : ℝ) (64959961061/125000000000 : ℝ) (3247998053/6250000000 : ℝ) (64959961061/125000000000 : ℝ) (3247998053/6250000000 : ℝ) (64959961061/125000000000 : ℝ) (3247998053/6250000000 : ℝ) (64959961061/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2309/16384 : ℝ))) 6 (3247998053/6250000000 : ℝ) (64959961061/125000000000 : ℝ) (3247998053/6250000000 : ℝ) (64959961061/125000000000 : ℝ) (3247998053/6250000000 : ℝ) (64959961061/125000000000 : ℝ) (3247998053/6250000000 : ℝ) (64959961061/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2309/16384 : ℝ))) 7 (3247998053/6250000000 : ℝ) (64959961061/125000000000 : ℝ) (3247998053/6250000000 : ℝ) (64959961061/125000000000 : ℝ) (3247998053/6250000000 : ℝ) (64959961061/125000000000 : ℝ) (3247998053/6250000000 : ℝ) (64959961061/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2309/16384 : ℝ)) hmem 8 (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ) (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2309/16384 : ℝ))) hcmem 8 (3247998053/6250000000 : ℝ) (64959961061/125000000000 : ℝ) (3247998053/6250000000 : ℝ) (64959961061/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2309/16384 : ℝ)) (99000913553/100000000000 : ℝ) (495004567767/500000000000 : ℝ) (3247998053/6250000000 : ℝ) (64959961061/125000000000 : ℝ) (8245489021/10000000000 : ℝ) (824548902117/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0528_exp_lower
  have heNumeric : (2019024753691/1000000000000 : ℝ)/4 ≤ Real.exp (-170919940373/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019024753691/1000000000000 : ℝ)/4 ≤ Real.exp ((577/4096 : ℝ)-(824548902117/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (577/4096 : ℝ) (2309/16384 : ℝ) (824548902117/1000000000000 : ℝ) (2019024753691/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0529; no trusted numerical premise.
theorem cover7_leaf0529_exp_radius : (997485466553625263/1000000000000000000 : ℝ) ≤ Real.exp ((-165/8192 : ℝ)/8) ∧ Real.exp ((-165/8192 : ℝ)/8) ≤ (62342841659601579/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-165/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0529_exp_lower : (183618010264388127/200000000000000000 : ℝ) ≤ Real.exp ((-2734713537623/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734713537623/4000000000000 : ℝ)/8) ≤ (229522512830485159/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734713537623/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0529_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (126189220879/62500000000 : ℝ) ≤ 4*Real.exp (2309/16384 : ℝ)*Real.exp (-mu (radius 7 (1155/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (126189220879/62500000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1155/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0529_exp_radius
  have hrNumeric : (980059885469/1000000000000 : ℝ) ≤ Real.exp (-165/8192 : ℝ) ∧ Real.exp (-165/8192 : ℝ) ≤ (98005988547/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980059885469/1000000000000 : ℝ) ≤ (radius 7 (1155/8192 : ℝ)) ∧ (radius 7 (1155/8192 : ℝ)) ≤ (98005988547/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1155/8192 : ℝ)) (980059885469/1000000000000 : ℝ) (98005988547/100000000000 : ℝ) (198702342443/1000000000000 : ℝ) (198702342449/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1155/8192 : ℝ)) (980059885469/1000000000000 : ℝ) (98005988547/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1155/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980059885469/1000000000000 : ℝ) (98005988547/100000000000 : ℝ) (495014971367/500000000000 : ℝ) (198005988547/200000000000 : ℝ) (123747467491/125000000000 : ℝ) (98997973993/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1155/8192 : ℝ)) 1 (495014971367/500000000000 : ℝ) (198005988547/200000000000 : ℝ) (123747467491/125000000000 : ℝ) (98997973993/100000000000 : ℝ) (990004841331/1000000000000 : ℝ) (990004841333/1000000000000 : ℝ) (247501210253/250000000000 : ℝ) (198000968203/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1155/8192 : ℝ)) 2 (990004841331/1000000000000 : ℝ) (990004841333/1000000000000 : ℝ) (247501210253/250000000000 : ℝ) (198000968203/200000000000 : ℝ) (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ) (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1155/8192 : ℝ)) 3 (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ) (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ) (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ) (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1155/8192 : ℝ)) 4 (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ) (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ) (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ) (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1155/8192 : ℝ)) 5 (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ) (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ) (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ) (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1155/8192 : ℝ)) 6 (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ) (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ) (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ) (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1155/8192 : ℝ)) 7 (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ) (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ) (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ) (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1155/8192 : ℝ))) (198702342443/1000000000000 : ℝ) (198702342449/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1155/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (198702342443/1000000000000 : ℝ) (198702342449/1000000000000 : ℝ) (599351171221/1000000000000 : ℝ) (23974046849/40000000000 : ℝ) (111440102309/250000000000 : ℝ) (111440102311/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1155/8192 : ℝ))) 1 (599351171221/1000000000000 : ℝ) (23974046849/40000000000 : ℝ) (111440102309/250000000000 : ℝ) (111440102311/250000000000 : ℝ) (130638947557/250000000000 : ℝ) (104511158047/200000000000 : ℝ) (103376404147/200000000000 : ℝ) (258441010371/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1155/8192 : ℝ))) 2 (130638947557/250000000000 : ℝ) (104511158047/200000000000 : ℝ) (103376404147/200000000000 : ℝ) (258441010371/500000000000 : ℝ) (519718905481/1000000000000 : ℝ) (519718905489/1000000000000 : ℝ) (259855581429/500000000000 : ℝ) (259855581433/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1155/8192 : ℝ))) 3 (519718905481/1000000000000 : ℝ) (519718905489/1000000000000 : ℝ) (259855581429/500000000000 : ℝ) (259855581433/500000000000 : ℝ) (519715034169/1000000000000 : ℝ) (259857517089/500000000000 : ℝ) (103943006831/200000000000 : ℝ) (129928758541/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1155/8192 : ℝ))) 4 (519715034169/1000000000000 : ℝ) (259857517089/500000000000 : ℝ) (103943006831/200000000000 : ℝ) (129928758541/250000000000 : ℝ) (259857517081/500000000000 : ℝ) (519715034171/1000000000000 : ℝ) (519715034161/1000000000000 : ℝ) (519715034171/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1155/8192 : ℝ))) 5 (259857517081/500000000000 : ℝ) (519715034171/1000000000000 : ℝ) (519715034161/1000000000000 : ℝ) (519715034171/1000000000000 : ℝ) (519715034161/1000000000000 : ℝ) (519715034171/1000000000000 : ℝ) (519715034161/1000000000000 : ℝ) (519715034171/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1155/8192 : ℝ))) 6 (519715034161/1000000000000 : ℝ) (519715034171/1000000000000 : ℝ) (519715034161/1000000000000 : ℝ) (519715034171/1000000000000 : ℝ) (519715034161/1000000000000 : ℝ) (519715034171/1000000000000 : ℝ) (519715034161/1000000000000 : ℝ) (519715034171/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1155/8192 : ℝ))) 7 (519715034161/1000000000000 : ℝ) (519715034171/1000000000000 : ℝ) (519715034161/1000000000000 : ℝ) (519715034171/1000000000000 : ℝ) (519715034161/1000000000000 : ℝ) (519715034171/1000000000000 : ℝ) (519715034161/1000000000000 : ℝ) (519715034171/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1155/8192 : ℝ)) hmem 8 (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ) (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1155/8192 : ℝ))) hcmem 8 (519715034161/1000000000000 : ℝ) (519715034171/1000000000000 : ℝ) (519715034161/1000000000000 : ℝ) (519715034171/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1155/8192 : ℝ)) (990004841171/1000000000000 : ℝ) (495002420587/500000000000 : ℝ) (519715034161/1000000000000 : ℝ) (519715034171/1000000000000 : ℝ) (103076070021/125000000000 : ℝ) (824608560187/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0529_exp_lower
  have heNumeric : (126189220879/62500000000 : ℝ)/4 ≤ Real.exp (-2734713537623/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (126189220879/62500000000 : ℝ)/4 ≤ Real.exp ((2309/16384 : ℝ)-(824608560187/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2309/16384 : ℝ) (1155/8192 : ℝ) (824608560187/1000000000000 : ℝ) (126189220879/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0530; no trusted numerical premise.
theorem cover7_leaf0530_exp_radius : (997484379381337221/1000000000000000000 : ℝ) ≤ Real.exp ((-2311/114688 : ℝ)/8) ∧ Real.exp ((-2311/114688 : ℝ)/8) ≤ (498742189690668611/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2311/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0530_exp_lower : (45904510566548179/50000000000000000 : ℝ) ≤ Real.exp ((-1367353980257/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367353980257/2000000000000 : ℝ)/8) ≤ (918090211330963581/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367353980257/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0530_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019030349151/1000000000000 : ℝ) ≤ 4*Real.exp (1155/8192 : ℝ)*Real.exp (-mu (radius 7 (2311/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019030349151/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2311/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0530_exp_radius
  have hrNumeric : (490025670031/500000000000 : ℝ) ≤ Real.exp (-2311/114688 : ℝ) ∧ Real.exp (-2311/114688 : ℝ) ≤ (980051340063/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490025670031/500000000000 : ℝ) ≤ (radius 7 (2311/16384 : ℝ)) ∧ (radius 7 (2311/16384 : ℝ)) ≤ (980051340063/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2311/16384 : ℝ)) (490025670031/500000000000 : ℝ) (980051340063/1000000000000 : ℝ) (39748897263/200000000000 : ℝ) (198744486321/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2311/16384 : ℝ)) (490025670031/500000000000 : ℝ) (980051340063/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2311/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490025670031/500000000000 : ℝ) (980051340063/1000000000000 : ℝ) (990025670031/1000000000000 : ℝ) (61876604377/62500000000 : ℝ) (30936731999/31250000000 : ℝ) (98997542397/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2311/16384 : ℝ)) 1 (990025670031/1000000000000 : ℝ) (61876604377/62500000000 : ℝ) (30936731999/31250000000 : ℝ) (98997542397/100000000000 : ℝ) (990000546999/1000000000000 : ℝ) (990000547001/1000000000000 : ℝ) (24750013667/25000000000 : ℝ) (990000546683/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2311/16384 : ℝ)) 2 (990000546999/1000000000000 : ℝ) (990000547001/1000000000000 : ℝ) (24750013667/25000000000 : ℝ) (990000546683/1000000000000 : ℝ) (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ) (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2311/16384 : ℝ)) 3 (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ) (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ) (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ) (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2311/16384 : ℝ)) 4 (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ) (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ) (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ) (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2311/16384 : ℝ)) 5 (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ) (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ) (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ) (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2311/16384 : ℝ)) 6 (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ) (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ) (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ) (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2311/16384 : ℝ)) 7 (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ) (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ) (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ) (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2311/16384 : ℝ))) (39748897263/200000000000 : ℝ) (198744486321/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2311/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39748897263/200000000000 : ℝ) (198744486321/1000000000000 : ℝ) (599372243157/1000000000000 : ℝ) (599372243161/1000000000000 : ℝ) (222903839309/500000000000 : ℝ) (3566461429/8000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2311/16384 : ℝ))) 1 (599372243157/1000000000000 : ℝ) (599372243161/1000000000000 : ℝ) (222903839309/500000000000 : ℝ) (3566461429/8000000000 : ℝ) (522589960887/1000000000000 : ℝ) (522589960893/1000000000000 : ℝ) (516918512291/1000000000000 : ℝ) (258459256149/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2311/16384 : ℝ))) 2 (522589960887/1000000000000 : ℝ) (522589960893/1000000000000 : ℝ) (516918512291/1000000000000 : ℝ) (258459256149/500000000000 : ℝ) (519754236589/1000000000000 : ℝ) (129938559149/250000000000 : ℝ) (20789860033/40000000000 : ℝ) (16242078151/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2311/16384 : ℝ))) 3 (519754236589/1000000000000 : ℝ) (129938559149/250000000000 : ℝ) (20789860033/40000000000 : ℝ) (16242078151/31250000000 : ℝ) (519750368707/1000000000000 : ℝ) (259875184357/500000000000 : ℝ) (129937592173/250000000000 : ℝ) (5197503687/10000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2311/16384 : ℝ))) 4 (519750368707/1000000000000 : ℝ) (259875184357/500000000000 : ℝ) (129937592173/250000000000 : ℝ) (5197503687/10000000000 : ℝ) (519750368699/1000000000000 : ℝ) (519750368707/1000000000000 : ℝ) (519750368699/1000000000000 : ℝ) (519750368707/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2311/16384 : ℝ))) 5 (519750368699/1000000000000 : ℝ) (519750368707/1000000000000 : ℝ) (519750368699/1000000000000 : ℝ) (519750368707/1000000000000 : ℝ) (519750368699/1000000000000 : ℝ) (519750368707/1000000000000 : ℝ) (519750368699/1000000000000 : ℝ) (519750368707/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2311/16384 : ℝ))) 6 (519750368699/1000000000000 : ℝ) (519750368707/1000000000000 : ℝ) (519750368699/1000000000000 : ℝ) (519750368707/1000000000000 : ℝ) (519750368699/1000000000000 : ℝ) (519750368707/1000000000000 : ℝ) (519750368699/1000000000000 : ℝ) (519750368707/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2311/16384 : ℝ))) 7 (519750368699/1000000000000 : ℝ) (519750368707/1000000000000 : ℝ) (519750368699/1000000000000 : ℝ) (519750368707/1000000000000 : ℝ) (519750368699/1000000000000 : ℝ) (519750368707/1000000000000 : ℝ) (519750368699/1000000000000 : ℝ) (519750368707/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2311/16384 : ℝ)) hmem 8 (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ) (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2311/16384 : ℝ))) hcmem 8 (519750368699/1000000000000 : ℝ) (519750368707/1000000000000 : ℝ) (519750368699/1000000000000 : ℝ) (519750368707/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2311/16384 : ℝ)) (990000546839/1000000000000 : ℝ) (495000273421/500000000000 : ℝ) (519750368699/1000000000000 : ℝ) (519750368707/1000000000000 : ℝ) (824668201049/1000000000000 : ℝ) (412334100533/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0530_exp_lower
  have heNumeric : (2019030349151/1000000000000 : ℝ)/4 ≤ Real.exp (-1367353980257/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019030349151/1000000000000 : ℝ)/4 ≤ Real.exp ((1155/8192 : ℝ)-(412334100533/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1155/8192 : ℝ) (2311/16384 : ℝ) (412334100533/500000000000 : ℝ) (2019030349151/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0531; no trusted numerical premise.
theorem cover7_leaf0531_exp_radius : (997483292210234103/1000000000000000000 : ℝ) ≤ Real.exp ((-289/14336 : ℝ)/8) ∧ Real.exp ((-289/14336 : ℝ)/8) ≤ (124685411526279263/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-289/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0531_exp_lower : (918090373311843009/1000000000000000000 : ℝ) ≤ Real.exp ((-2734702314677/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734702314677/4000000000000 : ℝ)/8) ≤ (91809037331184301/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734702314677/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0531_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504758299733/250000000000 : ℝ) ≤ 4*Real.exp (2311/16384 : ℝ)*Real.exp (-mu (radius 7 (289/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (504758299733/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (289/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0531_exp_radius
  have hrNumeric : (98004279473/100000000000 : ℝ) ≤ Real.exp (-289/14336 : ℝ) ∧ Real.exp (-289/14336 : ℝ) ≤ (980042794731/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98004279473/100000000000 : ℝ) ≤ (radius 7 (289/2048 : ℝ)) ∧ (radius 7 (289/2048 : ℝ)) ≤ (980042794731/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (289/2048 : ℝ)) (98004279473/100000000000 : ℝ) (980042794731/1000000000000 : ℝ) (39757324103/200000000000 : ℝ) (198786620521/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (289/2048 : ℝ)) (98004279473/100000000000 : ℝ) (980042794731/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (289/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98004279473/100000000000 : ℝ) (980042794731/1000000000000 : ℝ) (198004279473/200000000000 : ℝ) (495010698683/500000000000 : ℝ) (989971108027/1000000000000 : ℝ) (989971108029/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (289/2048 : ℝ)) 1 (198004279473/200000000000 : ℝ) (495010698683/500000000000 : ℝ) (989971108027/1000000000000 : ℝ) (989971108029/1000000000000 : ℝ) (123749531587/125000000000 : ℝ) (494998126349/500000000000 : ℝ) (123749531547/125000000000 : ℝ) (989996252379/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (289/2048 : ℝ)) 2 (123749531587/125000000000 : ℝ) (494998126349/500000000000 : ℝ) (123749531547/125000000000 : ℝ) (989996252379/1000000000000 : ℝ) (123749531567/125000000000 : ℝ) (989996252539/1000000000000 : ℝ) (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (289/2048 : ℝ)) 3 (123749531567/125000000000 : ℝ) (989996252539/1000000000000 : ℝ) (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ) (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ) (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (289/2048 : ℝ)) 4 (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ) (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ) (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ) (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (289/2048 : ℝ)) 5 (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ) (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ) (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ) (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (289/2048 : ℝ)) 6 (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ) (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ) (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ) (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (289/2048 : ℝ)) 7 (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ) (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ) (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ) (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (289/2048 : ℝ))) (39757324103/200000000000 : ℝ) (198786620521/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (289/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39757324103/200000000000 : ℝ) (198786620521/1000000000000 : ℝ) (599393310257/1000000000000 : ℝ) (599393310261/1000000000000 : ℝ) (445854932141/1000000000000 : ℝ) (445854932149/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (289/2048 : ℝ))) 1 (599393310257/1000000000000 : ℝ) (599393310261/1000000000000 : ℝ) (445854932141/1000000000000 : ℝ) (445854932149/1000000000000 : ℝ) (522624121199/1000000000000 : ℝ) (104524824241/200000000000 : ℝ) (516954991919/1000000000000 : ℝ) (258477495963/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (289/2048 : ℝ))) 2 (522624121199/1000000000000 : ℝ) (104524824241/200000000000 : ℝ) (516954991919/1000000000000 : ℝ) (258477495963/500000000000 : ℝ) (519789556559/1000000000000 : ℝ) (259894778283/500000000000 : ℝ) (259890913823/500000000000 : ℝ) (519781827653/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (289/2048 : ℝ))) 3 (519789556559/1000000000000 : ℝ) (259894778283/500000000000 : ℝ) (259890913823/500000000000 : ℝ) (519781827653/1000000000000 : ℝ) (259892846051/500000000000 : ℝ) (51978569211/100000000000 : ℝ) (64973211511/125000000000 : ℝ) (8121651439/15625000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (289/2048 : ℝ))) 4 (259892846051/500000000000 : ℝ) (51978569211/100000000000 : ℝ) (64973211511/125000000000 : ℝ) (8121651439/15625000000 : ℝ) (103957138419/200000000000 : ℝ) (519785692103/1000000000000 : ℝ) (259892846047/500000000000 : ℝ) (519785692103/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (289/2048 : ℝ))) 5 (103957138419/200000000000 : ℝ) (519785692103/1000000000000 : ℝ) (259892846047/500000000000 : ℝ) (519785692103/1000000000000 : ℝ) (259892846047/500000000000 : ℝ) (519785692103/1000000000000 : ℝ) (259892846047/500000000000 : ℝ) (519785692103/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (289/2048 : ℝ))) 6 (259892846047/500000000000 : ℝ) (519785692103/1000000000000 : ℝ) (259892846047/500000000000 : ℝ) (519785692103/1000000000000 : ℝ) (259892846047/500000000000 : ℝ) (519785692103/1000000000000 : ℝ) (259892846047/500000000000 : ℝ) (519785692103/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (289/2048 : ℝ))) 7 (259892846047/500000000000 : ℝ) (519785692103/1000000000000 : ℝ) (259892846047/500000000000 : ℝ) (519785692103/1000000000000 : ℝ) (259892846047/500000000000 : ℝ) (519785692103/1000000000000 : ℝ) (259892846047/500000000000 : ℝ) (519785692103/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (289/2048 : ℝ)) hmem 8 (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ) (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (289/2048 : ℝ))) hcmem 8 (259892846047/500000000000 : ℝ) (519785692103/1000000000000 : ℝ) (259892846047/500000000000 : ℝ) (519785692103/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (289/2048 : ℝ)) (197999250507/200000000000 : ℝ) (989996252539/1000000000000 : ℝ) (259892846047/500000000000 : ℝ) (519785692103/1000000000000 : ℝ) (103090978093/125000000000 : ℝ) (824727824763/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0531_exp_lower
  have heNumeric : (504758299733/250000000000 : ℝ)/4 ≤ Real.exp (-2734702314677/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504758299733/250000000000 : ℝ)/4 ≤ Real.exp ((2311/16384 : ℝ)-(824727824763/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2311/16384 : ℝ) (289/2048 : ℝ) (824727824763/1000000000000 : ℝ) (504758299733/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0532; no trusted numerical premise.
theorem cover7_leaf0532_exp_radius : (498741102520157953/500000000000000000 : ℝ) ≤ Real.exp ((-2313/114688 : ℝ)/8) ∧ Real.exp ((-2313/114688 : ℝ)/8) ≤ (997482205040315907/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2313/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0532_exp_lower : (183618107452548757/200000000000000000 : ℝ) ≤ Real.exp ((-170918537511/250000000000 : ℝ)/8) ∧ Real.exp ((-170918537511/250000000000 : ℝ)/8) ≤ (459045268631371893/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-170918537511/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0532_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (16152288667/8000000000 : ℝ) ≤ 4*Real.exp (289/2048 : ℝ)*Real.exp (-mu (radius 7 (2313/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (16152288667/8000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2313/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0532_exp_radius
  have hrNumeric : (3828258787/3906250000 : ℝ) ≤ Real.exp (-2313/114688 : ℝ) ∧ Real.exp (-2313/114688 : ℝ) ≤ (980034249473/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (3828258787/3906250000 : ℝ) ≤ (radius 7 (2313/16384 : ℝ)) ∧ (radius 7 (2313/16384 : ℝ)) ≤ (980034249473/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2313/16384 : ℝ)) (3828258787/3906250000 : ℝ) (980034249473/1000000000000 : ℝ) (99414372527/500000000000 : ℝ) (9941437253/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2313/16384 : ℝ)) (3828258787/3906250000 : ℝ) (980034249473/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2313/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (3828258787/3906250000 : ℝ) (980034249473/1000000000000 : ℝ) (7734508787/7812500000 : ℝ) (990017124737/1000000000000 : ℝ) (197993358421/200000000000 : ℝ) (989966792107/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2313/16384 : ℝ)) 1 (7734508787/7812500000 : ℝ) (990017124737/1000000000000 : ℝ) (197993358421/200000000000 : ℝ) (989966792107/1000000000000 : ℝ) (49499597921/50000000000 : ℝ) (494995979211/500000000000 : ℝ) (9899919581/10000000000 : ℝ) (989991958103/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2313/16384 : ℝ)) 2 (49499597921/50000000000 : ℝ) (494995979211/500000000000 : ℝ) (9899919581/10000000000 : ℝ) (989991958103/1000000000000 : ℝ) (49499597913/50000000000 : ℝ) (989991958263/1000000000000 : ℝ) (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2313/16384 : ℝ)) 3 (49499597913/50000000000 : ℝ) (989991958263/1000000000000 : ℝ) (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ) (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ) (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2313/16384 : ℝ)) 4 (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ) (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ) (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ) (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2313/16384 : ℝ)) 5 (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ) (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ) (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ) (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2313/16384 : ℝ)) 6 (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ) (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ) (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ) (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2313/16384 : ℝ)) 7 (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ) (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ) (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ) (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2313/16384 : ℝ))) (99414372527/500000000000 : ℝ) (9941437253/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2313/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (99414372527/500000000000 : ℝ) (9941437253/50000000000 : ℝ) (599414372527/1000000000000 : ℝ) (59941437253/100000000000 : ℝ) (13934442807/31250000000 : ℝ) (55737771229/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2313/16384 : ℝ))) 1 (599414372527/1000000000000 : ℝ) (59941437253/100000000000 : ℝ) (13934442807/31250000000 : ℝ) (55737771229/125000000000 : ℝ) (20906330847/40000000000 : ℝ) (522658271181/1000000000000 : ℝ) (516991459633/1000000000000 : ℝ) (516991459639/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2313/16384 : ℝ))) 2 (20906330847/40000000000 : ℝ) (522658271181/1000000000000 : ℝ) (516991459633/1000000000000 : ℝ) (516991459639/1000000000000 : ℝ) (129956216351/250000000000 : ℝ) (51982486541/100000000000 : ℝ) (259908571667/500000000000 : ℝ) (519817143341/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2313/16384 : ℝ))) 3 (129956216351/250000000000 : ℝ) (51982486541/100000000000 : ℝ) (259908571667/500000000000 : ℝ) (519817143341/1000000000000 : ℝ) (519821004369/1000000000000 : ℝ) (64977625547/125000000000 : ℝ) (259910502177/500000000000 : ℝ) (259910502181/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2313/16384 : ℝ))) 4 (519821004369/1000000000000 : ℝ) (64977625547/125000000000 : ℝ) (259910502177/500000000000 : ℝ) (259910502181/500000000000 : ℝ) (519821004361/1000000000000 : ℝ) (519821004369/1000000000000 : ℝ) (519821004361/1000000000000 : ℝ) (519821004369/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2313/16384 : ℝ))) 5 (519821004361/1000000000000 : ℝ) (519821004369/1000000000000 : ℝ) (519821004361/1000000000000 : ℝ) (519821004369/1000000000000 : ℝ) (519821004361/1000000000000 : ℝ) (519821004369/1000000000000 : ℝ) (519821004361/1000000000000 : ℝ) (519821004369/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2313/16384 : ℝ))) 6 (519821004361/1000000000000 : ℝ) (519821004369/1000000000000 : ℝ) (519821004361/1000000000000 : ℝ) (519821004369/1000000000000 : ℝ) (519821004361/1000000000000 : ℝ) (519821004369/1000000000000 : ℝ) (519821004361/1000000000000 : ℝ) (519821004369/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2313/16384 : ℝ))) 7 (519821004361/1000000000000 : ℝ) (519821004369/1000000000000 : ℝ) (519821004361/1000000000000 : ℝ) (519821004369/1000000000000 : ℝ) (519821004361/1000000000000 : ℝ) (519821004369/1000000000000 : ℝ) (519821004361/1000000000000 : ℝ) (519821004369/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2313/16384 : ℝ)) hmem 8 (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ) (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2313/16384 : ℝ))) hcmem 8 (519821004361/1000000000000 : ℝ) (519821004369/1000000000000 : ℝ) (519821004361/1000000000000 : ℝ) (519821004369/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2313/16384 : ℝ)) (989991958259/1000000000000 : ℝ) (989991958263/1000000000000 : ℝ) (519821004361/1000000000000 : ℝ) (519821004369/1000000000000 : ℝ) (824787431277/1000000000000 : ℝ) (412393715647/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0532_exp_lower
  have heNumeric : (16152288667/8000000000 : ℝ)/4 ≤ Real.exp (-170918537511/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (16152288667/8000000000 : ℝ)/4 ≤ Real.exp ((289/2048 : ℝ)-(412393715647/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (289/2048 : ℝ) (2313/16384 : ℝ) (412393715647/500000000000 : ℝ) (16152288667/8000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0533; no trusted numerical premise.
theorem cover7_leaf0533_exp_radius : (99748111787158263/100000000000000000 : ℝ) ≤ Real.exp ((-1157/57344 : ℝ)/8) ∧ Real.exp ((-1157/57344 : ℝ)/8) ≤ (997481117871582631/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1157/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0533_exp_lower : (459045351591431817/500000000000000000 : ℝ) ≤ Real.exp ((-2734690817039/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734690817039/4000000000000 : ℝ)/8) ≤ (183618140636572727/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734690817039/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0533_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504759750617/250000000000 : ℝ) ≤ 4*Real.exp (2313/16384 : ℝ)*Real.exp (-mu (radius 7 (1157/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (504759750617/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1157/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0533_exp_radius
  have hrNumeric : (980025704289/1000000000000 : ℝ) ≤ Real.exp (-1157/57344 : ℝ) ∧ Real.exp (-1157/57344 : ℝ) ≤ (98002570429/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980025704289/1000000000000 : ℝ) ≤ (radius 7 (1157/8192 : ℝ)) ∧ (radius 7 (1157/8192 : ℝ)) ≤ (98002570429/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1157/8192 : ℝ)) (980025704289/1000000000000 : ℝ) (98002570429/100000000000 : ℝ) (99435429967/500000000000 : ℝ) (198870859939/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1157/8192 : ℝ)) (980025704289/1000000000000 : ℝ) (98002570429/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1157/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980025704289/1000000000000 : ℝ) (98002570429/100000000000 : ℝ) (61875803259/62500000000 : ℝ) (198002570429/200000000000 : ℝ) (494981238101/500000000000 : ℝ) (247490619051/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1157/8192 : ℝ)) 1 (61875803259/62500000000 : ℝ) (198002570429/200000000000 : ℝ) (494981238101/500000000000 : ℝ) (247490619051/250000000000 : ℝ) (989987664173/1000000000000 : ℝ) (39599506567/40000000000 : ℝ) (247496915963/250000000000 : ℝ) (197997532771/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1157/8192 : ℝ)) 2 (989987664173/1000000000000 : ℝ) (39599506567/40000000000 : ℝ) (247496915963/250000000000 : ℝ) (197997532771/200000000000 : ℝ) (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ) (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1157/8192 : ℝ)) 3 (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ) (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ) (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ) (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1157/8192 : ℝ)) 4 (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ) (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ) (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ) (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1157/8192 : ℝ)) 5 (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ) (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ) (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ) (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1157/8192 : ℝ)) 6 (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ) (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ) (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ) (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1157/8192 : ℝ)) 7 (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ) (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ) (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ) (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1157/8192 : ℝ))) (99435429967/500000000000 : ℝ) (198870859939/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1157/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (99435429967/500000000000 : ℝ) (198870859939/1000000000000 : ℝ) (599435429967/1000000000000 : ℝ) (59943542997/100000000000 : ℝ) (445949391673/1000000000000 : ℝ) (1393591849/3125000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1157/8192 : ℝ))) 1 (599435429967/1000000000000 : ℝ) (59943542997/100000000000 : ℝ) (445949391673/1000000000000 : ℝ) (1393591849/3125000000 : ℝ) (26134620541/50000000000 : ℝ) (20907696433/40000000000 : ℝ) (129256978859/250000000000 : ℝ) (517027915443/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1157/8192 : ℝ))) 2 (26134620541/50000000000 : ℝ) (20907696433/40000000000 : ℝ) (129256978859/250000000000 : ℝ) (517027915443/1000000000000 : ℝ) (64982520391/125000000000 : ℝ) (259930081567/500000000000 : ℝ) (519852447893/1000000000000 : ℝ) (5198524479/10000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1157/8192 : ℝ))) 3 (64982520391/125000000000 : ℝ) (259930081567/500000000000 : ℝ) (519852447893/1000000000000 : ℝ) (5198524479/10000000000 : ℝ) (51985630551/100000000000 : ℝ) (519856305517/1000000000000 : ℝ) (64982038187/125000000000 : ℝ) (519856305503/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1157/8192 : ℝ))) 4 (51985630551/100000000000 : ℝ) (519856305517/1000000000000 : ℝ) (64982038187/125000000000 : ℝ) (519856305503/1000000000000 : ℝ) (519856305503/1000000000000 : ℝ) (51985630551/100000000000 : ℝ) (259928152751/500000000000 : ℝ) (51985630551/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1157/8192 : ℝ))) 5 (519856305503/1000000000000 : ℝ) (51985630551/100000000000 : ℝ) (259928152751/500000000000 : ℝ) (51985630551/100000000000 : ℝ) (259928152751/500000000000 : ℝ) (51985630551/100000000000 : ℝ) (259928152751/500000000000 : ℝ) (51985630551/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1157/8192 : ℝ))) 6 (259928152751/500000000000 : ℝ) (51985630551/100000000000 : ℝ) (259928152751/500000000000 : ℝ) (51985630551/100000000000 : ℝ) (259928152751/500000000000 : ℝ) (51985630551/100000000000 : ℝ) (259928152751/500000000000 : ℝ) (51985630551/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1157/8192 : ℝ))) 7 (259928152751/500000000000 : ℝ) (51985630551/100000000000 : ℝ) (259928152751/500000000000 : ℝ) (51985630551/100000000000 : ℝ) (259928152751/500000000000 : ℝ) (51985630551/100000000000 : ℝ) (259928152751/500000000000 : ℝ) (51985630551/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1157/8192 : ℝ)) hmem 8 (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ) (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1157/8192 : ℝ))) hcmem 8 (259928152751/500000000000 : ℝ) (51985630551/100000000000 : ℝ) (259928152751/500000000000 : ℝ) (51985630551/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1157/8192 : ℝ)) (247496916003/250000000000 : ℝ) (197997532803/200000000000 : ℝ) (259928152751/500000000000 : ℝ) (51985630551/100000000000 : ℝ) (16496940413/20000000000 : ℝ) (412423510333/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0533_exp_lower
  have heNumeric : (504759750617/250000000000 : ℝ)/4 ≤ Real.exp (-2734690817039/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504759750617/250000000000 : ℝ)/4 ≤ Real.exp ((2313/16384 : ℝ)-(412423510333/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2313/16384 : ℝ) (1157/8192 : ℝ) (412423510333/500000000000 : ℝ) (504759750617/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0534; no trusted numerical premise.
theorem cover7_leaf0534_exp_radius : (997480030704034273/1000000000000000000 : ℝ) ≤ Real.exp ((-2315/114688 : ℝ)/8) ∧ Real.exp ((-2315/114688 : ℝ)/8) ≤ (498740015352017137/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2315/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0534_exp_lower : (918090871069334589/1000000000000000000 : ℝ) ≤ Real.exp ((-1367342482683/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367342482683/2000000000000 : ℝ)/8) ≤ (91809087106933459/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367342482683/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0534_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019041956159/1000000000000 : ℝ) ≤ 4*Real.exp (1157/8192 : ℝ)*Real.exp (-mu (radius 7 (2315/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019041956159/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2315/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0534_exp_radius
  have hrNumeric : (49000857959/50000000000 : ℝ) ≤ Real.exp (-2315/114688 : ℝ) ∧ Real.exp (-2315/114688 : ℝ) ≤ (980017159181/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49000857959/50000000000 : ℝ) ≤ (radius 7 (2315/16384 : ℝ)) ∧ (radius 7 (2315/16384 : ℝ)) ≤ (980017159181/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2315/16384 : ℝ)) (49000857959/50000000000 : ℝ) (980017159181/1000000000000 : ℝ) (39782593033/200000000000 : ℝ) (198912965171/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2315/16384 : ℝ)) (49000857959/50000000000 : ℝ) (980017159181/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2315/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49000857959/50000000000 : ℝ) (980017159181/1000000000000 : ℝ) (99000857959/100000000000 : ℝ) (990008579591/1000000000000 : ℝ) (989958160317/1000000000000 : ℝ) (989958160319/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2315/16384 : ℝ)) 1 (99000857959/100000000000 : ℝ) (990008579591/1000000000000 : ℝ) (989958160317/1000000000000 : ℝ) (989958160319/1000000000000 : ℝ) (989983369953/1000000000000 : ℝ) (197996673991/200000000000 : ℝ) (30936980301/31250000000 : ℝ) (197996673927/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2315/16384 : ℝ)) 2 (989983369953/1000000000000 : ℝ) (197996673991/200000000000 : ℝ) (30936980301/31250000000 : ℝ) (197996673927/200000000000 : ℝ) (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ) (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2315/16384 : ℝ)) 3 (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ) (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ) (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ) (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2315/16384 : ℝ)) 4 (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ) (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ) (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ) (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2315/16384 : ℝ)) 5 (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ) (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ) (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ) (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2315/16384 : ℝ)) 6 (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ) (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ) (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ) (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2315/16384 : ℝ)) 7 (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ) (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ) (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ) (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2315/16384 : ℝ))) (39782593033/200000000000 : ℝ) (198912965171/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2315/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39782593033/200000000000 : ℝ) (198912965171/1000000000000 : ℝ) (299728241291/500000000000 : ℝ) (299728241293/500000000000 : ℝ) (89199319541/200000000000 : ℝ) (445996597713/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2315/16384 : ℝ))) 1 (299728241291/500000000000 : ℝ) (299728241293/500000000000 : ℝ) (89199319541/200000000000 : ℝ) (445996597713/1000000000000 : ℝ) (522726540143/1000000000000 : ℝ) (10454530803/20000000000 : ℝ) (517064359343/1000000000000 : ℝ) (517064359351/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2315/16384 : ℝ))) 2 (522726540143/1000000000000 : ℝ) (10454530803/20000000000 : ℝ) (517064359343/1000000000000 : ℝ) (517064359351/1000000000000 : ℝ) (519895449743/1000000000000 : ℝ) (519895449751/1000000000000 : ℝ) (103977548267/200000000000 : ℝ) (519887741343/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2315/16384 : ℝ))) 3 (519895449743/1000000000000 : ℝ) (519895449751/1000000000000 : ℝ) (103977548267/200000000000 : ℝ) (519887741343/1000000000000 : ℝ) (519891595539/1000000000000 : ℝ) (519891595547/1000000000000 : ℝ) (129972898881/250000000000 : ℝ) (519891595533/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2315/16384 : ℝ))) 4 (519891595539/1000000000000 : ℝ) (519891595547/1000000000000 : ℝ) (129972898881/250000000000 : ℝ) (519891595533/1000000000000 : ℝ) (519891595531/1000000000000 : ℝ) (25994579777/50000000000 : ℝ) (519891595531/1000000000000 : ℝ) (25994579777/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2315/16384 : ℝ))) 5 (519891595531/1000000000000 : ℝ) (25994579777/50000000000 : ℝ) (519891595531/1000000000000 : ℝ) (25994579777/50000000000 : ℝ) (519891595531/1000000000000 : ℝ) (25994579777/50000000000 : ℝ) (519891595531/1000000000000 : ℝ) (25994579777/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2315/16384 : ℝ))) 6 (519891595531/1000000000000 : ℝ) (25994579777/50000000000 : ℝ) (519891595531/1000000000000 : ℝ) (25994579777/50000000000 : ℝ) (519891595531/1000000000000 : ℝ) (25994579777/50000000000 : ℝ) (519891595531/1000000000000 : ℝ) (25994579777/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2315/16384 : ℝ))) 7 (519891595531/1000000000000 : ℝ) (25994579777/50000000000 : ℝ) (519891595531/1000000000000 : ℝ) (25994579777/50000000000 : ℝ) (519891595531/1000000000000 : ℝ) (25994579777/50000000000 : ℝ) (519891595531/1000000000000 : ℝ) (25994579777/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2315/16384 : ℝ)) hmem 8 (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ) (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2315/16384 : ℝ))) hcmem 8 (519891595531/1000000000000 : ℝ) (25994579777/50000000000 : ℝ) (519891595531/1000000000000 : ℝ) (25994579777/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2315/16384 : ℝ)) (15468490153/15625000000 : ℝ) (197996673959/200000000000 : ℝ) (519891595531/1000000000000 : ℝ) (25994579777/50000000000 : ℝ) (412453296443/500000000000 : ℝ) (103113324113/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0534_exp_lower
  have heNumeric : (2019041956159/1000000000000 : ℝ)/4 ≤ Real.exp (-1367342482683/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019041956159/1000000000000 : ℝ)/4 ≤ Real.exp ((1157/8192 : ℝ)-(103113324113/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1157/8192 : ℝ) (2315/16384 : ℝ) (103113324113/125000000000 : ℝ) (2019041956159/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0535; no trusted numerical premise.
theorem cover7_leaf0535_exp_radius : (498739471768835417/500000000000000000 : ℝ) ≤ Real.exp ((-579/28672 : ℝ)/8) ∧ Real.exp ((-579/28672 : ℝ)/8) ≤ (199495788707534167/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-579/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0535_exp_lower : (91809104092215773/100000000000000000 : ℝ) ≤ Real.exp ((-2734679045157/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734679045157/4000000000000 : ℝ)/8) ≤ (918091040922157731/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734679045157/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0535_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019044944449/1000000000000 : ℝ) ≤ 4*Real.exp (2315/16384 : ℝ)*Real.exp (-mu (radius 7 (579/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019044944449/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (579/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0535_exp_radius
  have hrNumeric : (490004307073/500000000000 : ℝ) ≤ Real.exp (-579/28672 : ℝ) ∧ Real.exp (-579/28672 : ℝ) ≤ (980008614147/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490004307073/500000000000 : ℝ) ≤ (radius 7 (579/4096 : ℝ)) ∧ (radius 7 (579/4096 : ℝ)) ≤ (980008614147/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (579/4096 : ℝ)) (490004307073/500000000000 : ℝ) (980008614147/1000000000000 : ℝ) (198955060749/1000000000000 : ℝ) (39791012151/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (579/4096 : ℝ)) (490004307073/500000000000 : ℝ) (980008614147/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (579/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490004307073/500000000000 : ℝ) (980008614147/1000000000000 : ℝ) (990004307073/1000000000000 : ℝ) (495002153537/500000000000 : ℝ) (247488461113/250000000000 : ℝ) (989953844453/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (579/4096 : ℝ)) 1 (990004307073/1000000000000 : ℝ) (495002153537/500000000000 : ℝ) (247488461113/250000000000 : ℝ) (989953844453/1000000000000 : ℝ) (494989537881/500000000000 : ℝ) (247494768941/250000000000 : ℝ) (12374738443/12500000000 : ℝ) (494989537721/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (579/4096 : ℝ)) 2 (494989537881/500000000000 : ℝ) (247494768941/250000000000 : ℝ) (12374738443/12500000000 : ℝ) (494989537721/500000000000 : ℝ) (989979075601/1000000000000 : ℝ) (989979075603/1000000000000 : ℝ) (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (579/4096 : ℝ)) 3 (989979075601/1000000000000 : ℝ) (989979075603/1000000000000 : ℝ) (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ) (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ) (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (579/4096 : ℝ)) 4 (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ) (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ) (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ) (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (579/4096 : ℝ)) 5 (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ) (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ) (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ) (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (579/4096 : ℝ)) 6 (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ) (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ) (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ) (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (579/4096 : ℝ)) 7 (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ) (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ) (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ) (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (579/4096 : ℝ))) (198955060749/1000000000000 : ℝ) (39791012151/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (579/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (198955060749/1000000000000 : ℝ) (39791012151/200000000000 : ℝ) (299738765187/500000000000 : ℝ) (299738765189/500000000000 : ℝ) (446043787927/1000000000000 : ℝ) (89208757587/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (579/4096 : ℝ))) 1 (299738765187/500000000000 : ℝ) (299738765189/500000000000 : ℝ) (446043787927/1000000000000 : ℝ) (89208757587/200000000000 : ℝ) (10455213183/20000000000 : ℝ) (522760659157/1000000000000 : ℝ) (1615939973/3125000000 : ℝ) (517100791367/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (579/4096 : ℝ))) 2 (10455213183/20000000000 : ℝ) (522760659157/1000000000000 : ℝ) (1615939973/3125000000 : ℝ) (517100791367/1000000000000 : ℝ) (103986145051/200000000000 : ℝ) (259965362631/500000000000 : ℝ) (259961511833/500000000000 : ℝ) (259961511837/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (579/4096 : ℝ))) 3 (103986145051/200000000000 : ℝ) (259965362631/500000000000 : ℝ) (259961511833/500000000000 : ℝ) (259961511837/500000000000 : ℝ) (25996343723/50000000000 : ℝ) (129981718617/250000000000 : ℝ) (259963437223/500000000000 : ℝ) (259963437227/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (579/4096 : ℝ))) 4 (25996343723/50000000000 : ℝ) (129981718617/250000000000 : ℝ) (259963437223/500000000000 : ℝ) (259963437227/500000000000 : ℝ) (519926874453/1000000000000 : ℝ) (519926874461/1000000000000 : ℝ) (129981718613/250000000000 : ℝ) (519926874461/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (579/4096 : ℝ))) 5 (519926874453/1000000000000 : ℝ) (519926874461/1000000000000 : ℝ) (129981718613/250000000000 : ℝ) (519926874461/1000000000000 : ℝ) (129981718613/250000000000 : ℝ) (519926874461/1000000000000 : ℝ) (129981718613/250000000000 : ℝ) (519926874461/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (579/4096 : ℝ))) 6 (129981718613/250000000000 : ℝ) (519926874461/1000000000000 : ℝ) (129981718613/250000000000 : ℝ) (519926874461/1000000000000 : ℝ) (129981718613/250000000000 : ℝ) (519926874461/1000000000000 : ℝ) (129981718613/250000000000 : ℝ) (519926874461/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (579/4096 : ℝ))) 7 (129981718613/250000000000 : ℝ) (519926874461/1000000000000 : ℝ) (129981718613/250000000000 : ℝ) (519926874461/1000000000000 : ℝ) (129981718613/250000000000 : ℝ) (519926874461/1000000000000 : ℝ) (129981718613/250000000000 : ℝ) (519926874461/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (579/4096 : ℝ)) hmem 8 (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ) (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (579/4096 : ℝ))) hcmem 8 (129981718613/250000000000 : ℝ) (519926874461/1000000000000 : ℝ) (129981718613/250000000000 : ℝ) (519926874461/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (579/4096 : ℝ)) (2474947689/2500000000 : ℝ) (989979075603/1000000000000 : ℝ) (129981718613/250000000000 : ℝ) (519926874461/1000000000000 : ℝ) (82496614799/100000000000 : ℝ) (103120768501/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0535_exp_lower
  have heNumeric : (2019044944449/1000000000000 : ℝ)/4 ≤ Real.exp (-2734679045157/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019044944449/1000000000000 : ℝ)/4 ≤ Real.exp ((2315/16384 : ℝ)-(103120768501/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2315/16384 : ℝ) (579/4096 : ℝ) (103120768501/125000000000 : ℝ) (2019044944449/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0536; no trusted numerical premise.
theorem cover7_leaf0536_exp_radius : (997477856372492311/1000000000000000000 : ℝ) ≤ Real.exp ((-331/16384 : ℝ)/8) ∧ Real.exp ((-331/16384 : ℝ)/8) ≤ (124684732046561539/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-331/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0536_exp_lower : (22952280318475973/25000000000000000 : ℝ) ≤ Real.exp ((-683668264123/1000000000000 : ℝ)/8) ∧ Real.exp ((-683668264123/1000000000000 : ℝ)/8) ≤ (918091212739038921/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683668264123/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0536_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019047967297/1000000000000 : ℝ) ≤ 4*Real.exp (579/4096 : ℝ)*Real.exp (-mu (radius 7 (2317/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019047967297/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2317/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0536_exp_radius
  have hrNumeric : (490000034593/500000000000 : ℝ) ≤ Real.exp (-331/16384 : ℝ) ∧ Real.exp (-331/16384 : ℝ) ≤ (980000069187/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490000034593/500000000000 : ℝ) ≤ (radius 7 (2317/16384 : ℝ)) ∧ (radius 7 (2317/16384 : ℝ)) ≤ (980000069187/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2317/16384 : ℝ)) (490000034593/500000000000 : ℝ) (980000069187/1000000000000 : ℝ) (24874643337/125000000000 : ℝ) (99498573351/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2317/16384 : ℝ)) (490000034593/500000000000 : ℝ) (980000069187/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2317/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490000034593/500000000000 : ℝ) (980000069187/1000000000000 : ℝ) (990000034593/1000000000000 : ℝ) (495000017297/500000000000 : ℝ) (197989905721/200000000000 : ℝ) (494974764303/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2317/16384 : ℝ)) 1 (990000034593/1000000000000 : ℝ) (495000017297/500000000000 : ℝ) (197989905721/200000000000 : ℝ) (494974764303/500000000000 : ℝ) (989974781599/1000000000000 : ℝ) (1237468477/1250000000 : ℝ) (247493695319/250000000000 : ℝ) (494987390639/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2317/16384 : ℝ)) 2 (989974781599/1000000000000 : ℝ) (1237468477/1250000000 : ℝ) (247493695319/250000000000 : ℝ) (494987390639/500000000000 : ℝ) (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ) (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2317/16384 : ℝ)) 3 (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ) (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ) (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ) (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2317/16384 : ℝ)) 4 (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ) (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ) (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ) (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2317/16384 : ℝ)) 5 (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ) (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ) (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ) (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2317/16384 : ℝ)) 6 (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ) (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ) (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ) (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2317/16384 : ℝ)) 7 (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ) (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ) (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ) (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2317/16384 : ℝ))) (24874643337/125000000000 : ℝ) (99498573351/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2317/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24874643337/125000000000 : ℝ) (99498573351/500000000000 : ℝ) (149874643337/250000000000 : ℝ) (599498573351/1000000000000 : ℝ) (111522740589/250000000000 : ℝ) (111522740591/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2317/16384 : ℝ))) 1 (149874643337/250000000000 : ℝ) (599498573351/1000000000000 : ℝ) (111522740589/250000000000 : ℝ) (111522740591/250000000000 : ℝ) (130698691963/250000000000 : ℝ) (261397383929/500000000000 : ℝ) (517137211497/1000000000000 : ℝ) (32321075719/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2317/16384 : ℝ))) 2 (130698691963/250000000000 : ℝ) (261397383929/500000000000 : ℝ) (517137211497/1000000000000 : ℝ) (32321075719/62500000000 : ℝ) (259982994837/500000000000 : ℝ) (519965989681/1000000000000 : ℝ) (519958294897/1000000000000 : ℝ) (64994786863/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2317/16384 : ℝ))) 3 (259982994837/500000000000 : ℝ) (519965989681/1000000000000 : ℝ) (519958294897/1000000000000 : ℝ) (64994786863/125000000000 : ℝ) (103992428457/200000000000 : ℝ) (519962142293/1000000000000 : ℝ) (519962142271/1000000000000 : ℝ) (519962142279/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2317/16384 : ℝ))) 4 (103992428457/200000000000 : ℝ) (519962142293/1000000000000 : ℝ) (519962142271/1000000000000 : ℝ) (519962142279/1000000000000 : ℝ) (259981071139/500000000000 : ℝ) (259981071143/500000000000 : ℝ) (519962142277/1000000000000 : ℝ) (259981071143/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2317/16384 : ℝ))) 5 (259981071139/500000000000 : ℝ) (259981071143/500000000000 : ℝ) (519962142277/1000000000000 : ℝ) (259981071143/500000000000 : ℝ) (519962142277/1000000000000 : ℝ) (259981071143/500000000000 : ℝ) (519962142277/1000000000000 : ℝ) (259981071143/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2317/16384 : ℝ))) 6 (519962142277/1000000000000 : ℝ) (259981071143/500000000000 : ℝ) (519962142277/1000000000000 : ℝ) (259981071143/500000000000 : ℝ) (519962142277/1000000000000 : ℝ) (259981071143/500000000000 : ℝ) (519962142277/1000000000000 : ℝ) (259981071143/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2317/16384 : ℝ))) 7 (519962142277/1000000000000 : ℝ) (259981071143/500000000000 : ℝ) (519962142277/1000000000000 : ℝ) (259981071143/500000000000 : ℝ) (519962142277/1000000000000 : ℝ) (259981071143/500000000000 : ℝ) (519962142277/1000000000000 : ℝ) (259981071143/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2317/16384 : ℝ)) hmem 8 (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ) (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2317/16384 : ℝ))) hcmem 8 (519962142277/1000000000000 : ℝ) (259981071143/500000000000 : ℝ) (519962142277/1000000000000 : ℝ) (259981071143/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2317/16384 : ℝ)) (989974781437/1000000000000 : ℝ) (989974781439/1000000000000 : ℝ) (519962142277/1000000000000 : ℝ) (259981071143/500000000000 : ℝ) (825025685981/1000000000000 : ℝ) (412512842999/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0536_exp_lower
  have heNumeric : (2019047967297/1000000000000 : ℝ)/4 ≤ Real.exp (-683668264123/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019047967297/1000000000000 : ℝ)/4 ≤ Real.exp ((579/4096 : ℝ)-(412512842999/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (579/4096 : ℝ) (2317/16384 : ℝ) (412512842999/500000000000 : ℝ) (2019047967297/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0537; no trusted numerical premise.
theorem cover7_leaf0537_exp_radius : (62342298075531169/62500000000000000 : ℝ) ≤ Real.exp ((-1159/57344 : ℝ)/8) ∧ Real.exp ((-1159/57344 : ℝ)/8) ≤ (199495353841699741/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1159/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0537_exp_lower : (459045693259415823/500000000000000000 : ℝ) ≤ Real.exp ((-2734666999411/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734666999411/4000000000000 : ℝ)/8) ≤ (918091386518831647/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734666999411/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0537_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504762756171/250000000000 : ℝ) ≤ 4*Real.exp (2317/16384 : ℝ)*Real.exp (-mu (radius 7 (1159/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (504762756171/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1159/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0537_exp_radius
  have hrNumeric : (979991524301/1000000000000 : ℝ) ≤ Real.exp (-1159/57344 : ℝ) ∧ Real.exp (-1159/57344 : ℝ) ≤ (489995762151/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979991524301/1000000000000 : ℝ) ≤ (radius 7 (1159/8192 : ℝ)) ∧ (radius 7 (1159/8192 : ℝ)) ≤ (489995762151/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1159/8192 : ℝ)) (979991524301/1000000000000 : ℝ) (489995762151/500000000000 : ℝ) (199039223009/1000000000000 : ℝ) (39807844603/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1159/8192 : ℝ)) (979991524301/1000000000000 : ℝ) (489995762151/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1159/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979991524301/1000000000000 : ℝ) (489995762151/500000000000 : ℝ) (19799915243/20000000000 : ℝ) (989995762151/1000000000000 : ℝ) (989945212777/1000000000000 : ℝ) (494972606389/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1159/8192 : ℝ)) 1 (19799915243/20000000000 : ℝ) (989995762151/1000000000000 : ℝ) (989945212777/1000000000000 : ℝ) (494972606389/500000000000 : ℝ) (989970487463/1000000000000 : ℝ) (197994097493/200000000000 : ℝ) (49498524357/50000000000 : ℝ) (494985243571/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1159/8192 : ℝ)) 2 (989970487463/1000000000000 : ℝ) (197994097493/200000000000 : ℝ) (49498524357/50000000000 : ℝ) (494985243571/500000000000 : ℝ) (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ) (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1159/8192 : ℝ)) 3 (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ) (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ) (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ) (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1159/8192 : ℝ)) 4 (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ) (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ) (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ) (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1159/8192 : ℝ)) 5 (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ) (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ) (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ) (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1159/8192 : ℝ)) 6 (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ) (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ) (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ) (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1159/8192 : ℝ)) 7 (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ) (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ) (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ) (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1159/8192 : ℝ))) (199039223009/1000000000000 : ℝ) (39807844603/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1159/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (199039223009/1000000000000 : ℝ) (39807844603/200000000000 : ℝ) (37469975719/62500000000 : ℝ) (149879902877/250000000000 : ℝ) (446138120999/1000000000000 : ℝ) (446138121007/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1159/8192 : ℝ))) 1 (37469975719/62500000000 : ℝ) (149879902877/250000000000 : ℝ) (446138120999/1000000000000 : ℝ) (446138121007/1000000000000 : ℝ) (522828866251/1000000000000 : ℝ) (261414433129/500000000000 : ℝ) (258586809881/500000000000 : ℝ) (51717361977/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1159/8192 : ℝ))) 2 (522828866251/1000000000000 : ℝ) (261414433129/500000000000 : ℝ) (258586809881/500000000000 : ℝ) (51717361977/100000000000 : ℝ) (260000621503/500000000000 : ℝ) (260000621507/500000000000 : ℝ) (64999194379/125000000000 : ℝ) (3249959719/6250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1159/8192 : ℝ))) 3 (260000621503/500000000000 : ℝ) (260000621507/500000000000 : ℝ) (64999194379/125000000000 : ℝ) (3249959719/6250000000 : ℝ) (519997399019/1000000000000 : ℝ) (519997399027/1000000000000 : ℝ) (129999349751/250000000000 : ℝ) (519997399013/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1159/8192 : ℝ))) 4 (519997399019/1000000000000 : ℝ) (519997399027/1000000000000 : ℝ) (129999349751/250000000000 : ℝ) (519997399013/1000000000000 : ℝ) (519997399011/1000000000000 : ℝ) (25999869951/50000000000 : ℝ) (519997399011/1000000000000 : ℝ) (25999869951/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1159/8192 : ℝ))) 5 (519997399011/1000000000000 : ℝ) (25999869951/50000000000 : ℝ) (519997399011/1000000000000 : ℝ) (25999869951/50000000000 : ℝ) (519997399011/1000000000000 : ℝ) (25999869951/50000000000 : ℝ) (519997399011/1000000000000 : ℝ) (25999869951/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1159/8192 : ℝ))) 6 (519997399011/1000000000000 : ℝ) (25999869951/50000000000 : ℝ) (519997399011/1000000000000 : ℝ) (25999869951/50000000000 : ℝ) (519997399011/1000000000000 : ℝ) (25999869951/50000000000 : ℝ) (519997399011/1000000000000 : ℝ) (25999869951/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1159/8192 : ℝ))) 7 (519997399011/1000000000000 : ℝ) (25999869951/50000000000 : ℝ) (519997399011/1000000000000 : ℝ) (25999869951/50000000000 : ℝ) (519997399011/1000000000000 : ℝ) (25999869951/50000000000 : ℝ) (519997399011/1000000000000 : ℝ) (25999869951/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1159/8192 : ℝ)) hmem 8 (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ) (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1159/8192 : ℝ))) hcmem 8 (519997399011/1000000000000 : ℝ) (25999869951/50000000000 : ℝ) (519997399011/1000000000000 : ℝ) (25999869951/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1159/8192 : ℝ)) (989970487301/1000000000000 : ℝ) (123746310913/125000000000 : ℝ) (519997399011/1000000000000 : ℝ) (25999869951/50000000000 : ℝ) (412542603433/500000000000 : ℝ) (206271301721/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0537_exp_lower
  have heNumeric : (504762756171/250000000000 : ℝ)/4 ≤ Real.exp (-2734666999411/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504762756171/250000000000 : ℝ)/4 ≤ Real.exp ((2317/16384 : ℝ)-(206271301721/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2317/16384 : ℝ) (1159/8192 : ℝ) (206271301721/250000000000 : ℝ) (504762756171/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0538; no trusted numerical premise.
theorem cover7_leaf0538_exp_radius : (249368920511422503/250000000000000000 : ℝ) ≤ Real.exp ((-2319/114688 : ℝ)/8) ∧ Real.exp ((-2319/114688 : ℝ)/8) ≤ (997475682045690013/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2319/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0538_exp_lower : (5738072264122413/6250000000000000 : ℝ) ≤ Real.exp ((-1367330436991/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367330436991/2000000000000 : ℝ)/8) ≤ (918091562259586081/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367330436991/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0538_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (80762164663/40000000000 : ℝ) ≤ 4*Real.exp (1159/8192 : ℝ)*Real.exp (-mu (radius 7 (2319/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (80762164663/40000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2319/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0538_exp_radius
  have hrNumeric : (97998297949/100000000000 : ℝ) ≤ Real.exp (-2319/114688 : ℝ) ∧ Real.exp (-2319/114688 : ℝ) ≤ (979982979491/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (97998297949/100000000000 : ℝ) ≤ (radius 7 (2319/16384 : ℝ)) ∧ (radius 7 (2319/16384 : ℝ)) ≤ (979982979491/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2319/16384 : ℝ)) (97998297949/100000000000 : ℝ) (979982979491/1000000000000 : ℝ) (99540644849/500000000000 : ℝ) (24885161213/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2319/16384 : ℝ)) (97998297949/100000000000 : ℝ) (979982979491/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2319/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (97998297949/100000000000 : ℝ) (979982979491/1000000000000 : ℝ) (197998297949/200000000000 : ℝ) (494995744873/500000000000 : ℝ) (123742612121/125000000000 : ℝ) (989940896969/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2319/16384 : ℝ)) 1 (197998297949/200000000000 : ℝ) (494995744873/500000000000 : ℝ) (123742612121/125000000000 : ℝ) (989940896969/1000000000000 : ℝ) (247491548339/250000000000 : ℝ) (494983096679/500000000000 : ℝ) (989966193033/1000000000000 : ℝ) (197993238607/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2319/16384 : ℝ)) 2 (247491548339/250000000000 : ℝ) (494983096679/500000000000 : ℝ) (989966193033/1000000000000 : ℝ) (197993238607/200000000000 : ℝ) (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ) (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2319/16384 : ℝ)) 3 (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ) (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ) (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ) (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2319/16384 : ℝ)) 4 (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ) (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ) (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ) (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2319/16384 : ℝ)) 5 (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ) (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ) (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ) (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2319/16384 : ℝ)) 6 (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ) (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ) (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ) (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2319/16384 : ℝ)) 7 (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ) (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ) (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ) (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2319/16384 : ℝ))) (99540644849/500000000000 : ℝ) (24885161213/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2319/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (99540644849/500000000000 : ℝ) (24885161213/125000000000 : ℝ) (599540644849/1000000000000 : ℝ) (149885161213/250000000000 : ℝ) (446185263873/1000000000000 : ℝ) (446185263881/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2319/16384 : ℝ))) 1 (599540644849/1000000000000 : ℝ) (149885161213/250000000000 : ℝ) (446185263873/1000000000000 : ℝ) (446185263881/1000000000000 : ℝ) (522862954361/1000000000000 : ℝ) (522862954367/1000000000000 : ℝ) (64651252021/125000000000 : ℝ) (258605008087/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2319/16384 : ℝ))) 2 (522862954361/1000000000000 : ℝ) (522862954367/1000000000000 : ℝ) (64651252021/125000000000 : ℝ) (258605008087/500000000000 : ℝ) (32502280329/62500000000 : ℝ) (520036485271/1000000000000 : ℝ) (104005760817/200000000000 : ℝ) (130007201023/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2319/16384 : ℝ))) 3 (32502280329/62500000000 : ℝ) (520036485271/1000000000000 : ℝ) (104005760817/200000000000 : ℝ) (130007201023/250000000000 : ℝ) (260016322337/500000000000 : ℝ) (260016322341/500000000000 : ℝ) (26001632233/50000000000 : ℝ) (130008161167/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2319/16384 : ℝ))) 4 (260016322337/500000000000 : ℝ) (260016322341/500000000000 : ℝ) (26001632233/50000000000 : ℝ) (130008161167/250000000000 : ℝ) (520032644667/1000000000000 : ℝ) (20801305787/40000000000 : ℝ) (260016322333/500000000000 : ℝ) (20801305787/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2319/16384 : ℝ))) 5 (520032644667/1000000000000 : ℝ) (20801305787/40000000000 : ℝ) (260016322333/500000000000 : ℝ) (20801305787/40000000000 : ℝ) (260016322333/500000000000 : ℝ) (20801305787/40000000000 : ℝ) (260016322333/500000000000 : ℝ) (20801305787/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2319/16384 : ℝ))) 6 (260016322333/500000000000 : ℝ) (20801305787/40000000000 : ℝ) (260016322333/500000000000 : ℝ) (20801305787/40000000000 : ℝ) (260016322333/500000000000 : ℝ) (20801305787/40000000000 : ℝ) (260016322333/500000000000 : ℝ) (20801305787/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2319/16384 : ℝ))) 7 (260016322333/500000000000 : ℝ) (20801305787/40000000000 : ℝ) (260016322333/500000000000 : ℝ) (20801305787/40000000000 : ℝ) (260016322333/500000000000 : ℝ) (20801305787/40000000000 : ℝ) (260016322333/500000000000 : ℝ) (20801305787/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2319/16384 : ℝ)) hmem 8 (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ) (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2319/16384 : ℝ))) hcmem 8 (260016322333/500000000000 : ℝ) (20801305787/40000000000 : ℝ) (260016322333/500000000000 : ℝ) (20801305787/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2319/16384 : ℝ)) (494983096597/500000000000 : ℝ) (989966193197/1000000000000 : ℝ) (260016322333/500000000000 : ℝ) (20801305787/40000000000 : ℝ) (412572355333/500000000000 : ℝ) (825144710683/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0538_exp_lower
  have heNumeric : (80762164663/40000000000 : ℝ)/4 ≤ Real.exp (-1367330436991/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (80762164663/40000000000 : ℝ)/4 ≤ Real.exp ((1159/8192 : ℝ)-(825144710683/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1159/8192 : ℝ) (2319/16384 : ℝ) (825144710683/1000000000000 : ℝ) (80762164663/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0539; no trusted numerical premise.
theorem cover7_leaf0539_exp_radius : (997474594884066231/1000000000000000000 : ℝ) ≤ Real.exp ((-145/7168 : ℝ)/8) ∧ Real.exp ((-145/7168 : ℝ)/8) ≤ (124684324360508279/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-145/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0539_exp_lower : (183618347992077051/200000000000000000 : ℝ) ≤ Real.exp ((-2734654680237/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734654680237/4000000000000 : ℝ)/8) ≤ (114761467495048157/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734654680237/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0539_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009528621477/500000000000 : ℝ) ≤ 4*Real.exp (2319/16384 : ℝ)*Real.exp (-mu (radius 7 (145/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (1009528621477/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (145/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0539_exp_radius
  have hrNumeric : (489987217377/500000000000 : ℝ) ≤ Real.exp (-145/7168 : ℝ) ∧ Real.exp (-145/7168 : ℝ) ≤ (195994886951/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (489987217377/500000000000 : ℝ) ≤ (radius 7 (145/1024 : ℝ)) ∧ (radius 7 (145/1024 : ℝ)) ≤ (195994886951/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (145/1024 : ℝ)) (489987217377/500000000000 : ℝ) (195994886951/200000000000 : ℝ) (49780836691/250000000000 : ℝ) (19912334677/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (145/1024 : ℝ)) (489987217377/500000000000 : ℝ) (195994886951/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (145/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (489987217377/500000000000 : ℝ) (195994886951/200000000000 : ℝ) (989987217377/1000000000000 : ℝ) (494993608689/500000000000 : ℝ) (989936581177/1000000000000 : ℝ) (989936581179/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (145/1024 : ℝ)) 1 (989987217377/1000000000000 : ℝ) (494993608689/500000000000 : ℝ) (989936581177/1000000000000 : ℝ) (989936581179/1000000000000 : ℝ) (989961899277/1000000000000 : ℝ) (989961899279/1000000000000 : ℝ) (989961898953/1000000000000 : ℝ) (197992379791/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (145/1024 : ℝ)) 2 (989961899277/1000000000000 : ℝ) (989961899279/1000000000000 : ℝ) (989961898953/1000000000000 : ℝ) (197992379791/200000000000 : ℝ) (197992379823/200000000000 : ℝ) (989961899117/1000000000000 : ℝ) (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (145/1024 : ℝ)) 3 (197992379823/200000000000 : ℝ) (989961899117/1000000000000 : ℝ) (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ) (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ) (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (145/1024 : ℝ)) 4 (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ) (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ) (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ) (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (145/1024 : ℝ)) 5 (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ) (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ) (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ) (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (145/1024 : ℝ)) 6 (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ) (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ) (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ) (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (145/1024 : ℝ)) 7 (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ) (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ) (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ) (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (145/1024 : ℝ))) (49780836691/250000000000 : ℝ) (19912334677/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (145/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (49780836691/250000000000 : ℝ) (19912334677/100000000000 : ℝ) (299780836691/500000000000 : ℝ) (119912334677/200000000000 : ℝ) (55779048873/125000000000 : ℝ) (27889524437/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (145/1024 : ℝ))) 1 (299780836691/500000000000 : ℝ) (119912334677/200000000000 : ℝ) (55779048873/125000000000 : ℝ) (27889524437/62500000000 : ℝ) (522897032183/1000000000000 : ℝ) (522897032189/1000000000000 : ℝ) (517246400717/1000000000000 : ℝ) (129311600181/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (145/1024 : ℝ))) 2 (522897032183/1000000000000 : ℝ) (522897032189/1000000000000 : ℝ) (517246400717/1000000000000 : ℝ) (129311600181/250000000000 : ℝ) (10401434329/20000000000 : ℝ) (520071716457/1000000000000 : ℝ) (260032021029/500000000000 : ℝ) (260032021033/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (145/1024 : ℝ))) 3 (10401434329/20000000000 : ℝ) (520071716457/1000000000000 : ℝ) (260032021029/500000000000 : ℝ) (260032021033/500000000000 : ℝ) (260033939627/500000000000 : ℝ) (260033939631/500000000000 : ℝ) (520067879239/1000000000000 : ℝ) (32504242453/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (145/1024 : ℝ))) 4 (260033939627/500000000000 : ℝ) (260033939631/500000000000 : ℝ) (520067879239/1000000000000 : ℝ) (32504242453/62500000000 : ℝ) (260033939623/500000000000 : ℝ) (104013575851/200000000000 : ℝ) (260033939623/500000000000 : ℝ) (104013575851/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (145/1024 : ℝ))) 5 (260033939623/500000000000 : ℝ) (104013575851/200000000000 : ℝ) (260033939623/500000000000 : ℝ) (104013575851/200000000000 : ℝ) (260033939623/500000000000 : ℝ) (104013575851/200000000000 : ℝ) (260033939623/500000000000 : ℝ) (104013575851/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (145/1024 : ℝ))) 6 (260033939623/500000000000 : ℝ) (104013575851/200000000000 : ℝ) (260033939623/500000000000 : ℝ) (104013575851/200000000000 : ℝ) (260033939623/500000000000 : ℝ) (104013575851/200000000000 : ℝ) (260033939623/500000000000 : ℝ) (104013575851/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (145/1024 : ℝ))) 7 (260033939623/500000000000 : ℝ) (104013575851/200000000000 : ℝ) (260033939623/500000000000 : ℝ) (104013575851/200000000000 : ℝ) (260033939623/500000000000 : ℝ) (104013575851/200000000000 : ℝ) (260033939623/500000000000 : ℝ) (104013575851/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (145/1024 : ℝ)) hmem 8 (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ) (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (145/1024 : ℝ))) hcmem 8 (260033939623/500000000000 : ℝ) (104013575851/200000000000 : ℝ) (260033939623/500000000000 : ℝ) (104013575851/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (145/1024 : ℝ)) (494980949557/500000000000 : ℝ) (989961899117/1000000000000 : ℝ) (260033939623/500000000000 : ℝ) (104013575851/200000000000 : ℝ) (412602098693/500000000000 : ℝ) (825204197403/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0539_exp_lower
  have heNumeric : (1009528621477/500000000000 : ℝ)/4 ≤ Real.exp (-2734654680237/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009528621477/500000000000 : ℝ)/4 ≤ Real.exp ((2319/16384 : ℝ)-(825204197403/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2319/16384 : ℝ) (145/1024 : ℝ) (825204197403/1000000000000 : ℝ) (1009528621477/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0540; no trusted numerical premise.
theorem cover7_leaf0540_exp_radius : (997473507723627363/1000000000000000000 : ℝ) ≤ Real.exp ((-2321/114688 : ℝ)/8) ∧ Real.exp ((-2321/114688 : ℝ)/8) ≤ (249368376930906841/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2321/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0540_exp_lower : (459045959809697063/500000000000000000 : ℝ) ≤ Real.exp ((-8545776307/12500000000 : ℝ)/8) ∧ Real.exp ((-8545776307/12500000000 : ℝ)/8) ≤ (918091919619394127/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8545776307/12500000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0540_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019060403789/1000000000000 : ℝ) ≤ 4*Real.exp (145/1024 : ℝ)*Real.exp (-mu (radius 7 (2321/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019060403789/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2321/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0540_exp_radius
  have hrNumeric : (244991472523/250000000000 : ℝ) ≤ Real.exp (-2321/114688 : ℝ) ∧ Real.exp (-2321/114688 : ℝ) ≤ (979965890093/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (244991472523/250000000000 : ℝ) ≤ (radius 7 (2321/16384 : ℝ)) ∧ (radius 7 (2321/16384 : ℝ)) ≤ (979965890093/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2321/16384 : ℝ)) (244991472523/250000000000 : ℝ) (979965890093/1000000000000 : ℝ) (99582697109/500000000000 : ℝ) (12447837139/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2321/16384 : ℝ)) (244991472523/250000000000 : ℝ) (979965890093/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2321/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (244991472523/250000000000 : ℝ) (979965890093/1000000000000 : ℝ) (494991472523/500000000000 : ℝ) (989982945047/1000000000000 : ℝ) (494966132703/500000000000 : ℝ) (989932265407/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2321/16384 : ℝ)) 1 (494991472523/500000000000 : ℝ) (989982945047/1000000000000 : ℝ) (494966132703/500000000000 : ℝ) (989932265407/1000000000000 : ℝ) (494978802613/500000000000 : ℝ) (989957605227/1000000000000 : ℝ) (989957604901/1000000000000 : ℝ) (989957604903/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2321/16384 : ℝ)) 2 (494978802613/500000000000 : ℝ) (989957605227/1000000000000 : ℝ) (989957604901/1000000000000 : ℝ) (989957604903/1000000000000 : ℝ) (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ) (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2321/16384 : ℝ)) 3 (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ) (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ) (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ) (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2321/16384 : ℝ)) 4 (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ) (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ) (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ) (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2321/16384 : ℝ)) 5 (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ) (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ) (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ) (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2321/16384 : ℝ)) 6 (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ) (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ) (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ) (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2321/16384 : ℝ)) 7 (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ) (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ) (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ) (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2321/16384 : ℝ))) (99582697109/500000000000 : ℝ) (12447837139/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2321/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (99582697109/500000000000 : ℝ) (12447837139/62500000000 : ℝ) (599582697109/1000000000000 : ℝ) (74947837139/125000000000 : ℝ) (8925590047/20000000000 : ℝ) (446279502357/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2321/16384 : ℝ))) 1 (599582697109/1000000000000 : ℝ) (74947837139/125000000000 : ℝ) (8925590047/20000000000 : ℝ) (446279502357/1000000000000 : ℝ) (522931099729/1000000000000 : ℝ) (104586219947/200000000000 : ℝ) (258641386713/500000000000 : ℝ) (64660346679/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2321/16384 : ℝ))) 2 (522931099729/1000000000000 : ℝ) (104586219947/200000000000 : ℝ) (258641386713/500000000000 : ℝ) (64660346679/125000000000 : ℝ) (520106936577/1000000000000 : ℝ) (65013367073/125000000000 : ℝ) (104019853793/200000000000 : ℝ) (130024817243/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2321/16384 : ℝ))) 3 (520106936577/1000000000000 : ℝ) (65013367073/125000000000 : ℝ) (104019853793/200000000000 : ℝ) (130024817243/250000000000 : ℝ) (520103102771/1000000000000 : ℝ) (260051551389/500000000000 : ℝ) (130025775689/250000000000 : ℝ) (130025775691/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2321/16384 : ℝ))) 4 (520103102771/1000000000000 : ℝ) (260051551389/500000000000 : ℝ) (130025775689/250000000000 : ℝ) (130025775691/250000000000 : ℝ) (520103102763/1000000000000 : ℝ) (520103102771/1000000000000 : ℝ) (520103102763/1000000000000 : ℝ) (520103102771/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2321/16384 : ℝ))) 5 (520103102763/1000000000000 : ℝ) (520103102771/1000000000000 : ℝ) (520103102763/1000000000000 : ℝ) (520103102771/1000000000000 : ℝ) (520103102763/1000000000000 : ℝ) (520103102771/1000000000000 : ℝ) (520103102763/1000000000000 : ℝ) (520103102771/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2321/16384 : ℝ))) 6 (520103102763/1000000000000 : ℝ) (520103102771/1000000000000 : ℝ) (520103102763/1000000000000 : ℝ) (520103102771/1000000000000 : ℝ) (520103102763/1000000000000 : ℝ) (520103102771/1000000000000 : ℝ) (520103102763/1000000000000 : ℝ) (520103102771/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2321/16384 : ℝ))) 7 (520103102763/1000000000000 : ℝ) (520103102771/1000000000000 : ℝ) (520103102763/1000000000000 : ℝ) (520103102771/1000000000000 : ℝ) (520103102763/1000000000000 : ℝ) (520103102771/1000000000000 : ℝ) (520103102763/1000000000000 : ℝ) (520103102771/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2321/16384 : ℝ)) hmem 8 (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ) (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2321/16384 : ℝ))) hcmem 8 (520103102763/1000000000000 : ℝ) (520103102771/1000000000000 : ℝ) (520103102763/1000000000000 : ℝ) (520103102771/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2321/16384 : ℝ)) (989957605063/1000000000000 : ℝ) (197991521013/200000000000 : ℝ) (520103102763/1000000000000 : ℝ) (520103102771/1000000000000 : ℝ) (206315916761/250000000000 : ℝ) (41263183353/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0540_exp_lower
  have heNumeric : (2019060403789/1000000000000 : ℝ)/4 ≤ Real.exp (-8545776307/12500000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019060403789/1000000000000 : ℝ)/4 ≤ Real.exp ((145/1024 : ℝ)-(41263183353/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (145/1024 : ℝ) (2321/16384 : ℝ) (41263183353/50000000000 : ℝ) (2019060403789/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0541; no trusted numerical premise.
theorem cover7_leaf0541_exp_radius : (249368105141093351/250000000000000000 : ℝ) ≤ Real.exp ((-1161/57344 : ℝ)/8) ∧ Real.exp ((-1161/57344 : ℝ)/8) ≤ (199494484112874681/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1161/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0541_exp_lower : (183618420247070293/200000000000000000 : ℝ) ≤ Real.exp ((-546928417607/800000000000 : ℝ)/8) ∧ Real.exp ((-546928417607/800000000000 : ℝ)/8) ≤ (459046050617675733/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-546928417607/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0541_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009531799529/500000000000 : ℝ) ≤ 4*Real.exp (2321/16384 : ℝ)*Real.exp (-mu (radius 7 (1161/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (1009531799529/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1161/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0541_exp_radius
  have hrNumeric : (195991469101/200000000000 : ℝ) ≤ Real.exp (-1161/57344 : ℝ) ∧ Real.exp (-1161/57344 : ℝ) ≤ (489978672753/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (195991469101/200000000000 : ℝ) ≤ (radius 7 (1161/8192 : ℝ)) ∧ (radius 7 (1161/8192 : ℝ)) ≤ (489978672753/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1161/8192 : ℝ)) (195991469101/200000000000 : ℝ) (489978672753/500000000000 : ℝ) (99603716031/500000000000 : ℝ) (49801858017/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1161/8192 : ℝ)) (195991469101/200000000000 : ℝ) (489978672753/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1161/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (195991469101/200000000000 : ℝ) (489978672753/500000000000 : ℝ) (61873667047/62500000000 : ℝ) (989978672753/1000000000000 : ℝ) (989927949653/1000000000000 : ℝ) (494963974827/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1161/8192 : ℝ)) 1 (61873667047/62500000000 : ℝ) (989978672753/1000000000000 : ℝ) (989927949653/1000000000000 : ℝ) (494963974827/500000000000 : ℝ) (494976655601/500000000000 : ℝ) (247488327801/250000000000 : ℝ) (989953310877/1000000000000 : ℝ) (989953310879/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1161/8192 : ℝ)) 2 (494976655601/500000000000 : ℝ) (247488327801/250000000000 : ℝ) (989953310877/1000000000000 : ℝ) (989953310879/1000000000000 : ℝ) (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ) (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1161/8192 : ℝ)) 3 (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ) (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ) (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ) (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1161/8192 : ℝ)) 4 (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ) (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ) (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ) (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1161/8192 : ℝ)) 5 (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ) (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ) (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ) (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1161/8192 : ℝ)) 6 (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ) (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ) (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ) (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1161/8192 : ℝ)) 7 (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ) (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ) (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ) (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1161/8192 : ℝ))) (99603716031/500000000000 : ℝ) (49801858017/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1161/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (99603716031/500000000000 : ℝ) (49801858017/250000000000 : ℝ) (599603716031/1000000000000 : ℝ) (299801858017/500000000000 : ℝ) (446326597977/1000000000000 : ℝ) (89265319597/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1161/8192 : ℝ))) 1 (599603716031/1000000000000 : ℝ) (299801858017/500000000000 : ℝ) (446326597977/1000000000000 : ℝ) (89265319597/200000000000 : ℝ) (130741289251/250000000000 : ℝ) (52296515701/100000000000 : ℝ) (517319134297/1000000000000 : ℝ) (16166222947/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1161/8192 : ℝ))) 2 (130741289251/250000000000 : ℝ) (52296515701/100000000000 : ℝ) (517319134297/1000000000000 : ℝ) (16166222947/31250000000 : ℝ) (10402842913/20000000000 : ℝ) (520142145657/1000000000000 : ℝ) (52013448481/100000000000 : ℝ) (520134484817/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1161/8192 : ℝ))) 3 (10402842913/20000000000 : ℝ) (520142145657/1000000000000 : ℝ) (52013448481/100000000000 : ℝ) (520134484817/1000000000000 : ℝ) (52013831523/100000000000 : ℝ) (520138315237/1000000000000 : ℝ) (104027663043/200000000000 : ℝ) (520138315223/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1161/8192 : ℝ))) 4 (52013831523/100000000000 : ℝ) (520138315237/1000000000000 : ℝ) (104027663043/200000000000 : ℝ) (520138315223/1000000000000 : ℝ) (260069157611/500000000000 : ℝ) (52013831523/100000000000 : ℝ) (260069157611/500000000000 : ℝ) (52013831523/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1161/8192 : ℝ))) 5 (260069157611/500000000000 : ℝ) (52013831523/100000000000 : ℝ) (260069157611/500000000000 : ℝ) (52013831523/100000000000 : ℝ) (260069157611/500000000000 : ℝ) (52013831523/100000000000 : ℝ) (260069157611/500000000000 : ℝ) (52013831523/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1161/8192 : ℝ))) 6 (260069157611/500000000000 : ℝ) (52013831523/100000000000 : ℝ) (260069157611/500000000000 : ℝ) (52013831523/100000000000 : ℝ) (260069157611/500000000000 : ℝ) (52013831523/100000000000 : ℝ) (260069157611/500000000000 : ℝ) (52013831523/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1161/8192 : ℝ))) 7 (260069157611/500000000000 : ℝ) (52013831523/100000000000 : ℝ) (260069157611/500000000000 : ℝ) (52013831523/100000000000 : ℝ) (260069157611/500000000000 : ℝ) (52013831523/100000000000 : ℝ) (260069157611/500000000000 : ℝ) (52013831523/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1161/8192 : ℝ)) hmem 8 (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ) (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1161/8192 : ℝ))) hcmem 8 (260069157611/500000000000 : ℝ) (52013831523/100000000000 : ℝ) (260069157611/500000000000 : ℝ) (52013831523/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1161/8192 : ℝ)) (989953311039/1000000000000 : ℝ) (494976655521/500000000000 : ℝ) (260069157611/500000000000 : ℝ) (52013831523/100000000000 : ℝ) (25791347489/31250000000 : ℝ) (165064623933/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0541_exp_lower
  have heNumeric : (1009531799529/500000000000 : ℝ)/4 ≤ Real.exp (-546928417607/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009531799529/500000000000 : ℝ)/4 ≤ Real.exp ((2321/16384 : ℝ)-(165064623933/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2321/16384 : ℝ) (1161/8192 : ℝ) (165064623933/200000000000 : ℝ) (1009531799529/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0542; no trusted numerical premise.
theorem cover7_leaf0542_exp_radius : (199494266681260871/200000000000000000 : ℝ) ≤ Real.exp ((-2323/114688 : ℝ)/8) ∧ Real.exp ((-2323/114688 : ℝ)/8) ≤ (249367833351576089/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2323/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0542_exp_lower : (918092284807340343/1000000000000000000 : ℝ) ≤ Real.exp ((-1367317844827/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367317844827/2000000000000 : ℝ)/8) ≤ (114761535600917543/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367317844827/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0542_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403813365749/200000000000 : ℝ) ≤ 4*Real.exp (1161/8192 : ℝ)*Real.exp (-mu (radius 7 (2323/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (403813365749/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2323/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0542_exp_radius
  have hrNumeric : (979948800993/1000000000000 : ℝ) ≤ Real.exp (-2323/114688 : ℝ) ∧ Real.exp (-2323/114688 : ℝ) ≤ (489974400497/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979948800993/1000000000000 : ℝ) ≤ (radius 7 (2323/16384 : ℝ)) ∧ (radius 7 (2323/16384 : ℝ)) ≤ (489974400497/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2323/16384 : ℝ)) (979948800993/1000000000000 : ℝ) (489974400497/500000000000 : ℝ) (199249460301/1000000000000 : ℝ) (199249460307/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2323/16384 : ℝ)) (979948800993/1000000000000 : ℝ) (489974400497/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2323/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979948800993/1000000000000 : ℝ) (489974400497/500000000000 : ℝ) (61873400031/62500000000 : ℝ) (989974400497/1000000000000 : ℝ) (989923633919/1000000000000 : ℝ) (989923633921/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2323/16384 : ℝ)) 1 (61873400031/62500000000 : ℝ) (989974400497/1000000000000 : ℝ) (989923633919/1000000000000 : ℝ) (989923633921/1000000000000 : ℝ) (989949017207/1000000000000 : ℝ) (989949017209/1000000000000 : ℝ) (494974508441/500000000000 : ℝ) (247487254221/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2323/16384 : ℝ)) 2 (989949017207/1000000000000 : ℝ) (989949017209/1000000000000 : ℝ) (494974508441/500000000000 : ℝ) (247487254221/250000000000 : ℝ) (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ) (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2323/16384 : ℝ)) 3 (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ) (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ) (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ) (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2323/16384 : ℝ)) 4 (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ) (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ) (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ) (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2323/16384 : ℝ)) 5 (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ) (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ) (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ) (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2323/16384 : ℝ)) 6 (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ) (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ) (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ) (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2323/16384 : ℝ)) 7 (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ) (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ) (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ) (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2323/16384 : ℝ))) (199249460301/1000000000000 : ℝ) (199249460307/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2323/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (199249460301/1000000000000 : ℝ) (199249460307/1000000000000 : ℝ) (11992494603/20000000000 : ℝ) (299812365077/500000000000 : ℝ) (111593419469/250000000000 : ℝ) (111593419471/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2323/16384 : ℝ))) 1 (11992494603/20000000000 : ℝ) (299812365077/500000000000 : ℝ) (111593419469/250000000000 : ℝ) (111593419471/250000000000 : ℝ) (522999204013/1000000000000 : ℝ) (522999204019/1000000000000 : ℝ) (25867774167/50000000000 : ℝ) (517355483347/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2323/16384 : ℝ))) 2 (522999204013/1000000000000 : ℝ) (522999204019/1000000000000 : ℝ) (25867774167/50000000000 : ℝ) (517355483347/1000000000000 : ℝ) (130044335919/250000000000 : ℝ) (520177343683/1000000000000 : ℝ) (40638257/78125000 : ℝ) (520169689607/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2323/16384 : ℝ))) 3 (130044335919/250000000000 : ℝ) (520177343683/1000000000000 : ℝ) (40638257/78125000 : ℝ) (520169689607/1000000000000 : ℝ) (260086758319/500000000000 : ℝ) (104034703329/200000000000 : ℝ) (520173516623/1000000000000 : ℝ) (520173516631/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2323/16384 : ℝ))) 4 (260086758319/500000000000 : ℝ) (104034703329/200000000000 : ℝ) (520173516623/1000000000000 : ℝ) (520173516631/1000000000000 : ℝ) (52017351663/100000000000 : ℝ) (260086758319/500000000000 : ℝ) (52017351663/100000000000 : ℝ) (260086758319/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2323/16384 : ℝ))) 5 (52017351663/100000000000 : ℝ) (260086758319/500000000000 : ℝ) (52017351663/100000000000 : ℝ) (260086758319/500000000000 : ℝ) (52017351663/100000000000 : ℝ) (260086758319/500000000000 : ℝ) (52017351663/100000000000 : ℝ) (260086758319/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2323/16384 : ℝ))) 6 (52017351663/100000000000 : ℝ) (260086758319/500000000000 : ℝ) (52017351663/100000000000 : ℝ) (260086758319/500000000000 : ℝ) (52017351663/100000000000 : ℝ) (260086758319/500000000000 : ℝ) (52017351663/100000000000 : ℝ) (260086758319/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2323/16384 : ℝ))) 7 (52017351663/100000000000 : ℝ) (260086758319/500000000000 : ℝ) (52017351663/100000000000 : ℝ) (260086758319/500000000000 : ℝ) (52017351663/100000000000 : ℝ) (260086758319/500000000000 : ℝ) (52017351663/100000000000 : ℝ) (260086758319/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2323/16384 : ℝ)) hmem 8 (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ) (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2323/16384 : ℝ))) hcmem 8 (52017351663/100000000000 : ℝ) (260086758319/500000000000 : ℝ) (52017351663/100000000000 : ℝ) (260086758319/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2323/16384 : ℝ)) (247487254261/250000000000 : ℝ) (989949017047/1000000000000 : ℝ) (52017351663/100000000000 : ℝ) (260086758319/500000000000 : ℝ) (82538255521/100000000000 : ℝ) (412691277613/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0542_exp_lower
  have heNumeric : (403813365749/200000000000 : ℝ)/4 ≤ Real.exp (-1367317844827/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403813365749/200000000000 : ℝ)/4 ≤ Real.exp ((1161/8192 : ℝ)-(412691277613/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1161/8192 : ℝ) (2323/16384 : ℝ) (412691277613/500000000000 : ℝ) (403813365749/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0543; no trusted numerical premise.
theorem cover7_leaf0543_exp_radius : (997470246249420213/1000000000000000000 : ℝ) ≤ Real.exp ((-83/4096 : ℝ)/8) ∧ Real.exp ((-83/4096 : ℝ)/8) ≤ (498735123124710107/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-83/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0543_exp_lower : (918092470331804323/1000000000000000000 : ℝ) ≤ Real.exp ((-2734629223221/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734629223221/4000000000000 : ℝ)/8) ≤ (229523117582951081/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734629223221/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0543_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504767523197/250000000000 : ℝ) ≤ 4*Real.exp (2323/16384 : ℝ)*Real.exp (-mu (radius 7 (581/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (504767523197/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (581/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0543_exp_radius
  have hrNumeric : (489970128277/500000000000 : ℝ) ≤ Real.exp (-83/4096 : ℝ) ∧ Real.exp (-83/4096 : ℝ) ≤ (195988051311/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (489970128277/500000000000 : ℝ) ≤ (radius 7 (581/4096 : ℝ)) ∧ (radius 7 (581/4096 : ℝ)) ≤ (195988051311/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (581/4096 : ℝ)) (489970128277/500000000000 : ℝ) (195988051311/200000000000 : ℝ) (24911434869/125000000000 : ℝ) (99645739479/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (581/4096 : ℝ)) (489970128277/500000000000 : ℝ) (195988051311/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (581/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (489970128277/500000000000 : ℝ) (195988051311/200000000000 : ℝ) (989970128277/1000000000000 : ℝ) (494985064139/500000000000 : ℝ) (247479829551/250000000000 : ℝ) (197983863641/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (581/4096 : ℝ)) 1 (989970128277/1000000000000 : ℝ) (494985064139/500000000000 : ℝ) (247479829551/250000000000 : ℝ) (197983863641/200000000000 : ℝ) (24748618081/25000000000 : ℝ) (494972361621/500000000000 : ℝ) (494972361457/500000000000 : ℝ) (247486180729/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (581/4096 : ℝ)) 2 (24748618081/25000000000 : ℝ) (494972361621/500000000000 : ℝ) (494972361457/500000000000 : ℝ) (247486180729/250000000000 : ℝ) (989944723077/1000000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (581/4096 : ℝ)) 3 (989944723077/1000000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (581/4096 : ℝ)) 4 (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (581/4096 : ℝ)) 5 (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (581/4096 : ℝ)) 6 (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (581/4096 : ℝ)) 7 (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (581/4096 : ℝ))) (24911434869/125000000000 : ℝ) (99645739479/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (581/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24911434869/125000000000 : ℝ) (99645739479/500000000000 : ℝ) (149911434869/250000000000 : ℝ) (599645739479/1000000000000 : ℝ) (446420742071/1000000000000 : ℝ) (446420742079/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (581/4096 : ℝ))) 1 (149911434869/250000000000 : ℝ) (599645739479/1000000000000 : ℝ) (446420742071/1000000000000 : ℝ) (446420742079/1000000000000 : ℝ) (523033240773/1000000000000 : ℝ) (523033240779/1000000000000 : ℝ) (517391820573/1000000000000 : ℝ) (25869591029/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (581/4096 : ℝ))) 2 (523033240773/1000000000000 : ℝ) (523033240779/1000000000000 : ℝ) (517391820573/1000000000000 : ℝ) (25869591029/50000000000 : ℝ) (520212530673/1000000000000 : ℝ) (13005313267/25000000000 : ℝ) (65025610419/125000000000 : ℝ) (520204883359/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (581/4096 : ℝ))) 3 (520212530673/1000000000000 : ℝ) (13005313267/25000000000 : ℝ) (65025610419/125000000000 : ℝ) (520204883359/1000000000000 : ℝ) (130052176753/250000000000 : ℝ) (26010435351/50000000000 : ℝ) (260104353499/500000000000 : ℝ) (260104353503/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (581/4096 : ℝ))) 4 (130052176753/250000000000 : ℝ) (26010435351/50000000000 : ℝ) (260104353499/500000000000 : ℝ) (260104353503/500000000000 : ℝ) (104041741401/200000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (581/4096 : ℝ))) 5 (104041741401/200000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (581/4096 : ℝ))) 6 (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (581/4096 : ℝ))) 7 (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (581/4096 : ℝ)) hmem 8 (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (581/4096 : ℝ))) hcmem 8 (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (581/4096 : ℝ)) (247486180769/250000000000 : ℝ) (989944723079/1000000000000 : ℝ) (130052176751/250000000000 : ℝ) (520208707013/1000000000000 : ℝ) (206360493439/250000000000 : ℝ) (412720986887/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0543_exp_lower
  have heNumeric : (504767523197/250000000000 : ℝ)/4 ≤ Real.exp (-2734629223221/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504767523197/250000000000 : ℝ)/4 ≤ Real.exp ((2323/16384 : ℝ)-(412720986887/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2323/16384 : ℝ) (581/4096 : ℝ) (412720986887/500000000000 : ℝ) (504767523197/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0544; no trusted numerical premise.
theorem cover7_leaf0544_exp_radius : (997469159093720977/1000000000000000000 : ℝ) ≤ Real.exp ((-2325/114688 : ℝ)/8) ∧ Real.exp ((-2325/114688 : ℝ)/8) ≤ (498734579546860489/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2325/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0544_exp_lower : (896574861142697/976562500000000 : ℝ) ≤ Real.exp ((-170913918043/250000000000 : ℝ)/8) ∧ Real.exp ((-170913918043/250000000000 : ℝ)/8) ≤ (918092657810121729/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-170913918043/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0544_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201907339121/100000000000 : ℝ) ≤ 4*Real.exp (581/4096 : ℝ)*Real.exp (-mu (radius 7 (2325/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (201907339121/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2325/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0544_exp_radius
  have hrNumeric : (979931712191/1000000000000 : ℝ) ≤ Real.exp (-2325/114688 : ℝ) ∧ Real.exp (-2325/114688 : ℝ) ≤ (15311433003/15625000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979931712191/1000000000000 : ℝ) ≤ (radius 7 (2325/16384 : ℝ)) ∧ (radius 7 (2325/16384 : ℝ)) ≤ (15311433003/15625000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2325/16384 : ℝ)) (979931712191/1000000000000 : ℝ) (15311433003/15625000000 : ℝ) (39866697601/200000000000 : ℝ) (199333488011/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2325/16384 : ℝ)) (979931712191/1000000000000 : ℝ) (15311433003/15625000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2325/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979931712191/1000000000000 : ℝ) (15311433003/15625000000 : ℝ) (197993171219/200000000000 : ℝ) (30936433003/31250000000 : ℝ) (247478750627/250000000000 : ℝ) (989915002509/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2325/16384 : ℝ)) 1 (197993171219/200000000000 : ℝ) (30936433003/31250000000 : ℝ) (247478750627/250000000000 : ℝ) (989915002509/1000000000000 : ℝ) (989940429301/1000000000000 : ℝ) (989940429303/1000000000000 : ℝ) (494970214487/500000000000 : ℝ) (61871276811/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2325/16384 : ℝ)) 2 (989940429301/1000000000000 : ℝ) (989940429303/1000000000000 : ℝ) (494970214487/500000000000 : ℝ) (61871276811/62500000000 : ℝ) (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ) (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2325/16384 : ℝ)) 3 (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ) (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ) (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ) (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2325/16384 : ℝ)) 4 (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ) (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ) (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ) (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2325/16384 : ℝ)) 5 (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ) (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ) (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ) (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2325/16384 : ℝ)) 6 (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ) (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ) (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ) (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2325/16384 : ℝ)) 7 (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ) (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ) (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ) (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2325/16384 : ℝ))) (39866697601/200000000000 : ℝ) (199333488011/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2325/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39866697601/200000000000 : ℝ) (199333488011/1000000000000 : ℝ) (299833372001/500000000000 : ℝ) (299833372003/500000000000 : ℝ) (446467790557/1000000000000 : ℝ) (111616947641/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2325/16384 : ℝ))) 1 (299833372001/500000000000 : ℝ) (299833372003/500000000000 : ℝ) (446467790557/1000000000000 : ℝ) (111616947641/250000000000 : ℝ) (523067267279/1000000000000 : ℝ) (104613453457/200000000000 : ℝ) (64678518249/125000000000 : ℝ) (517428145999/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2325/16384 : ℝ))) 2 (523067267279/1000000000000 : ℝ) (104613453457/200000000000 : ℝ) (64678518249/125000000000 : ℝ) (517428145999/1000000000000 : ℝ) (104049541327/200000000000 : ℝ) (260123853321/500000000000 : ℝ) (520240066063/1000000000000 : ℝ) (52024006607/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2325/16384 : ℝ))) 3 (104049541327/200000000000 : ℝ) (260123853321/500000000000 : ℝ) (520240066063/1000000000000 : ℝ) (52024006607/100000000000 : ℝ) (520243886349/1000000000000 : ℝ) (130060971589/250000000000 : ℝ) (260121943167/500000000000 : ℝ) (260121943171/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2325/16384 : ℝ))) 4 (520243886349/1000000000000 : ℝ) (130060971589/250000000000 : ℝ) (260121943167/500000000000 : ℝ) (260121943171/500000000000 : ℝ) (520243886341/1000000000000 : ℝ) (520243886349/1000000000000 : ℝ) (520243886341/1000000000000 : ℝ) (520243886349/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2325/16384 : ℝ))) 5 (520243886341/1000000000000 : ℝ) (520243886349/1000000000000 : ℝ) (520243886341/1000000000000 : ℝ) (520243886349/1000000000000 : ℝ) (520243886341/1000000000000 : ℝ) (520243886349/1000000000000 : ℝ) (520243886341/1000000000000 : ℝ) (520243886349/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2325/16384 : ℝ))) 6 (520243886341/1000000000000 : ℝ) (520243886349/1000000000000 : ℝ) (520243886341/1000000000000 : ℝ) (520243886349/1000000000000 : ℝ) (520243886341/1000000000000 : ℝ) (520243886349/1000000000000 : ℝ) (520243886341/1000000000000 : ℝ) (520243886349/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2325/16384 : ℝ))) 7 (520243886341/1000000000000 : ℝ) (520243886349/1000000000000 : ℝ) (520243886341/1000000000000 : ℝ) (520243886349/1000000000000 : ℝ) (520243886341/1000000000000 : ℝ) (520243886349/1000000000000 : ℝ) (520243886341/1000000000000 : ℝ) (520243886349/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2325/16384 : ℝ)) hmem 8 (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ) (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2325/16384 : ℝ))) hcmem 8 (520243886341/1000000000000 : ℝ) (520243886349/1000000000000 : ℝ) (520243886341/1000000000000 : ℝ) (520243886349/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2325/16384 : ℝ)) (989940429137/1000000000000 : ℝ) (49497021457/50000000000 : ℝ) (520243886341/1000000000000 : ℝ) (520243886349/1000000000000 : ℝ) (825501375281/1000000000000 : ℝ) (825501375297/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0544_exp_lower
  have heNumeric : (201907339121/100000000000 : ℝ)/4 ≤ Real.exp (-170913918043/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201907339121/100000000000 : ℝ)/4 ≤ Real.exp ((581/4096 : ℝ)-(825501375297/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (581/4096 : ℝ) (2325/16384 : ℝ) (825501375297/1000000000000 : ℝ) (201907339121/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0545; no trusted numerical premise.
theorem cover7_leaf0545_exp_radius : (997468071939206647/1000000000000000000 : ℝ) ≤ Real.exp ((-1163/57344 : ℝ)/8) ∧ Real.exp ((-1163/57344 : ℝ)/8) ≤ (124683508992400831/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1163/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0545_exp_lower : (918092847238047577/1000000000000000000 : ℝ) ≤ Real.exp ((-2734616086203/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734616086203/4000000000000 : ℝ)/8) ≤ (459046423619023789/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734616086203/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0545_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019076723939/1000000000000 : ℝ) ≤ 4*Real.exp (2325/16384 : ℝ)*Real.exp (-mu (radius 7 (1163/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019076723939/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1163/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0545_exp_radius
  have hrNumeric : (979923167901/1000000000000 : ℝ) ≤ Real.exp (-1163/57344 : ℝ) ∧ Real.exp (-1163/57344 : ℝ) ≤ (489961583951/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979923167901/1000000000000 : ℝ) ≤ (radius 7 (1163/8192 : ℝ)) ∧ (radius 7 (1163/8192 : ℝ)) ≤ (489961583951/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1163/8192 : ℝ)) (979923167901/1000000000000 : ℝ) (489961583951/500000000000 : ℝ) (99687743741/500000000000 : ℝ) (389405249/1953125000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1163/8192 : ℝ)) (979923167901/1000000000000 : ℝ) (489961583951/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1163/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979923167901/1000000000000 : ℝ) (489961583951/500000000000 : ℝ) (19799231679/20000000000 : ℝ) (989961583951/1000000000000 : ℝ) (98991068683/100000000000 : ℝ) (989910686831/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1163/8192 : ℝ)) 1 (19799231679/20000000000 : ℝ) (989961583951/1000000000000 : ℝ) (98991068683/100000000000 : ℝ) (989910686831/1000000000000 : ℝ) (98993613539/100000000000 : ℝ) (989936135391/1000000000000 : ℝ) (494968067531/500000000000 : ℝ) (123742016883/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1163/8192 : ℝ)) 2 (98993613539/100000000000 : ℝ) (989936135391/1000000000000 : ℝ) (494968067531/500000000000 : ℝ) (123742016883/125000000000 : ℝ) (494968067613/500000000000 : ℝ) (247484033807/250000000000 : ℝ) (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1163/8192 : ℝ)) 3 (494968067613/500000000000 : ℝ) (247484033807/250000000000 : ℝ) (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ) (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ) (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1163/8192 : ℝ)) 4 (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ) (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ) (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ) (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1163/8192 : ℝ)) 5 (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ) (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ) (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ) (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1163/8192 : ℝ)) 6 (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ) (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ) (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ) (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1163/8192 : ℝ)) 7 (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ) (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ) (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ) (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1163/8192 : ℝ))) (99687743741/500000000000 : ℝ) (389405249/1953125000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1163/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (99687743741/500000000000 : ℝ) (389405249/1953125000 : ℝ) (599687743741/1000000000000 : ℝ) (2342530249/3906250000 : ℝ) (223257411681/500000000000 : ℝ) (446514823369/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1163/8192 : ℝ))) 1 (599687743741/1000000000000 : ℝ) (2342530249/3906250000 : ℝ) (223257411681/500000000000 : ℝ) (446514823369/1000000000000 : ℝ) (523101283551/1000000000000 : ℝ) (523101283557/1000000000000 : ℝ) (517464459619/1000000000000 : ℝ) (4139715677/8000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1163/8192 : ℝ))) 2 (523101283551/1000000000000 : ℝ) (523101283557/1000000000000 : ℝ) (517464459619/1000000000000 : ℝ) (4139715677/8000000000 : ℝ) (104056574317/200000000000 : ℝ) (520282871591/1000000000000 : ℝ) (65034404719/125000000000 : ℝ) (520275237759/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1163/8192 : ℝ))) 3 (104056574317/200000000000 : ℝ) (520282871591/1000000000000 : ℝ) (65034404719/125000000000 : ℝ) (520275237759/1000000000000 : ℝ) (130069763667/250000000000 : ℝ) (20811162187/40000000000 : ℝ) (260139527327/500000000000 : ℝ) (520279054661/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1163/8192 : ℝ))) 4 (130069763667/250000000000 : ℝ) (20811162187/40000000000 : ℝ) (260139527327/500000000000 : ℝ) (520279054661/1000000000000 : ℝ) (520279054661/1000000000000 : ℝ) (130069763667/250000000000 : ℝ) (26013952733/50000000000 : ℝ) (130069763667/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1163/8192 : ℝ))) 5 (520279054661/1000000000000 : ℝ) (130069763667/250000000000 : ℝ) (26013952733/50000000000 : ℝ) (130069763667/250000000000 : ℝ) (26013952733/50000000000 : ℝ) (130069763667/250000000000 : ℝ) (26013952733/50000000000 : ℝ) (130069763667/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1163/8192 : ℝ))) 6 (26013952733/50000000000 : ℝ) (130069763667/250000000000 : ℝ) (26013952733/50000000000 : ℝ) (130069763667/250000000000 : ℝ) (26013952733/50000000000 : ℝ) (130069763667/250000000000 : ℝ) (26013952733/50000000000 : ℝ) (130069763667/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1163/8192 : ℝ))) 7 (26013952733/50000000000 : ℝ) (130069763667/250000000000 : ℝ) (26013952733/50000000000 : ℝ) (130069763667/250000000000 : ℝ) (26013952733/50000000000 : ℝ) (130069763667/250000000000 : ℝ) (26013952733/50000000000 : ℝ) (130069763667/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1163/8192 : ℝ)) hmem 8 (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ) (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1163/8192 : ℝ))) hcmem 8 (26013952733/50000000000 : ℝ) (130069763667/250000000000 : ℝ) (26013952733/50000000000 : ℝ) (130069763667/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1163/8192 : ℝ)) (39597445409/40000000000 : ℝ) (247484033807/250000000000 : ℝ) (26013952733/50000000000 : ℝ) (130069763667/250000000000 : ℝ) (103195094977/125000000000 : ℝ) (103195094979/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0545_exp_lower
  have heNumeric : (2019076723939/1000000000000 : ℝ)/4 ≤ Real.exp (-2734616086203/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019076723939/1000000000000 : ℝ)/4 ≤ Real.exp ((2325/16384 : ℝ)-(103195094979/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2325/16384 : ℝ) (1163/8192 : ℝ) (103195094979/125000000000 : ℝ) (2019076723939/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0546; no trusted numerical premise.
theorem cover7_leaf0546_exp_radius : (49873349239293861/50000000000000000 : ℝ) ≤ Real.exp ((-2327/114688 : ℝ)/8) ∧ Real.exp ((-2327/114688 : ℝ)/8) ≤ (997466984785877221/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2327/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0546_exp_lower : (918093038616730691/1000000000000000000 : ℝ) ≤ Real.exp ((-1367304707863/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367304707863/2000000000000 : ℝ)/8) ≤ (229523259654182673/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367304707863/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0546_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019080090993/1000000000000 : ℝ) ≤ 4*Real.exp (1163/8192 : ℝ)*Real.exp (-mu (radius 7 (2327/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019080090993/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2327/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0546_exp_radius
  have hrNumeric : (979914623687/1000000000000 : ℝ) ≤ Real.exp (-2327/114688 : ℝ) ∧ Real.exp (-2327/114688 : ℝ) ≤ (122489327961/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979914623687/1000000000000 : ℝ) ≤ (radius 7 (2327/16384 : ℝ)) ∧ (radius 7 (2327/16384 : ℝ)) ≤ (122489327961/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2327/16384 : ℝ)) (979914623687/1000000000000 : ℝ) (122489327961/125000000000 : ℝ) (99708738687/500000000000 : ℝ) (9970873869/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2327/16384 : ℝ)) (979914623687/1000000000000 : ℝ) (122489327961/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2327/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979914623687/1000000000000 : ℝ) (122489327961/125000000000 : ℝ) (989957311843/1000000000000 : ℝ) (247489327961/250000000000 : ℝ) (247476592793/250000000000 : ℝ) (989906371173/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2327/16384 : ℝ)) 1 (989957311843/1000000000000 : ℝ) (247489327961/250000000000 : ℝ) (247476592793/250000000000 : ℝ) (989906371173/1000000000000 : ℝ) (989931841507/1000000000000 : ℝ) (989931841509/1000000000000 : ℝ) (989931841179/1000000000000 : ℝ) (989931841181/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2327/16384 : ℝ)) 2 (989931841507/1000000000000 : ℝ) (989931841509/1000000000000 : ℝ) (989931841179/1000000000000 : ℝ) (989931841181/1000000000000 : ℝ) (989931841343/1000000000000 : ℝ) (197986368269/200000000000 : ℝ) (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2327/16384 : ℝ)) 3 (989931841343/1000000000000 : ℝ) (197986368269/200000000000 : ℝ) (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ) (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ) (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2327/16384 : ℝ)) 4 (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ) (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ) (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ) (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2327/16384 : ℝ)) 5 (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ) (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ) (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ) (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2327/16384 : ℝ)) 6 (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ) (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ) (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ) (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2327/16384 : ℝ)) 7 (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ) (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ) (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ) (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2327/16384 : ℝ))) (99708738687/500000000000 : ℝ) (9970873869/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2327/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (99708738687/500000000000 : ℝ) (9970873869/50000000000 : ℝ) (599708738687/1000000000000 : ℝ) (59970873869/100000000000 : ℝ) (446561840481/1000000000000 : ℝ) (55820230061/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2327/16384 : ℝ))) 1 (599708738687/1000000000000 : ℝ) (59970873869/100000000000 : ℝ) (446561840481/1000000000000 : ℝ) (55820230061/125000000000 : ℝ) (32695955599/62500000000 : ℝ) (523135289589/1000000000000 : ℝ) (517500761449/1000000000000 : ℝ) (103500152291/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2327/16384 : ℝ))) 2 (32695955599/62500000000 : ℝ) (523135289589/1000000000000 : ℝ) (517500761449/1000000000000 : ℝ) (103500152291/200000000000 : ℝ) (130079506379/250000000000 : ℝ) (260159012761/500000000000 : ℝ) (32519399901/62500000000 : ℝ) (520310398423/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2327/16384 : ℝ))) 3 (130079506379/250000000000 : ℝ) (260159012761/500000000000 : ℝ) (32519399901/62500000000 : ℝ) (520310398423/1000000000000 : ℝ) (260157105983/500000000000 : ℝ) (520314211973/1000000000000 : ℝ) (32519638247/62500000000 : ℝ) (520314211959/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2327/16384 : ℝ))) 4 (260157105983/500000000000 : ℝ) (520314211973/1000000000000 : ℝ) (32519638247/62500000000 : ℝ) (520314211959/1000000000000 : ℝ) (520314211959/1000000000000 : ℝ) (260157105983/500000000000 : ℝ) (260157105979/500000000000 : ℝ) (260157105983/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2327/16384 : ℝ))) 5 (520314211959/1000000000000 : ℝ) (260157105983/500000000000 : ℝ) (260157105979/500000000000 : ℝ) (260157105983/500000000000 : ℝ) (260157105979/500000000000 : ℝ) (260157105983/500000000000 : ℝ) (260157105979/500000000000 : ℝ) (260157105983/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2327/16384 : ℝ))) 6 (260157105979/500000000000 : ℝ) (260157105983/500000000000 : ℝ) (260157105979/500000000000 : ℝ) (260157105983/500000000000 : ℝ) (260157105979/500000000000 : ℝ) (260157105983/500000000000 : ℝ) (260157105979/500000000000 : ℝ) (260157105983/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2327/16384 : ℝ))) 7 (260157105979/500000000000 : ℝ) (260157105983/500000000000 : ℝ) (260157105979/500000000000 : ℝ) (260157105983/500000000000 : ℝ) (260157105979/500000000000 : ℝ) (260157105983/500000000000 : ℝ) (260157105979/500000000000 : ℝ) (260157105983/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2327/16384 : ℝ)) hmem 8 (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ) (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2327/16384 : ℝ))) hcmem 8 (260157105979/500000000000 : ℝ) (260157105983/500000000000 : ℝ) (260157105979/500000000000 : ℝ) (260157105983/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2327/16384 : ℝ)) (494965920671/500000000000 : ℝ) (197986368269/200000000000 : ℝ) (260157105979/500000000000 : ℝ) (260157105983/500000000000 : ℝ) (825620127353/1000000000000 : ℝ) (825620127369/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0546_exp_lower
  have heNumeric : (2019080090993/1000000000000 : ℝ)/4 ≤ Real.exp (-1367304707863/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019080090993/1000000000000 : ℝ)/4 ≤ Real.exp ((1163/8192 : ℝ)-(825620127369/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1163/8192 : ℝ) (2327/16384 : ℝ) (825620127369/1000000000000 : ℝ) (2019080090993/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0547; no trusted numerical premise.
theorem cover7_leaf0547_exp_radius : (199493179526746539/200000000000000000 : ℝ) ≤ Real.exp ((-291/14336 : ℝ)/8) ∧ Real.exp ((-291/14336 : ℝ)/8) ≤ (124683237204216587/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-291/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0547_exp_lower : (114761653992755109/125000000000000000 : ℝ) ≤ Real.exp ((-2734602677401/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734602677401/4000000000000 : ℝ)/8) ≤ (918093231942040873/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734602677401/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0547_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (20190834923/10000000000 : ℝ) ≤ 4*Real.exp (2327/16384 : ℝ)*Real.exp (-mu (radius 7 (291/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (20190834923/10000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (291/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0547_exp_radius
  have hrNumeric : (489953039773/500000000000 : ℝ) ≤ Real.exp (-291/14336 : ℝ) ∧ Real.exp (-291/14336 : ℝ) ≤ (979906079547/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (489953039773/500000000000 : ℝ) ≤ (radius 7 (291/2048 : ℝ)) ∧ (radius 7 (291/2048 : ℝ)) ≤ (979906079547/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (291/2048 : ℝ)) (489953039773/500000000000 : ℝ) (979906079547/1000000000000 : ℝ) (99729728851/500000000000 : ℝ) (49864864427/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (291/2048 : ℝ)) (489953039773/500000000000 : ℝ) (979906079547/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (291/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (489953039773/500000000000 : ℝ) (979906079547/1000000000000 : ℝ) (989953039773/1000000000000 : ℝ) (494976519887/500000000000 : ℝ) (989902055531/1000000000000 : ℝ) (989902055533/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (291/2048 : ℝ)) 1 (989953039773/1000000000000 : ℝ) (494976519887/500000000000 : ℝ) (989902055531/1000000000000 : ℝ) (989902055533/1000000000000 : ℝ) (247481886913/250000000000 : ℝ) (494963773827/500000000000 : ℝ) (989927547323/1000000000000 : ℝ) (494963773663/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (291/2048 : ℝ)) 2 (247481886913/250000000000 : ℝ) (494963773827/500000000000 : ℝ) (989927547323/1000000000000 : ℝ) (494963773663/500000000000 : ℝ) (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ) (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (291/2048 : ℝ)) 3 (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ) (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ) (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ) (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (291/2048 : ℝ)) 4 (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ) (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ) (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ) (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (291/2048 : ℝ)) 5 (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ) (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ) (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ) (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (291/2048 : ℝ)) 6 (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ) (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ) (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ) (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (291/2048 : ℝ)) 7 (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ) (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ) (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ) (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (291/2048 : ℝ))) (99729728851/500000000000 : ℝ) (49864864427/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (291/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (99729728851/500000000000 : ℝ) (49864864427/250000000000 : ℝ) (599729728851/1000000000000 : ℝ) (299864864427/500000000000 : ℝ) (446608841943/1000000000000 : ℝ) (446608841951/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (291/2048 : ℝ))) 1 (599729728851/1000000000000 : ℝ) (299864864427/500000000000 : ℝ) (446608841943/1000000000000 : ℝ) (446608841951/1000000000000 : ℝ) (523169285397/1000000000000 : ℝ) (523169285403/1000000000000 : ℝ) (103507410301/200000000000 : ℝ) (64692131439/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (291/2048 : ℝ))) 2 (523169285397/1000000000000 : ℝ) (523169285403/1000000000000 : ℝ) (103507410301/200000000000 : ℝ) (64692131439/125000000000 : ℝ) (520353168451/1000000000000 : ℝ) (260176584229/500000000000 : ℝ) (20813821923/40000000000 : ℝ) (520345548083/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (291/2048 : ℝ))) 3 (520353168451/1000000000000 : ℝ) (260176584229/500000000000 : ℝ) (20813821923/40000000000 : ℝ) (520345548083/1000000000000 : ℝ) (520349358263/1000000000000 : ℝ) (520349358271/1000000000000 : ℝ) (520349358249/1000000000000 : ℝ) (520349358257/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (291/2048 : ℝ))) 4 (520349358263/1000000000000 : ℝ) (520349358271/1000000000000 : ℝ) (520349358249/1000000000000 : ℝ) (520349358257/1000000000000 : ℝ) (32521834891/62500000000 : ℝ) (65043669783/125000000000 : ℝ) (104069871651/200000000000 : ℝ) (65043669783/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (291/2048 : ℝ))) 5 (32521834891/62500000000 : ℝ) (65043669783/125000000000 : ℝ) (104069871651/200000000000 : ℝ) (65043669783/125000000000 : ℝ) (104069871651/200000000000 : ℝ) (65043669783/125000000000 : ℝ) (104069871651/200000000000 : ℝ) (65043669783/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (291/2048 : ℝ))) 6 (104069871651/200000000000 : ℝ) (65043669783/125000000000 : ℝ) (104069871651/200000000000 : ℝ) (65043669783/125000000000 : ℝ) (104069871651/200000000000 : ℝ) (65043669783/125000000000 : ℝ) (104069871651/200000000000 : ℝ) (65043669783/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (291/2048 : ℝ))) 7 (104069871651/200000000000 : ℝ) (65043669783/125000000000 : ℝ) (104069871651/200000000000 : ℝ) (65043669783/125000000000 : ℝ) (104069871651/200000000000 : ℝ) (65043669783/125000000000 : ℝ) (104069871651/200000000000 : ℝ) (65043669783/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (291/2048 : ℝ)) hmem 8 (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ) (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (291/2048 : ℝ))) hcmem 8 (104069871651/200000000000 : ℝ) (65043669783/125000000000 : ℝ) (104069871651/200000000000 : ℝ) (65043669783/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (291/2048 : ℝ)) (989927547487/1000000000000 : ℝ) (98992754749/100000000000 : ℝ) (104069871651/200000000000 : ℝ) (65043669783/125000000000 : ℝ) (412839738963/500000000000 : ℝ) (103209934743/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0547_exp_lower
  have heNumeric : (20190834923/10000000000 : ℝ)/4 ≤ Real.exp (-2734602677401/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (20190834923/10000000000 : ℝ)/4 ≤ Real.exp ((2327/16384 : ℝ)-(103209934743/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2327/16384 : ℝ) (291/2048 : ℝ) (103209934743/125000000000 : ℝ) (20190834923/10000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0548; no trusted numerical premise.
theorem cover7_leaf0548_exp_radius : (62341550655173317/62500000000000000 : ℝ) ≤ Real.exp ((-2329/114688 : ℝ)/8) ∧ Real.exp ((-2329/114688 : ℝ)/8) ≤ (997464810482773073/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2329/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0548_exp_lower : (918093427215356489/1000000000000000000 : ℝ) ≤ Real.exp ((-136729793559/200000000000 : ℝ)/8) ∧ Real.exp ((-136729793559/200000000000 : ℝ)/8) ≤ (91809342721535649/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-136729793559/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0548_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403817385577/200000000000 : ℝ) ≤ 4*Real.exp (291/2048 : ℝ)*Real.exp (-mu (radius 7 (2329/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (403817385577/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2329/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0548_exp_radius
  have hrNumeric : (979897535481/1000000000000 : ℝ) ≤ Real.exp (-2329/114688 : ℝ) ∧ Real.exp (-2329/114688 : ℝ) ≤ (489948767741/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979897535481/1000000000000 : ℝ) ≤ (radius 7 (2329/16384 : ℝ)) ∧ (radius 7 (2329/16384 : ℝ)) ≤ (489948767741/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2329/16384 : ℝ)) (979897535481/1000000000000 : ℝ) (489948767741/500000000000 : ℝ) (24937678557/125000000000 : ℝ) (99750714231/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2329/16384 : ℝ)) (979897535481/1000000000000 : ℝ) (489948767741/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2329/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979897535481/1000000000000 : ℝ) (489948767741/500000000000 : ℝ) (49497438387/50000000000 : ℝ) (989948767741/1000000000000 : ℝ) (989897739911/1000000000000 : ℝ) (123737217489/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2329/16384 : ℝ)) 1 (49497438387/50000000000 : ℝ) (989948767741/1000000000000 : ℝ) (989897739911/1000000000000 : ℝ) (123737217489/125000000000 : ℝ) (39596930153/40000000000 : ℝ) (989923253827/1000000000000 : ℝ) (123740406687/125000000000 : ℝ) (494961626749/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2329/16384 : ℝ)) 2 (39596930153/40000000000 : ℝ) (989923253827/1000000000000 : ℝ) (123740406687/125000000000 : ℝ) (494961626749/500000000000 : ℝ) (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ) (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2329/16384 : ℝ)) 3 (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ) (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ) (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ) (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2329/16384 : ℝ)) 4 (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ) (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ) (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ) (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2329/16384 : ℝ)) 5 (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ) (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ) (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ) (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2329/16384 : ℝ)) 6 (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ) (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ) (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ) (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2329/16384 : ℝ)) 7 (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ) (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ) (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ) (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2329/16384 : ℝ))) (24937678557/125000000000 : ℝ) (99750714231/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2329/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24937678557/125000000000 : ℝ) (99750714231/500000000000 : ℝ) (149937678557/250000000000 : ℝ) (599750714231/1000000000000 : ℝ) (223327913871/500000000000 : ℝ) (446655827749/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2329/16384 : ℝ))) 1 (149937678557/250000000000 : ℝ) (599750714231/1000000000000 : ℝ) (223327913871/500000000000 : ℝ) (446655827749/1000000000000 : ℝ) (104640654197/200000000000 : ℝ) (52320327099/100000000000 : ℝ) (258786664891/500000000000 : ℝ) (517573329789/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2329/16384 : ℝ))) 2 (104640654197/200000000000 : ℝ) (52320327099/100000000000 : ℝ) (258786664891/500000000000 : ℝ) (517573329789/1000000000000 : ℝ) (520388300383/1000000000000 : ℝ) (52038830039/100000000000 : ℝ) (20815227469/40000000000 : ℝ) (130095171683/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2329/16384 : ℝ))) 3 (520388300383/1000000000000 : ℝ) (52038830039/100000000000 : ℝ) (20815227469/40000000000 : ℝ) (130095171683/250000000000 : ℝ) (260192246777/500000000000 : ℝ) (520384493561/1000000000000 : ℝ) (26019224677/50000000000 : ℝ) (130096123387/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2329/16384 : ℝ))) 4 (260192246777/500000000000 : ℝ) (520384493561/1000000000000 : ℝ) (26019224677/50000000000 : ℝ) (130096123387/250000000000 : ℝ) (520384493547/1000000000000 : ℝ) (104076898711/200000000000 : ℝ) (260192246773/500000000000 : ℝ) (104076898711/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2329/16384 : ℝ))) 5 (520384493547/1000000000000 : ℝ) (104076898711/200000000000 : ℝ) (260192246773/500000000000 : ℝ) (104076898711/200000000000 : ℝ) (260192246773/500000000000 : ℝ) (104076898711/200000000000 : ℝ) (260192246773/500000000000 : ℝ) (104076898711/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2329/16384 : ℝ))) 6 (260192246773/500000000000 : ℝ) (104076898711/200000000000 : ℝ) (260192246773/500000000000 : ℝ) (104076898711/200000000000 : ℝ) (260192246773/500000000000 : ℝ) (104076898711/200000000000 : ℝ) (260192246773/500000000000 : ℝ) (104076898711/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2329/16384 : ℝ))) 7 (260192246773/500000000000 : ℝ) (104076898711/200000000000 : ℝ) (260192246773/500000000000 : ℝ) (104076898711/200000000000 : ℝ) (260192246773/500000000000 : ℝ) (104076898711/200000000000 : ℝ) (260192246773/500000000000 : ℝ) (104076898711/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2329/16384 : ℝ)) hmem 8 (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ) (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2329/16384 : ℝ))) hcmem 8 (260192246773/500000000000 : ℝ) (104076898711/200000000000 : ℝ) (260192246773/500000000000 : ℝ) (104076898711/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2329/16384 : ℝ)) (49496162683/50000000000 : ℝ) (989923253663/1000000000000 : ℝ) (260192246773/500000000000 : ℝ) (104076898711/200000000000 : ℝ) (825738811527/1000000000000 : ℝ) (165147762309/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0548_exp_lower
  have heNumeric : (403817385577/200000000000 : ℝ)/4 ≤ Real.exp (-136729793559/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403817385577/200000000000 : ℝ)/4 ≤ Real.exp ((291/2048 : ℝ)-(165147762309/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (291/2048 : ℝ) (2329/16384 : ℝ) (165147762309/200000000000 : ℝ) (403817385577/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0549; no trusted numerical premise.
theorem cover7_leaf0549_exp_radius : (997463723332998349/1000000000000000000 : ℝ) ≤ Real.exp ((-1165/57344 : ℝ)/8) ∧ Real.exp ((-1165/57344 : ℝ)/8) ≤ (19949274466659967/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1165/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0549_exp_lower : (918093624433580219/1000000000000000000 : ℝ) ≤ Real.exp ((-2734588997171/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734588997171/4000000000000 : ℝ)/8) ≤ (45904681221679011/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734588997171/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0549_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019090397693/1000000000000 : ℝ) ≤ 4*Real.exp (2329/16384 : ℝ)*Real.exp (-mu (radius 7 (1165/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019090397693/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1165/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0549_exp_radius
  have hrNumeric : (97988899149/100000000000 : ℝ) ≤ Real.exp (-1165/57344 : ℝ) ∧ Real.exp (-1165/57344 : ℝ) ≤ (979888991491/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (97988899149/100000000000 : ℝ) ≤ (radius 7 (1165/8192 : ℝ)) ∧ (radius 7 (1165/8192 : ℝ)) ≤ (979888991491/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1165/8192 : ℝ)) (97988899149/100000000000 : ℝ) (979888991491/1000000000000 : ℝ) (99771694827/500000000000 : ℝ) (9977169483/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1165/8192 : ℝ)) (97988899149/100000000000 : ℝ) (979888991491/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1165/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (97988899149/100000000000 : ℝ) (979888991491/1000000000000 : ℝ) (197988899149/200000000000 : ℝ) (494972247873/500000000000 : ℝ) (247473356077/250000000000 : ℝ) (98989342431/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1165/8192 : ℝ)) 1 (197988899149/200000000000 : ℝ) (494972247873/500000000000 : ℝ) (247473356077/250000000000 : ℝ) (98989342431/100000000000 : ℝ) (494959480013/500000000000 : ℝ) (247479740007/250000000000 : ℝ) (989918959697/1000000000000 : ℝ) (989918959699/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1165/8192 : ℝ)) 2 (494959480013/500000000000 : ℝ) (247479740007/250000000000 : ℝ) (989918959697/1000000000000 : ℝ) (989918959699/1000000000000 : ℝ) (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ) (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1165/8192 : ℝ)) 3 (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ) (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ) (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ) (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1165/8192 : ℝ)) 4 (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ) (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ) (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ) (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1165/8192 : ℝ)) 5 (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ) (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ) (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ) (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1165/8192 : ℝ)) 6 (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ) (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ) (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ) (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1165/8192 : ℝ)) 7 (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ) (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ) (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ) (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1165/8192 : ℝ))) (99771694827/500000000000 : ℝ) (9977169483/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1165/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (99771694827/500000000000 : ℝ) (9977169483/50000000000 : ℝ) (599771694827/1000000000000 : ℝ) (59977169483/100000000000 : ℝ) (223351398951/500000000000 : ℝ) (44670279791/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1165/8192 : ℝ))) 1 (599771694827/1000000000000 : ℝ) (59977169483/100000000000 : ℝ) (223351398951/500000000000 : ℝ) (44670279791/100000000000 : ℝ) (130809311591/250000000000 : ℝ) (52323724637/100000000000 : ℝ) (517609596299/1000000000000 : ℝ) (258804798153/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1165/8192 : ℝ))) 2 (130809311591/250000000000 : ℝ) (52323724637/100000000000 : ℝ) (517609596299/1000000000000 : ℝ) (258804798153/500000000000 : ℝ) (520423421331/1000000000000 : ℝ) (260211710669/500000000000 : ℝ) (260207907191/500000000000 : ℝ) (520415814389/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1165/8192 : ℝ))) 3 (520423421331/1000000000000 : ℝ) (260211710669/500000000000 : ℝ) (260207907191/500000000000 : ℝ) (520415814389/1000000000000 : ℝ) (8131556529/15625000000 : ℝ) (65052452233/125000000000 : ℝ) (260209808921/500000000000 : ℝ) (10408392357/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1165/8192 : ℝ))) 4 (8131556529/15625000000 : ℝ) (65052452233/125000000000 : ℝ) (260209808921/500000000000 : ℝ) (10408392357/20000000000 : ℝ) (520419617849/1000000000000 : ℝ) (520419617857/1000000000000 : ℝ) (65052452231/125000000000 : ℝ) (520419617857/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1165/8192 : ℝ))) 5 (520419617849/1000000000000 : ℝ) (520419617857/1000000000000 : ℝ) (65052452231/125000000000 : ℝ) (520419617857/1000000000000 : ℝ) (65052452231/125000000000 : ℝ) (520419617857/1000000000000 : ℝ) (65052452231/125000000000 : ℝ) (520419617857/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1165/8192 : ℝ))) 6 (65052452231/125000000000 : ℝ) (520419617857/1000000000000 : ℝ) (65052452231/125000000000 : ℝ) (520419617857/1000000000000 : ℝ) (65052452231/125000000000 : ℝ) (520419617857/1000000000000 : ℝ) (65052452231/125000000000 : ℝ) (520419617857/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1165/8192 : ℝ))) 7 (65052452231/125000000000 : ℝ) (520419617857/1000000000000 : ℝ) (65052452231/125000000000 : ℝ) (520419617857/1000000000000 : ℝ) (65052452231/125000000000 : ℝ) (520419617857/1000000000000 : ℝ) (65052452231/125000000000 : ℝ) (520419617857/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1165/8192 : ℝ)) hmem 8 (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ) (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1165/8192 : ℝ))) hcmem 8 (65052452231/125000000000 : ℝ) (520419617857/1000000000000 : ℝ) (65052452231/125000000000 : ℝ) (520419617857/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1165/8192 : ℝ)) (989918959861/1000000000000 : ℝ) (123739869983/125000000000 : ℝ) (65052452231/125000000000 : ℝ) (520419617857/1000000000000 : ℝ) (412899064091/500000000000 : ℝ) (825798128199/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0549_exp_lower
  have heNumeric : (2019090397693/1000000000000 : ℝ)/4 ≤ Real.exp (-2734588997171/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019090397693/1000000000000 : ℝ)/4 ≤ Real.exp ((2329/16384 : ℝ)-(825798128199/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2329/16384 : ℝ) (1165/8192 : ℝ) (825798128199/1000000000000 : ℝ) (2019090397693/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0525_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0525_certificate
#check SmaleRate.Proofs.cover7_leaf0526_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0526_certificate
#check SmaleRate.Proofs.cover7_leaf0527_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0527_certificate
#check SmaleRate.Proofs.cover7_leaf0528_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0528_certificate
#check SmaleRate.Proofs.cover7_leaf0529_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0529_certificate
#check SmaleRate.Proofs.cover7_leaf0530_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0530_certificate
#check SmaleRate.Proofs.cover7_leaf0531_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0531_certificate
#check SmaleRate.Proofs.cover7_leaf0532_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0532_certificate
#check SmaleRate.Proofs.cover7_leaf0533_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0533_certificate
#check SmaleRate.Proofs.cover7_leaf0534_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0534_certificate
#check SmaleRate.Proofs.cover7_leaf0535_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0535_certificate
#check SmaleRate.Proofs.cover7_leaf0536_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0536_certificate
#check SmaleRate.Proofs.cover7_leaf0537_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0537_certificate
#check SmaleRate.Proofs.cover7_leaf0538_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0538_certificate
#check SmaleRate.Proofs.cover7_leaf0539_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0539_certificate
#check SmaleRate.Proofs.cover7_leaf0540_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0540_certificate
#check SmaleRate.Proofs.cover7_leaf0541_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0541_certificate
#check SmaleRate.Proofs.cover7_leaf0542_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0542_certificate
#check SmaleRate.Proofs.cover7_leaf0543_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0543_certificate
#check SmaleRate.Proofs.cover7_leaf0544_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0544_certificate
#check SmaleRate.Proofs.cover7_leaf0545_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0545_certificate
#check SmaleRate.Proofs.cover7_leaf0546_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0546_certificate
#check SmaleRate.Proofs.cover7_leaf0547_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0547_certificate
#check SmaleRate.Proofs.cover7_leaf0548_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0548_certificate
#check SmaleRate.Proofs.cover7_leaf0549_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0549_certificate
