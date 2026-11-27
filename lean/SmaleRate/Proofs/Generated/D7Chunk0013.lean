/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0325; no trusted numerical premise.
theorem cover7_leaf0325_exp_radius : (997568095114699709/1000000000000000000 : ℝ) ≤ Real.exp ((-1117/57344 : ℝ)/8) ∧ Real.exp ((-1117/57344 : ℝ)/8) ≤ (99756809511469971/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1117/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0325_exp_lower : (57380564329075503/62500000000000000 : ℝ) ≤ Real.exp ((-10938996645593/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938996645593/16000000000000 : ℝ)/8) ≤ (918089029265208049/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938996645593/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0325_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019009552799/1000000000000 : ℝ) ≤ 4*Real.exp (8935/65536 : ℝ)*Real.exp (-mu (radius 7 (1117/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019009552799/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1117/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0325_exp_radius
  have hrNumeric : (980709554449/1000000000000 : ℝ) ≤ Real.exp (-1117/57344 : ℝ) ∧ Real.exp (-1117/57344 : ℝ) ≤ (19614191089/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980709554449/1000000000000 : ℝ) ≤ (radius 7 (1117/8192 : ℝ)) ∧ (radius 7 (1117/8192 : ℝ)) ≤ (19614191089/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1117/8192 : ℝ)) (980709554449/1000000000000 : ℝ) (19614191089/20000000000 : ℝ) (24433829587/125000000000 : ℝ) (97735318351/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1117/8192 : ℝ)) (980709554449/1000000000000 : ℝ) (19614191089/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1117/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980709554449/1000000000000 : ℝ) (19614191089/20000000000 : ℝ) (123794347153/125000000000 : ℝ) (39614191089/40000000000 : ℝ) (99030780793/100000000000 : ℝ) (247576951983/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1117/8192 : ℝ)) 1 (123794347153/125000000000 : ℝ) (39614191089/40000000000 : ℝ) (99030780793/100000000000 : ℝ) (247576951983/250000000000 : ℝ) (990331292577/1000000000000 : ℝ) (990331292579/1000000000000 : ℝ) (495165646149/500000000000 : ℝ) (990331292301/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1117/8192 : ℝ)) 2 (990331292577/1000000000000 : ℝ) (990331292579/1000000000000 : ℝ) (495165646149/500000000000 : ℝ) (990331292301/1000000000000 : ℝ) (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ) (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1117/8192 : ℝ)) 3 (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ) (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ) (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ) (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1117/8192 : ℝ)) 4 (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ) (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ) (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ) (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1117/8192 : ℝ)) 5 (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ) (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ) (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ) (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1117/8192 : ℝ)) 6 (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ) (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ) (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ) (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1117/8192 : ℝ)) 7 (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ) (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ) (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ) (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1117/8192 : ℝ))) (24433829587/125000000000 : ℝ) (97735318351/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1117/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24433829587/125000000000 : ℝ) (97735318351/500000000000 : ℝ) (149433829587/250000000000 : ℝ) (597735318351/1000000000000 : ℝ) (44212061329/100000000000 : ℝ) (442120613297/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1117/8192 : ℝ))) 1 (149433829587/250000000000 : ℝ) (597735318351/1000000000000 : ℝ) (44212061329/100000000000 : ℝ) (442120613297/1000000000000 : ℝ) (519927965819/1000000000000 : ℝ) (4061937233/7812500000 : ℝ) (102814610933/200000000000 : ℝ) (514073054671/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1117/8192 : ℝ))) 2 (519927965819/1000000000000 : ℝ) (4061937233/7812500000 : ℝ) (102814610933/200000000000 : ℝ) (514073054671/1000000000000 : ℝ) (258500255121/500000000000 : ℝ) (64625063781/125000000000 : ℝ) (258496110993/500000000000 : ℝ) (64624027749/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1117/8192 : ℝ))) 3 (258500255121/500000000000 : ℝ) (64625063781/125000000000 : ℝ) (258496110993/500000000000 : ℝ) (64624027749/125000000000 : ℝ) (258498183057/500000000000 : ℝ) (12924909153/25000000000 : ℝ) (516996366097/1000000000000 : ℝ) (64624545763/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1117/8192 : ℝ))) 4 (258498183057/500000000000 : ℝ) (12924909153/25000000000 : ℝ) (516996366097/1000000000000 : ℝ) (64624545763/125000000000 : ℝ) (103399273221/200000000000 : ℝ) (16156136441/31250000000 : ℝ) (103399273221/200000000000 : ℝ) (16156136441/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1117/8192 : ℝ))) 5 (103399273221/200000000000 : ℝ) (16156136441/31250000000 : ℝ) (103399273221/200000000000 : ℝ) (16156136441/31250000000 : ℝ) (103399273221/200000000000 : ℝ) (16156136441/31250000000 : ℝ) (103399273221/200000000000 : ℝ) (16156136441/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1117/8192 : ℝ))) 6 (103399273221/200000000000 : ℝ) (16156136441/31250000000 : ℝ) (103399273221/200000000000 : ℝ) (16156136441/31250000000 : ℝ) (103399273221/200000000000 : ℝ) (16156136441/31250000000 : ℝ) (103399273221/200000000000 : ℝ) (16156136441/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1117/8192 : ℝ))) 7 (103399273221/200000000000 : ℝ) (16156136441/31250000000 : ℝ) (103399273221/200000000000 : ℝ) (16156136441/31250000000 : ℝ) (103399273221/200000000000 : ℝ) (16156136441/31250000000 : ℝ) (103399273221/200000000000 : ℝ) (16156136441/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1117/8192 : ℝ)) hmem 8 (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ) (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1117/8192 : ℝ))) hcmem 8 (103399273221/200000000000 : ℝ) (16156136441/31250000000 : ℝ) (103399273221/200000000000 : ℝ) (16156136441/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1117/8192 : ℝ)) (990331292437/1000000000000 : ℝ) (24758282311/25000000000 : ℝ) (103399273221/200000000000 : ℝ) (16156136441/31250000000 : ℝ) (820024570609/1000000000000 : ℝ) (820024570623/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0325_exp_lower
  have heNumeric : (2019009552799/1000000000000 : ℝ)/4 ≤ Real.exp (-10938996645593/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019009552799/1000000000000 : ℝ)/4 ≤ Real.exp ((8935/65536 : ℝ)-(820024570623/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8935/65536 : ℝ) (1117/8192 : ℝ) (820024570623/1000000000000 : ℝ) (2019009552799/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0326; no trusted numerical premise.
theorem cover7_leaf0326_exp_radius : (997567823299002119/1000000000000000000 : ℝ) ≤ Real.exp ((-8937/458752 : ℝ)/8) ∧ Real.exp ((-8937/458752 : ℝ)/8) ≤ (24939195582475053/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8937/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0326_exp_lower : (918089030483519363/1000000000000000000 : ℝ) ≤ Real.exp ((-1367374559467/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367374559467/2000000000000 : ℝ)/8) ≤ (229522257620879841/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367374559467/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0326_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019009574233/1000000000000 : ℝ) ≤ 4*Real.exp (1117/8192 : ℝ)*Real.exp (-mu (radius 7 (8937/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019009574233/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8937/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0326_exp_radius
  have hrNumeric : (490353708337/500000000000 : ℝ) ≤ Real.exp (-8937/458752 : ℝ) ∧ Real.exp (-8937/458752 : ℝ) ≤ (39228296667/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490353708337/500000000000 : ℝ) ≤ (radius 7 (8937/65536 : ℝ)) ∧ (radius 7 (8937/65536 : ℝ)) ≤ (39228296667/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8937/65536 : ℝ)) (490353708337/500000000000 : ℝ) (39228296667/40000000000 : ℝ) (48870340493/250000000000 : ℝ) (97740680989/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8937/65536 : ℝ)) (490353708337/500000000000 : ℝ) (39228296667/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8937/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490353708337/500000000000 : ℝ) (39228296667/40000000000 : ℝ) (990353708337/1000000000000 : ℝ) (495176854169/500000000000 : ℝ) (990306728581/1000000000000 : ℝ) (990306728583/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8937/65536 : ℝ)) 1 (990353708337/1000000000000 : ℝ) (495176854169/500000000000 : ℝ) (990306728581/1000000000000 : ℝ) (990306728583/1000000000000 : ℝ) (990330218459/1000000000000 : ℝ) (990330218461/1000000000000 : ℝ) (49516510909/50000000000 : ℝ) (495165109091/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8937/65536 : ℝ)) 2 (990330218459/1000000000000 : ℝ) (990330218461/1000000000000 : ℝ) (49516510909/50000000000 : ℝ) (495165109091/500000000000 : ℝ) (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ) (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8937/65536 : ℝ)) 3 (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ) (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ) (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ) (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8937/65536 : ℝ)) 4 (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ) (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ) (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ) (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8937/65536 : ℝ)) 5 (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ) (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ) (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ) (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8937/65536 : ℝ)) 6 (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ) (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ) (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ) (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8937/65536 : ℝ)) 7 (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ) (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ) (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ) (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8937/65536 : ℝ))) (48870340493/250000000000 : ℝ) (97740680989/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8937/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48870340493/250000000000 : ℝ) (97740680989/500000000000 : ℝ) (298870340493/500000000000 : ℝ) (597740680989/1000000000000 : ℝ) (221066371239/500000000000 : ℝ) (221066371243/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8937/65536 : ℝ))) 1 (298870340493/500000000000 : ℝ) (597740680989/1000000000000 : ℝ) (221066371239/500000000000 : ℝ) (221066371243/500000000000 : ℝ) (129984177933/250000000000 : ℝ) (259968355869/500000000000 : ℝ) (6426030153/12500000000 : ℝ) (514082412247/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8937/65536 : ℝ))) 2 (129984177933/250000000000 : ℝ) (259968355869/500000000000 : ℝ) (6426030153/12500000000 : ℝ) (514082412247/1000000000000 : ℝ) (258504780993/500000000000 : ℝ) (517009561993/1000000000000 : ℝ) (517001275607/1000000000000 : ℝ) (258500637807/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8937/65536 : ℝ))) 3 (258504780993/500000000000 : ℝ) (517009561993/1000000000000 : ℝ) (517001275607/1000000000000 : ℝ) (258500637807/500000000000 : ℝ) (129251354699/250000000000 : ℝ) (129251354701/250000000000 : ℝ) (517005418779/1000000000000 : ℝ) (517005418787/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8937/65536 : ℝ))) 4 (129251354699/250000000000 : ℝ) (129251354701/250000000000 : ℝ) (517005418779/1000000000000 : ℝ) (517005418787/1000000000000 : ℝ) (517005418787/1000000000000 : ℝ) (129251354699/250000000000 : ℝ) (517005418787/1000000000000 : ℝ) (129251354699/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8937/65536 : ℝ))) 5 (517005418787/1000000000000 : ℝ) (129251354699/250000000000 : ℝ) (517005418787/1000000000000 : ℝ) (129251354699/250000000000 : ℝ) (517005418787/1000000000000 : ℝ) (129251354699/250000000000 : ℝ) (517005418787/1000000000000 : ℝ) (129251354699/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8937/65536 : ℝ))) 6 (517005418787/1000000000000 : ℝ) (129251354699/250000000000 : ℝ) (517005418787/1000000000000 : ℝ) (129251354699/250000000000 : ℝ) (517005418787/1000000000000 : ℝ) (129251354699/250000000000 : ℝ) (517005418787/1000000000000 : ℝ) (129251354699/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8937/65536 : ℝ))) 7 (517005418787/1000000000000 : ℝ) (129251354699/250000000000 : ℝ) (517005418787/1000000000000 : ℝ) (129251354699/250000000000 : ℝ) (517005418787/1000000000000 : ℝ) (129251354699/250000000000 : ℝ) (517005418787/1000000000000 : ℝ) (129251354699/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8937/65536 : ℝ)) hmem 8 (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ) (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8937/65536 : ℝ))) hcmem 8 (517005418787/1000000000000 : ℝ) (129251354699/250000000000 : ℝ) (517005418787/1000000000000 : ℝ) (129251354699/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8937/65536 : ℝ)) (990330218319/1000000000000 : ℝ) (495165109161/500000000000 : ℝ) (517005418787/1000000000000 : ℝ) (129251354699/250000000000 : ℝ) (410019909389/500000000000 : ℝ) (205009954699/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0326_exp_lower
  have heNumeric : (2019009574233/1000000000000 : ℝ)/4 ≤ Real.exp (-1367374559467/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019009574233/1000000000000 : ℝ)/4 ≤ Real.exp ((1117/8192 : ℝ)-(205009954699/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1117/8192 : ℝ) (8937/65536 : ℝ) (205009954699/250000000000 : ℝ) (2019009574233/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0327; no trusted numerical premise.
theorem cover7_leaf0327_exp_radius : (997567551483378593/1000000000000000000 : ℝ) ≤ Real.exp ((-4469/229376 : ℝ)/8) ∧ Real.exp ((-4469/229376 : ℝ)/8) ≤ (498783775741689297/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4469/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0327_exp_lower : (229522257958279353/250000000000000000 : ℝ) ≤ Real.exp ((-437559851503/640000000000 : ℝ)/8) ∧ Real.exp ((-437559851503/640000000000 : ℝ)/8) ≤ (918089031833117413/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-437559851503/640000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0327_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252376199747/125000000000 : ℝ) ≤ 4*Real.exp (8937/65536 : ℝ)*Real.exp (-mu (radius 7 (4469/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (252376199747/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4469/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0327_exp_radius
  have hrNumeric : (122588159863/125000000000 : ℝ) ≤ Real.exp (-4469/229376 : ℝ) ∧ Real.exp (-4469/229376 : ℝ) ≤ (196141055781/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122588159863/125000000000 : ℝ) ≤ (radius 7 (4469/32768 : ℝ)) ∧ (radius 7 (4469/32768 : ℝ)) ≤ (196141055781/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4469/32768 : ℝ)) (122588159863/125000000000 : ℝ) (196141055781/200000000000 : ℝ) (195492086611/1000000000000 : ℝ) (195492086617/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4469/32768 : ℝ)) (122588159863/125000000000 : ℝ) (196141055781/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4469/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122588159863/125000000000 : ℝ) (196141055781/200000000000 : ℝ) (247588159863/250000000000 : ℝ) (990352639453/1000000000000 : ℝ) (990305649233/1000000000000 : ℝ) (198061129847/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4469/32768 : ℝ)) 1 (247588159863/250000000000 : ℝ) (990352639453/1000000000000 : ℝ) (990305649233/1000000000000 : ℝ) (198061129847/200000000000 : ℝ) (495164572171/500000000000 : ℝ) (123791143043/125000000000 : ℝ) (990329144063/1000000000000 : ℝ) (495164572033/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4469/32768 : ℝ)) 2 (495164572171/500000000000 : ℝ) (123791143043/125000000000 : ℝ) (990329144063/1000000000000 : ℝ) (495164572033/500000000000 : ℝ) (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ) (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4469/32768 : ℝ)) 3 (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ) (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ) (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ) (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4469/32768 : ℝ)) 4 (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ) (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ) (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ) (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4469/32768 : ℝ)) 5 (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ) (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ) (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ) (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4469/32768 : ℝ)) 6 (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ) (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ) (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ) (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4469/32768 : ℝ)) 7 (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ) (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ) (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ) (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4469/32768 : ℝ))) (195492086611/1000000000000 : ℝ) (195492086617/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4469/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195492086611/1000000000000 : ℝ) (195492086617/1000000000000 : ℝ) (119549208661/200000000000 : ℝ) (597746043309/1000000000000 : ℝ) (221072435307/500000000000 : ℝ) (221072435311/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4469/32768 : ℝ))) 1 (119549208661/200000000000 : ℝ) (597746043309/1000000000000 : ℝ) (221072435307/500000000000 : ℝ) (221072435311/500000000000 : ℝ) (519945456959/1000000000000 : ℝ) (259972728483/500000000000 : ℝ) (257045884511/500000000000 : ℝ) (51409176903/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4469/32768 : ℝ))) 2 (519945456959/1000000000000 : ℝ) (259972728483/500000000000 : ℝ) (257045884511/500000000000 : ℝ) (51409176903/100000000000 : ℝ) (51701861299/100000000000 : ℝ) (258509306499/500000000000 : ℝ) (517010328487/1000000000000 : ℝ) (32313145531/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4469/32768 : ℝ))) 3 (51701861299/100000000000 : ℝ) (258509306499/500000000000 : ℝ) (517010328487/1000000000000 : ℝ) (32313145531/62500000000 : ℝ) (258507235369/500000000000 : ℝ) (517014470747/1000000000000 : ℝ) (517014470721/1000000000000 : ℝ) (517014470731/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4469/32768 : ℝ))) 4 (258507235369/500000000000 : ℝ) (517014470747/1000000000000 : ℝ) (517014470721/1000000000000 : ℝ) (517014470731/1000000000000 : ℝ) (517014470729/1000000000000 : ℝ) (517014470739/1000000000000 : ℝ) (517014470729/1000000000000 : ℝ) (517014470739/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4469/32768 : ℝ))) 5 (517014470729/1000000000000 : ℝ) (517014470739/1000000000000 : ℝ) (517014470729/1000000000000 : ℝ) (517014470739/1000000000000 : ℝ) (517014470729/1000000000000 : ℝ) (517014470739/1000000000000 : ℝ) (517014470729/1000000000000 : ℝ) (517014470739/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4469/32768 : ℝ))) 6 (517014470729/1000000000000 : ℝ) (517014470739/1000000000000 : ℝ) (517014470729/1000000000000 : ℝ) (517014470739/1000000000000 : ℝ) (517014470729/1000000000000 : ℝ) (517014470739/1000000000000 : ℝ) (517014470729/1000000000000 : ℝ) (517014470739/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4469/32768 : ℝ))) 7 (517014470729/1000000000000 : ℝ) (517014470739/1000000000000 : ℝ) (517014470729/1000000000000 : ℝ) (517014470739/1000000000000 : ℝ) (517014470729/1000000000000 : ℝ) (517014470739/1000000000000 : ℝ) (517014470729/1000000000000 : ℝ) (517014470739/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4469/32768 : ℝ)) hmem 8 (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ) (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4469/32768 : ℝ))) hcmem 8 (517014470729/1000000000000 : ℝ) (517014470739/1000000000000 : ℝ) (517014470729/1000000000000 : ℝ) (517014470739/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4469/32768 : ℝ)) (495164572101/500000000000 : ℝ) (198065828841/200000000000 : ℝ) (517014470729/1000000000000 : ℝ) (517014470739/1000000000000 : ℝ) (410027532903/500000000000 : ℝ) (32802202633/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0327_exp_lower
  have heNumeric : (252376199747/125000000000 : ℝ)/4 ≤ Real.exp (-437559851503/640000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252376199747/125000000000 : ℝ)/4 ≤ Real.exp ((8937/65536 : ℝ)-(32802202633/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8937/65536 : ℝ) (4469/32768 : ℝ) (32802202633/40000000000 : ℝ) (252376199747/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0328; no trusted numerical premise.
theorem cover7_leaf0328_exp_radius : (99756727966782913/100000000000000000 : ℝ) ≤ Real.exp ((-1277/65536 : ℝ)/8) ∧ Real.exp ((-1277/65536 : ℝ)/8) ≤ (997567279667829131/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1277/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0328_exp_lower : (918089033313543149/1000000000000000000 : ℝ) ≤ Real.exp ((-5469498040587/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469498040587/8000000000000 : ℝ)/8) ≤ (18361780666270863/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469498040587/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0328_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009504812011/500000000000 : ℝ) ≤ 4*Real.exp (4469/32768 : ℝ)*Real.exp (-mu (radius 7 (8939/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009504812011/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8939/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0328_exp_radius
  have hrNumeric : (980703141139/1000000000000 : ℝ) ≤ Real.exp (-1277/65536 : ℝ) ∧ Real.exp (-1277/65536 : ℝ) ≤ (49035157057/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980703141139/1000000000000 : ℝ) ≤ (radius 7 (8939/65536 : ℝ)) ∧ (radius 7 (8939/65536 : ℝ)) ≤ (49035157057/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8939/65536 : ℝ)) (980703141139/1000000000000 : ℝ) (49035157057/50000000000 : ℝ) (97751405307/500000000000 : ℝ) (9775140531/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8939/65536 : ℝ)) (980703141139/1000000000000 : ℝ) (49035157057/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8939/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980703141139/1000000000000 : ℝ) (49035157057/50000000000 : ℝ) (990351570569/1000000000000 : ℝ) (99035157057/100000000000 : ℝ) (495152284943/500000000000 : ℝ) (30947017809/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8939/65536 : ℝ)) 1 (990351570569/1000000000000 : ℝ) (99035157057/100000000000 : ℝ) (495152284943/500000000000 : ℝ) (30947017809/31250000000 : ℝ) (990328070227/1000000000000 : ℝ) (990328070229/1000000000000 : ℝ) (247582017487/250000000000 : ℝ) (990328069951/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8939/65536 : ℝ)) 2 (990328070227/1000000000000 : ℝ) (990328070229/1000000000000 : ℝ) (247582017487/250000000000 : ℝ) (990328069951/1000000000000 : ℝ) (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ) (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8939/65536 : ℝ)) 3 (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ) (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ) (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ) (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8939/65536 : ℝ)) 4 (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ) (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ) (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ) (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8939/65536 : ℝ)) 5 (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ) (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ) (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ) (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8939/65536 : ℝ)) 6 (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ) (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ) (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ) (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8939/65536 : ℝ)) 7 (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ) (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ) (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ) (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8939/65536 : ℝ))) (97751405307/500000000000 : ℝ) (9775140531/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8939/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97751405307/500000000000 : ℝ) (9775140531/50000000000 : ℝ) (597751405307/1000000000000 : ℝ) (59775140531/100000000000 : ℝ) (221078498849/500000000000 : ℝ) (221078498853/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8939/65536 : ℝ))) 1 (597751405307/1000000000000 : ℝ) (59775140531/100000000000 : ℝ) (221078498849/500000000000 : ℝ) (221078498853/500000000000 : ℝ) (259977100751/500000000000 : ℝ) (129988550377/250000000000 : ℝ) (514101125013/1000000000000 : ℝ) (25705056251/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8939/65536 : ℝ))) 2 (259977100751/500000000000 : ℝ) (129988550377/250000000000 : ℝ) (514101125013/1000000000000 : ℝ) (25705056251/50000000000 : ℝ) (517027663257/1000000000000 : ℝ) (16157114477/31250000000 : ℝ) (51701938063/100000000000 : ℝ) (517019380637/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8939/65536 : ℝ))) 3 (517027663257/1000000000000 : ℝ) (16157114477/31250000000 : ℝ) (51701938063/100000000000 : ℝ) (517019380637/1000000000000 : ℝ) (517023521943/1000000000000 : ℝ) (517023521951/1000000000000 : ℝ) (258511760963/500000000000 : ℝ) (258511760967/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8939/65536 : ℝ))) 4 (517023521943/1000000000000 : ℝ) (517023521951/1000000000000 : ℝ) (258511760963/500000000000 : ℝ) (258511760967/500000000000 : ℝ) (258511760967/500000000000 : ℝ) (517023521943/1000000000000 : ℝ) (258511760967/500000000000 : ℝ) (517023521943/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8939/65536 : ℝ))) 5 (258511760967/500000000000 : ℝ) (517023521943/1000000000000 : ℝ) (258511760967/500000000000 : ℝ) (517023521943/1000000000000 : ℝ) (258511760967/500000000000 : ℝ) (517023521943/1000000000000 : ℝ) (258511760967/500000000000 : ℝ) (517023521943/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8939/65536 : ℝ))) 6 (258511760967/500000000000 : ℝ) (517023521943/1000000000000 : ℝ) (258511760967/500000000000 : ℝ) (517023521943/1000000000000 : ℝ) (258511760967/500000000000 : ℝ) (517023521943/1000000000000 : ℝ) (258511760967/500000000000 : ℝ) (517023521943/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8939/65536 : ℝ))) 7 (258511760967/500000000000 : ℝ) (517023521943/1000000000000 : ℝ) (258511760967/500000000000 : ℝ) (517023521943/1000000000000 : ℝ) (258511760967/500000000000 : ℝ) (517023521943/1000000000000 : ℝ) (258511760967/500000000000 : ℝ) (517023521943/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8939/65536 : ℝ)) hmem 8 (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ) (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8939/65536 : ℝ))) hcmem 8 (258511760967/500000000000 : ℝ) (517023521943/1000000000000 : ℝ) (258511760967/500000000000 : ℝ) (517023521943/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8939/65536 : ℝ)) (990328070087/1000000000000 : ℝ) (99032807009/100000000000 : ℝ) (258511760967/500000000000 : ℝ) (517023521943/1000000000000 : ℝ) (51254394481/62500000000 : ℝ) (410035155857/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0328_exp_lower
  have heNumeric : (1009504812011/500000000000 : ℝ)/4 ≤ Real.exp (-5469498040587/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009504812011/500000000000 : ℝ)/4 ≤ Real.exp ((4469/32768 : ℝ)-(410035155857/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4469/32768 : ℝ) (8939/65536 : ℝ) (410035155857/500000000000 : ℝ) (1009504812011/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0329; no trusted numerical premise.
theorem cover7_leaf0329_exp_radius : (249391751963088433/250000000000000000 : ℝ) ≤ Real.exp ((-2235/114688 : ℝ)/8) ∧ Real.exp ((-2235/114688 : ℝ)/8) ≤ (997567007852353733/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2235/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0329_exp_lower : (229522258731084383/250000000000000000 : ℝ) ≤ Real.exp ((-10938995856597/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938995856597/16000000000000 : ℝ)/8) ≤ (918089034924337533/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938995856597/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0329_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019009652361/1000000000000 : ℝ) ≤ 4*Real.exp (8939/65536 : ℝ)*Real.exp (-mu (radius 7 (2235/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019009652361/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2235/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0329_exp_radius
  have hrNumeric : (490350501689/500000000000 : ℝ) ≤ Real.exp (-2235/114688 : ℝ) ∧ Real.exp (-2235/114688 : ℝ) ≤ (980701003379/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490350501689/500000000000 : ℝ) ≤ (radius 7 (2235/16384 : ℝ)) ∧ (radius 7 (2235/16384 : ℝ)) ≤ (980701003379/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2235/16384 : ℝ)) (490350501689/500000000000 : ℝ) (980701003379/1000000000000 : ℝ) (39102706797/200000000000 : ℝ) (195513533991/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2235/16384 : ℝ)) (490350501689/500000000000 : ℝ) (980701003379/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2235/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490350501689/500000000000 : ℝ) (980701003379/1000000000000 : ℝ) (990350501689/1000000000000 : ℝ) (99035050169/100000000000 : ℝ) (990303490541/1000000000000 : ℝ) (495151745271/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2235/16384 : ℝ)) 1 (990350501689/1000000000000 : ℝ) (99035050169/100000000000 : ℝ) (990303490541/1000000000000 : ℝ) (495151745271/500000000000 : ℝ) (198065399223/200000000000 : ℝ) (247581749029/250000000000 : ℝ) (247581748959/250000000000 : ℝ) (495163497919/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2235/16384 : ℝ)) 2 (198065399223/200000000000 : ℝ) (247581749029/250000000000 : ℝ) (247581748959/250000000000 : ℝ) (495163497919/500000000000 : ℝ) (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ) (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2235/16384 : ℝ)) 3 (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ) (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ) (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ) (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2235/16384 : ℝ)) 4 (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ) (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ) (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ) (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2235/16384 : ℝ)) 5 (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ) (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ) (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ) (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2235/16384 : ℝ)) 6 (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ) (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ) (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ) (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2235/16384 : ℝ)) 7 (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ) (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ) (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ) (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2235/16384 : ℝ))) (39102706797/200000000000 : ℝ) (195513533991/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2235/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39102706797/200000000000 : ℝ) (195513533991/1000000000000 : ℝ) (37359797937/62500000000 : ℝ) (149439191749/250000000000 : ℝ) (88433824747/200000000000 : ℝ) (442169123743/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2235/16384 : ℝ))) 1 (37359797937/62500000000 : ℝ) (149439191749/250000000000 : ℝ) (88433824747/200000000000 : ℝ) (442169123743/1000000000000 : ℝ) (519962945363/1000000000000 : ℝ) (51996294537/100000000000 : ℝ) (102822096043/200000000000 : ℝ) (257055240111/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2235/16384 : ℝ))) 2 (519962945363/1000000000000 : ℝ) (51996294537/100000000000 : ℝ) (102822096043/200000000000 : ℝ) (257055240111/500000000000 : ℝ) (517036712789/1000000000000 : ℝ) (129259178199/250000000000 : ℝ) (129257108009/250000000000 : ℝ) (129257108011/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2235/16384 : ℝ))) 3 (517036712789/1000000000000 : ℝ) (129259178199/250000000000 : ℝ) (129257108009/250000000000 : ℝ) (129257108011/250000000000 : ℝ) (129258143103/250000000000 : ℝ) (25851628621/50000000000 : ℝ) (103406514479/200000000000 : ℝ) (129258143101/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2235/16384 : ℝ))) 4 (129258143103/250000000000 : ℝ) (25851628621/50000000000 : ℝ) (103406514479/200000000000 : ℝ) (129258143101/250000000000 : ℝ) (517032572403/1000000000000 : ℝ) (129258143103/250000000000 : ℝ) (517032572403/1000000000000 : ℝ) (129258143103/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2235/16384 : ℝ))) 5 (517032572403/1000000000000 : ℝ) (129258143103/250000000000 : ℝ) (517032572403/1000000000000 : ℝ) (129258143103/250000000000 : ℝ) (517032572403/1000000000000 : ℝ) (129258143103/250000000000 : ℝ) (517032572403/1000000000000 : ℝ) (129258143103/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2235/16384 : ℝ))) 6 (517032572403/1000000000000 : ℝ) (129258143103/250000000000 : ℝ) (517032572403/1000000000000 : ℝ) (129258143103/250000000000 : ℝ) (517032572403/1000000000000 : ℝ) (129258143103/250000000000 : ℝ) (517032572403/1000000000000 : ℝ) (129258143103/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2235/16384 : ℝ))) 7 (517032572403/1000000000000 : ℝ) (129258143103/250000000000 : ℝ) (517032572403/1000000000000 : ℝ) (129258143103/250000000000 : ℝ) (517032572403/1000000000000 : ℝ) (129258143103/250000000000 : ℝ) (517032572403/1000000000000 : ℝ) (129258143103/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2235/16384 : ℝ)) hmem 8 (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ) (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2235/16384 : ℝ))) hcmem 8 (517032572403/1000000000000 : ℝ) (129258143103/250000000000 : ℝ) (517032572403/1000000000000 : ℝ) (129258143103/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2235/16384 : ℝ)) (39613079839/40000000000 : ℝ) (990326995977/1000000000000 : ℝ) (517032572403/1000000000000 : ℝ) (129258143103/250000000000 : ℝ) (16401711129/20000000000 : ℝ) (820085556467/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0329_exp_lower
  have heNumeric : (2019009652361/1000000000000 : ℝ)/4 ≤ Real.exp (-10938995856597/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019009652361/1000000000000 : ℝ)/4 ≤ Real.exp ((8939/65536 : ℝ)-(820085556467/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8939/65536 : ℝ) (2235/16384 : ℝ) (820085556467/1000000000000 : ℝ) (2019009652361/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0330; no trusted numerical premise.
theorem cover7_leaf0330_exp_radius : (997566736036952397/1000000000000000000 : ℝ) ≤ Real.exp ((-8941/458752 : ℝ)/8) ∧ Real.exp ((-8941/458752 : ℝ)/8) ≤ (498783368018476199/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8941/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0330_exp_lower : (183617807333168969/200000000000000000 : ℝ) ≤ Real.exp ((-2734748903449/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734748903449/4000000000000 : ℝ)/8) ≤ (459044518332922423/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734748903449/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0330_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019009682999/1000000000000 : ℝ) ≤ 4*Real.exp (2235/16384 : ℝ)*Real.exp (-mu (radius 7 (8941/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019009682999/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8941/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0330_exp_radius
  have hrNumeric : (490349432811/500000000000 : ℝ) ≤ Real.exp (-8941/458752 : ℝ) ∧ Real.exp (-8941/458752 : ℝ) ≤ (980698865623/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490349432811/500000000000 : ℝ) ≤ (radius 7 (8941/65536 : ℝ)) ∧ (radius 7 (8941/65536 : ℝ)) ≤ (980698865623/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8941/65536 : ℝ)) (490349432811/500000000000 : ℝ) (980698865623/1000000000000 : ℝ) (195524256719/1000000000000 : ℝ) (7820970269/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8941/65536 : ℝ)) (490349432811/500000000000 : ℝ) (980698865623/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8941/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490349432811/500000000000 : ℝ) (980698865623/1000000000000 : ℝ) (990349432811/1000000000000 : ℝ) (247587358203/250000000000 : ℝ) (247575602799/250000000000 : ℝ) (495151205599/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8941/65536 : ℝ)) 1 (990349432811/1000000000000 : ℝ) (247587358203/250000000000 : ℝ) (247575602799/250000000000 : ℝ) (495151205599/500000000000 : ℝ) (990325922003/1000000000000 : ℝ) (198065184401/200000000000 : ℝ) (247581480431/250000000000 : ℝ) (495162960863/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8941/65536 : ℝ)) 2 (990325922003/1000000000000 : ℝ) (198065184401/200000000000 : ℝ) (247581480431/250000000000 : ℝ) (495162960863/500000000000 : ℝ) (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ) (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8941/65536 : ℝ)) 3 (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ) (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ) (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ) (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8941/65536 : ℝ)) 4 (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ) (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ) (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ) (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8941/65536 : ℝ)) 5 (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ) (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ) (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ) (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8941/65536 : ℝ)) 6 (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ) (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ) (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ) (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8941/65536 : ℝ)) 7 (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ) (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ) (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ) (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8941/65536 : ℝ))) (195524256719/1000000000000 : ℝ) (7820970269/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8941/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195524256719/1000000000000 : ℝ) (7820970269/40000000000 : ℝ) (597762128359/1000000000000 : ℝ) (597762128363/1000000000000 : ℝ) (442181248719/1000000000000 : ℝ) (442181248727/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8941/65536 : ℝ))) 1 (597762128359/1000000000000 : ℝ) (597762128363/1000000000000 : ℝ) (442181248719/1000000000000 : ℝ) (442181248727/1000000000000 : ℝ) (519971688539/1000000000000 : ℝ) (103994337709/200000000000 : ℝ) (502070151/976562500 : ℝ) (64264979329/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8941/65536 : ℝ))) 2 (519971688539/1000000000000 : ℝ) (103994337709/200000000000 : ℝ) (502070151/976562500 : ℝ) (64264979329/125000000000 : ℝ) (517045761581/1000000000000 : ℝ) (517045761589/1000000000000 : ℝ) (517037482703/1000000000000 : ℝ) (517037482711/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8941/65536 : ℝ))) 3 (517045761581/1000000000000 : ℝ) (517045761589/1000000000000 : ℝ) (517037482703/1000000000000 : ℝ) (517037482711/1000000000000 : ℝ) (258520811071/500000000000 : ℝ) (10340832443/20000000000 : ℝ) (4136332977/8000000000 : ℝ) (258520811067/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8941/65536 : ℝ))) 4 (258520811071/500000000000 : ℝ) (10340832443/20000000000 : ℝ) (4136332977/8000000000 : ℝ) (258520811067/500000000000 : ℝ) (517041622133/1000000000000 : ℝ) (258520811071/500000000000 : ℝ) (517041622133/1000000000000 : ℝ) (258520811071/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8941/65536 : ℝ))) 5 (517041622133/1000000000000 : ℝ) (258520811071/500000000000 : ℝ) (517041622133/1000000000000 : ℝ) (258520811071/500000000000 : ℝ) (517041622133/1000000000000 : ℝ) (258520811071/500000000000 : ℝ) (517041622133/1000000000000 : ℝ) (258520811071/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8941/65536 : ℝ))) 6 (517041622133/1000000000000 : ℝ) (258520811071/500000000000 : ℝ) (517041622133/1000000000000 : ℝ) (258520811071/500000000000 : ℝ) (517041622133/1000000000000 : ℝ) (258520811071/500000000000 : ℝ) (517041622133/1000000000000 : ℝ) (258520811071/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8941/65536 : ℝ))) 7 (517041622133/1000000000000 : ℝ) (258520811071/500000000000 : ℝ) (517041622133/1000000000000 : ℝ) (258520811071/500000000000 : ℝ) (517041622133/1000000000000 : ℝ) (258520811071/500000000000 : ℝ) (517041622133/1000000000000 : ℝ) (258520811071/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8941/65536 : ℝ)) hmem 8 (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ) (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8941/65536 : ℝ))) hcmem 8 (517041622133/1000000000000 : ℝ) (258520811071/500000000000 : ℝ) (517041622133/1000000000000 : ℝ) (258520811071/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8941/65536 : ℝ)) (990325921863/1000000000000 : ℝ) (495162960933/500000000000 : ℝ) (517041622133/1000000000000 : ℝ) (258520811071/500000000000 : ℝ) (12814075001/15625000000 : ℝ) (820100800081/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0330_exp_lower
  have heNumeric : (2019009682999/1000000000000 : ℝ)/4 ≤ Real.exp (-2734748903449/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019009682999/1000000000000 : ℝ)/4 ≤ Real.exp ((2235/16384 : ℝ)-(820100800081/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2235/16384 : ℝ) (8941/65536 : ℝ) (820100800081/1000000000000 : ℝ) (2019009682999/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0331; no trusted numerical premise.
theorem cover7_leaf0331_exp_radius : (498783232110812563/500000000000000000 : ℝ) ≤ Real.exp ((-4471/229376 : ℝ)/8) ∧ Real.exp ((-4471/229376 : ℝ)/8) ≤ (997566464221625127/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4471/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0331_exp_lower : (918089038537491281/1000000000000000000 : ℝ) ≤ Real.exp ((-10938995352851/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938995352851/16000000000000 : ℝ)/8) ≤ (459044519268745641/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938995352851/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0331_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019009715927/1000000000000 : ℝ) ≤ 4*Real.exp (8941/65536 : ℝ)*Real.exp (-mu (radius 7 (4471/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019009715927/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4471/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0331_exp_radius
  have hrNumeric : (98069672787/100000000000 : ℝ) ≤ Real.exp (-4471/229376 : ℝ) ∧ Real.exp (-4471/229376 : ℝ) ≤ (980696727871/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98069672787/100000000000 : ℝ) ≤ (radius 7 (4471/32768 : ℝ)) ∧ (radius 7 (4471/32768 : ℝ)) ≤ (980696727871/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4471/32768 : ℝ)) (98069672787/100000000000 : ℝ) (980696727871/1000000000000 : ℝ) (97767489411/500000000000 : ℝ) (48883744707/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4471/32768 : ℝ)) (98069672787/100000000000 : ℝ) (980696727871/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4471/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98069672787/100000000000 : ℝ) (980696727871/1000000000000 : ℝ) (198069672787/200000000000 : ℝ) (30948386373/31250000000 : ℝ) (990301331853/1000000000000 : ℝ) (495150665927/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4471/32768 : ℝ)) 1 (198069672787/200000000000 : ℝ) (30948386373/31250000000 : ℝ) (990301331853/1000000000000 : ℝ) (495150665927/500000000000 : ℝ) (495162423947/500000000000 : ℝ) (198064969579/200000000000 : ℝ) (495162423807/500000000000 : ℝ) (967114109/976562500 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4471/32768 : ℝ)) 2 (495162423947/500000000000 : ℝ) (198064969579/200000000000 : ℝ) (495162423807/500000000000 : ℝ) (967114109/976562500 : ℝ) (495162423877/500000000000 : ℝ) (247581211939/250000000000 : ℝ) (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4471/32768 : ℝ)) 3 (495162423877/500000000000 : ℝ) (247581211939/250000000000 : ℝ) (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ) (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ) (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4471/32768 : ℝ)) 4 (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ) (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ) (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ) (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4471/32768 : ℝ)) 5 (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ) (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ) (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ) (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4471/32768 : ℝ)) 6 (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ) (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ) (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ) (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4471/32768 : ℝ)) 7 (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ) (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ) (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ) (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4471/32768 : ℝ))) (97767489411/500000000000 : ℝ) (48883744707/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4471/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97767489411/500000000000 : ℝ) (48883744707/250000000000 : ℝ) (597767489411/1000000000000 : ℝ) (298883744707/500000000000 : ℝ) (442193372657/1000000000000 : ℝ) (88438674533/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4471/32768 : ℝ))) 1 (597767489411/1000000000000 : ℝ) (298883744707/500000000000 : ℝ) (442193372657/1000000000000 : ℝ) (88438674533/200000000000 : ℝ) (259990215517/500000000000 : ℝ) (1624938847/3125000000 : ℝ) (257064594123/500000000000 : ℝ) (514129188253/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4471/32768 : ℝ))) 2 (259990215517/500000000000 : ℝ) (1624938847/3125000000 : ℝ) (257064594123/500000000000 : ℝ) (514129188253/1000000000000 : ℝ) (12926370241/25000000000 : ℝ) (517054809647/1000000000000 : ℝ) (129261633159/250000000000 : ℝ) (517046532643/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4471/32768 : ℝ))) 3 (12926370241/25000000000 : ℝ) (517054809647/1000000000000 : ℝ) (129261633159/250000000000 : ℝ) (517046532643/1000000000000 : ℝ) (258525335569/500000000000 : ℝ) (103410134229/200000000000 : ℝ) (517050671121/1000000000000 : ℝ) (517050671129/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4471/32768 : ℝ))) 4 (258525335569/500000000000 : ℝ) (103410134229/200000000000 : ℝ) (517050671121/1000000000000 : ℝ) (517050671129/1000000000000 : ℝ) (517050671129/1000000000000 : ℝ) (517050671137/1000000000000 : ℝ) (517050671129/1000000000000 : ℝ) (517050671137/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4471/32768 : ℝ))) 5 (517050671129/1000000000000 : ℝ) (517050671137/1000000000000 : ℝ) (517050671129/1000000000000 : ℝ) (517050671137/1000000000000 : ℝ) (517050671129/1000000000000 : ℝ) (517050671137/1000000000000 : ℝ) (517050671129/1000000000000 : ℝ) (517050671137/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4471/32768 : ℝ))) 6 (517050671129/1000000000000 : ℝ) (517050671137/1000000000000 : ℝ) (517050671129/1000000000000 : ℝ) (517050671137/1000000000000 : ℝ) (517050671129/1000000000000 : ℝ) (517050671137/1000000000000 : ℝ) (517050671129/1000000000000 : ℝ) (517050671137/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4471/32768 : ℝ))) 7 (517050671129/1000000000000 : ℝ) (517050671137/1000000000000 : ℝ) (517050671129/1000000000000 : ℝ) (517050671137/1000000000000 : ℝ) (517050671129/1000000000000 : ℝ) (517050671137/1000000000000 : ℝ) (517050671129/1000000000000 : ℝ) (517050671137/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4471/32768 : ℝ)) hmem 8 (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ) (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4471/32768 : ℝ))) hcmem 8 (517050671129/1000000000000 : ℝ) (517050671137/1000000000000 : ℝ) (517050671129/1000000000000 : ℝ) (517050671137/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4471/32768 : ℝ)) (990324847753/1000000000000 : ℝ) (247581211939/250000000000 : ℝ) (517050671129/1000000000000 : ℝ) (517050671137/1000000000000 : ℝ) (164023208509/200000000000 : ℝ) (820116042561/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0331_exp_lower
  have heNumeric : (2019009715927/1000000000000 : ℝ)/4 ≤ Real.exp (-10938995352851/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019009715927/1000000000000 : ℝ)/4 ≤ Real.exp ((8941/65536 : ℝ)-(820116042561/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8941/65536 : ℝ) (4471/32768 : ℝ) (820116042561/1000000000000 : ℝ) (2019009715927/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0332; no trusted numerical premise.
theorem cover7_leaf0332_exp_radius : (997566192406371919/1000000000000000000 : ℝ) ≤ Real.exp ((-8943/458752 : ℝ)/8) ∧ Real.exp ((-8943/458752 : ℝ)/8) ≤ (12469577405079649/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8943/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0332_exp_lower : (918089040539850649/1000000000000000000 : ℝ) ≤ Real.exp ((-5469497536841/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469497536841/8000000000000 : ℝ)/8) ≤ (18361780810797013/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469497536841/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0332_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403801950231/200000000000 : ℝ) ≤ 4*Real.exp (4471/32768 : ℝ)*Real.exp (-mu (radius 7 (8943/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (403801950231/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8943/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0332_exp_radius
  have hrNumeric : (980694590123/1000000000000 : ℝ) ≤ Real.exp (-8943/458752 : ℝ) ∧ Real.exp (-8943/458752 : ℝ) ≤ (245173647531/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980694590123/1000000000000 : ℝ) ≤ (radius 7 (8943/65536 : ℝ)) ∧ (radius 7 (8943/65536 : ℝ)) ≤ (245173647531/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8943/65536 : ℝ)) (980694590123/1000000000000 : ℝ) (245173647531/250000000000 : ℝ) (195545700289/1000000000000 : ℝ) (39109140059/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8943/65536 : ℝ)) (980694590123/1000000000000 : ℝ) (245173647531/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8943/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980694590123/1000000000000 : ℝ) (245173647531/250000000000 : ℝ) (990347295061/1000000000000 : ℝ) (495173647531/500000000000 : ℝ) (99030025251/100000000000 : ℝ) (30946882891/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8943/65536 : ℝ)) 1 (990347295061/1000000000000 : ℝ) (495173647531/500000000000 : ℝ) (99030025251/100000000000 : ℝ) (30946882891/31250000000 : ℝ) (198064754757/200000000000 : ℝ) (990323773787/1000000000000 : ℝ) (495161886753/500000000000 : ℝ) (247580943377/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8943/65536 : ℝ)) 2 (198064754757/200000000000 : ℝ) (990323773787/1000000000000 : ℝ) (495161886753/500000000000 : ℝ) (247580943377/250000000000 : ℝ) (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ) (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8943/65536 : ℝ)) 3 (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ) (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ) (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ) (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8943/65536 : ℝ)) 4 (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ) (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ) (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ) (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8943/65536 : ℝ)) 5 (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ) (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ) (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ) (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8943/65536 : ℝ)) 6 (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ) (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ) (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ) (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8943/65536 : ℝ)) 7 (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ) (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ) (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ) (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8943/65536 : ℝ))) (195545700289/1000000000000 : ℝ) (39109140059/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8943/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195545700289/1000000000000 : ℝ) (39109140059/200000000000 : ℝ) (18680401567/31250000000 : ℝ) (149443212537/250000000000 : ℝ) (442205495543/1000000000000 : ℝ) (442205495551/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8943/65536 : ℝ))) 1 (18680401567/31250000000 : ℝ) (149443212537/250000000000 : ℝ) (442205495543/1000000000000 : ℝ) (442205495551/1000000000000 : ℝ) (519989172843/1000000000000 : ℝ) (10399783457/20000000000 : ℝ) (128534635269/250000000000 : ℝ) (514138541083/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8943/65536 : ℝ))) 2 (519989172843/1000000000000 : ℝ) (10399783457/20000000000 : ℝ) (128534635269/250000000000 : ℝ) (514138541083/1000000000000 : ℝ) (517063856959/1000000000000 : ℝ) (517063856967/1000000000000 : ℝ) (517055581829/1000000000000 : ℝ) (517055581837/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8943/65536 : ℝ))) 3 (517063856959/1000000000000 : ℝ) (517063856967/1000000000000 : ℝ) (517055581829/1000000000000 : ℝ) (517055581837/1000000000000 : ℝ) (258529859697/500000000000 : ℝ) (258529859701/500000000000 : ℝ) (517059719377/1000000000000 : ℝ) (258529859693/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8943/65536 : ℝ))) 4 (258529859697/500000000000 : ℝ) (258529859701/500000000000 : ℝ) (517059719377/1000000000000 : ℝ) (258529859693/500000000000 : ℝ) (103411943877/200000000000 : ℝ) (258529859697/500000000000 : ℝ) (103411943877/200000000000 : ℝ) (258529859697/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8943/65536 : ℝ))) 5 (103411943877/200000000000 : ℝ) (258529859697/500000000000 : ℝ) (103411943877/200000000000 : ℝ) (258529859697/500000000000 : ℝ) (103411943877/200000000000 : ℝ) (258529859697/500000000000 : ℝ) (103411943877/200000000000 : ℝ) (258529859697/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8943/65536 : ℝ))) 6 (103411943877/200000000000 : ℝ) (258529859697/500000000000 : ℝ) (103411943877/200000000000 : ℝ) (258529859697/500000000000 : ℝ) (103411943877/200000000000 : ℝ) (258529859697/500000000000 : ℝ) (103411943877/200000000000 : ℝ) (258529859697/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8943/65536 : ℝ))) 7 (103411943877/200000000000 : ℝ) (258529859697/500000000000 : ℝ) (103411943877/200000000000 : ℝ) (258529859697/500000000000 : ℝ) (103411943877/200000000000 : ℝ) (258529859697/500000000000 : ℝ) (103411943877/200000000000 : ℝ) (258529859697/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8943/65536 : ℝ)) hmem 8 (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ) (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8943/65536 : ℝ))) hcmem 8 (103411943877/200000000000 : ℝ) (258529859697/500000000000 : ℝ) (103411943877/200000000000 : ℝ) (258529859697/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8943/65536 : ℝ)) (198064754729/200000000000 : ℝ) (61895235853/62500000000 : ℝ) (103411943877/200000000000 : ℝ) (258529859697/500000000000 : ℝ) (205032820971/250000000000 : ℝ) (410065641951/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0332_exp_lower
  have heNumeric : (403801950231/200000000000 : ℝ)/4 ≤ Real.exp (-5469497536841/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403801950231/200000000000 : ℝ)/4 ≤ Real.exp ((4471/32768 : ℝ)-(410065641951/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4471/32768 : ℝ) (8943/65536 : ℝ) (410065641951/500000000000 : ℝ) (403801950231/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0333; no trusted numerical premise.
theorem cover7_leaf0333_exp_radius : (124695740073899097/125000000000000000 : ℝ) ≤ Real.exp ((-559/28672 : ℝ)/8) ∧ Real.exp ((-559/28672 : ℝ)/8) ≤ (997565920591192777/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-559/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0333_exp_lower : (918089042673152471/1000000000000000000 : ℝ) ≤ Real.exp ((-10938994776257/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938994776257/16000000000000 : ℝ)/8) ≤ (114761130334144059/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938994776257/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0333_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019009788687/1000000000000 : ℝ) ≤ 4*Real.exp (8943/65536 : ℝ)*Real.exp (-mu (radius 7 (559/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019009788687/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (559/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0333_exp_radius
  have hrNumeric : (980692452381/1000000000000 : ℝ) ≤ Real.exp (-559/28672 : ℝ) ∧ Real.exp (-559/28672 : ℝ) ≤ (490346226191/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980692452381/1000000000000 : ℝ) ≤ (radius 7 (559/4096 : ℝ)) ∧ (radius 7 (559/4096 : ℝ)) ≤ (490346226191/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (559/4096 : ℝ)) (980692452381/1000000000000 : ℝ) (490346226191/500000000000 : ℝ) (195556421119/1000000000000 : ℝ) (1564451369/8000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (559/4096 : ℝ)) (980692452381/1000000000000 : ℝ) (490346226191/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (559/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980692452381/1000000000000 : ℝ) (490346226191/500000000000 : ℝ) (99034622619/100000000000 : ℝ) (990346226191/1000000000000 : ℝ) (990299173169/1000000000000 : ℝ) (990299173171/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (559/4096 : ℝ)) 1 (99034622619/100000000000 : ℝ) (990346226191/1000000000000 : ℝ) (990299173169/1000000000000 : ℝ) (990299173171/1000000000000 : ℝ) (990322699679/1000000000000 : ℝ) (990322699681/1000000000000 : ℝ) (4951613497/5000000000 : ℝ) (495161349701/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (559/4096 : ℝ)) 2 (990322699679/1000000000000 : ℝ) (990322699681/1000000000000 : ℝ) (4951613497/5000000000 : ℝ) (495161349701/500000000000 : ℝ) (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ) (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (559/4096 : ℝ)) 3 (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ) (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ) (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ) (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (559/4096 : ℝ)) 4 (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ) (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ) (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ) (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (559/4096 : ℝ)) 5 (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ) (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ) (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ) (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (559/4096 : ℝ)) 6 (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ) (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ) (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ) (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (559/4096 : ℝ)) 7 (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ) (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ) (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ) (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (559/4096 : ℝ))) (195556421119/1000000000000 : ℝ) (1564451369/8000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (559/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195556421119/1000000000000 : ℝ) (1564451369/8000000000 : ℝ) (597778210559/1000000000000 : ℝ) (597778210563/1000000000000 : ℝ) (442217617377/1000000000000 : ℝ) (88443523477/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (559/4096 : ℝ))) 1 (597778210559/1000000000000 : ℝ) (597778210563/1000000000000 : ℝ) (442217617377/1000000000000 : ℝ) (88443523477/200000000000 : ℝ) (32499869623/62500000000 : ℝ) (259998956987/500000000000 : ℝ) (514147893113/1000000000000 : ℝ) (514147893121/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (559/4096 : ℝ))) 2 (32499869623/62500000000 : ℝ) (259998956987/500000000000 : ℝ) (514147893113/1000000000000 : ℝ) (514147893121/1000000000000 : ℝ) (25853645177/50000000000 : ℝ) (129268225887/250000000000 : ℝ) (517064630283/1000000000000 : ℝ) (517064630291/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (559/4096 : ℝ))) 3 (25853645177/50000000000 : ℝ) (129268225887/250000000000 : ℝ) (517064630283/1000000000000 : ℝ) (517064630291/1000000000000 : ℝ) (517068766911/1000000000000 : ℝ) (12926719173/25000000000 : ℝ) (258534383447/500000000000 : ℝ) (517068766903/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (559/4096 : ℝ))) 4 (517068766911/1000000000000 : ℝ) (12926719173/25000000000 : ℝ) (258534383447/500000000000 : ℝ) (517068766903/1000000000000 : ℝ) (258534383451/500000000000 : ℝ) (8079199483/15625000000 : ℝ) (258534383451/500000000000 : ℝ) (8079199483/15625000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (559/4096 : ℝ))) 5 (258534383451/500000000000 : ℝ) (8079199483/15625000000 : ℝ) (258534383451/500000000000 : ℝ) (8079199483/15625000000 : ℝ) (258534383451/500000000000 : ℝ) (8079199483/15625000000 : ℝ) (258534383451/500000000000 : ℝ) (8079199483/15625000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (559/4096 : ℝ))) 6 (258534383451/500000000000 : ℝ) (8079199483/15625000000 : ℝ) (258534383451/500000000000 : ℝ) (8079199483/15625000000 : ℝ) (258534383451/500000000000 : ℝ) (8079199483/15625000000 : ℝ) (258534383451/500000000000 : ℝ) (8079199483/15625000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (559/4096 : ℝ))) 7 (258534383451/500000000000 : ℝ) (8079199483/15625000000 : ℝ) (258534383451/500000000000 : ℝ) (8079199483/15625000000 : ℝ) (258534383451/500000000000 : ℝ) (8079199483/15625000000 : ℝ) (258534383451/500000000000 : ℝ) (8079199483/15625000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (559/4096 : ℝ)) hmem 8 (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ) (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (559/4096 : ℝ))) hcmem 8 (258534383451/500000000000 : ℝ) (8079199483/15625000000 : ℝ) (258534383451/500000000000 : ℝ) (8079199483/15625000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (559/4096 : ℝ)) (990322699539/1000000000000 : ℝ) (495161349771/500000000000 : ℝ) (258534383451/500000000000 : ℝ) (8079199483/15625000000 : ℝ) (820146524083/1000000000000 : ℝ) (410073262051/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0333_exp_lower
  have heNumeric : (2019009788687/1000000000000 : ℝ)/4 ≤ Real.exp (-10938994776257/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019009788687/1000000000000 : ℝ)/4 ≤ Real.exp ((8943/65536 : ℝ)-(410073262051/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8943/65536 : ℝ) (559/4096 : ℝ) (410073262051/500000000000 : ℝ) (2019009788687/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0334; no trusted numerical premise.
theorem cover7_leaf0334_exp_radius : (62347853048505481/62500000000000000 : ℝ) ≤ Real.exp ((-8945/458752 : ℝ)/8) ∧ Real.exp ((-8945/458752 : ℝ)/8) ≤ (997565648776087697/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8945/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0334_exp_lower : (918089044936708181/1000000000000000000 : ℝ) ≤ Real.exp ((-5341305889/7812500000 : ℝ)/8) ∧ Real.exp ((-5341305889/7812500000 : ℝ)/8) ≤ (459044522468354091/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5341305889/7812500000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0334_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201900982851/100000000000 : ℝ) ≤ 4*Real.exp (559/4096 : ℝ)*Real.exp (-mu (radius 7 (8945/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (201900982851/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8945/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0334_exp_radius
  have hrNumeric : (980690314643/1000000000000 : ℝ) ≤ Real.exp (-8945/458752 : ℝ) ∧ Real.exp (-8945/458752 : ℝ) ≤ (245172578661/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980690314643/1000000000000 : ℝ) ≤ (radius 7 (8945/65536 : ℝ)) ∧ (radius 7 (8945/65536 : ℝ)) ≤ (245172578661/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8945/65536 : ℝ)) (980690314643/1000000000000 : ℝ) (245172578661/250000000000 : ℝ) (97783570659/500000000000 : ℝ) (48891785331/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8945/65536 : ℝ)) (980690314643/1000000000000 : ℝ) (245172578661/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8945/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980690314643/1000000000000 : ℝ) (245172578661/250000000000 : ℝ) (990345157321/1000000000000 : ℝ) (495172578661/500000000000 : ℝ) (990298093829/1000000000000 : ℝ) (990298093831/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8945/65536 : ℝ)) 1 (990345157321/1000000000000 : ℝ) (495172578661/500000000000 : ℝ) (990298093829/1000000000000 : ℝ) (990298093831/1000000000000 : ℝ) (39612865023/40000000000 : ℝ) (990321625577/1000000000000 : ℝ) (198064325059/200000000000 : ℝ) (990321625297/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8945/65536 : ℝ)) 2 (39612865023/40000000000 : ℝ) (990321625577/1000000000000 : ℝ) (198064325059/200000000000 : ℝ) (990321625297/1000000000000 : ℝ) (198064325087/200000000000 : ℝ) (990321625437/1000000000000 : ℝ) (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8945/65536 : ℝ)) 3 (198064325087/200000000000 : ℝ) (990321625437/1000000000000 : ℝ) (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ) (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ) (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8945/65536 : ℝ)) 4 (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ) (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ) (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ) (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8945/65536 : ℝ)) 5 (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ) (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ) (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ) (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8945/65536 : ℝ)) 6 (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ) (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ) (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ) (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8945/65536 : ℝ)) 7 (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ) (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ) (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ) (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8945/65536 : ℝ))) (97783570659/500000000000 : ℝ) (48891785331/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8945/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97783570659/500000000000 : ℝ) (48891785331/250000000000 : ℝ) (597783570659/1000000000000 : ℝ) (298891785331/500000000000 : ℝ) (88445947633/200000000000 : ℝ) (442229738173/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8945/65536 : ℝ))) 1 (597783570659/1000000000000 : ℝ) (298891785331/500000000000 : ℝ) (88445947633/200000000000 : ℝ) (442229738173/1000000000000 : ℝ) (130001663603/250000000000 : ℝ) (260003327209/500000000000 : ℝ) (514157244363/1000000000000 : ℝ) (51415724437/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8945/65536 : ℝ))) 2 (130001663603/250000000000 : ℝ) (260003327209/500000000000 : ℝ) (514157244363/1000000000000 : ℝ) (51415724437/100000000000 : ℝ) (517081949387/1000000000000 : ℝ) (258540974697/500000000000 : ℝ) (258536839001/500000000000 : ℝ) (517073678009/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8945/65536 : ℝ))) 3 (517081949387/1000000000000 : ℝ) (258540974697/500000000000 : ℝ) (258536839001/500000000000 : ℝ) (517073678009/1000000000000 : ℝ) (258538906847/500000000000 : ℝ) (258538906851/500000000000 : ℝ) (517077813677/1000000000000 : ℝ) (103415562737/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8945/65536 : ℝ))) 4 (258538906847/500000000000 : ℝ) (258538906851/500000000000 : ℝ) (517077813677/1000000000000 : ℝ) (103415562737/200000000000 : ℝ) (103415562737/200000000000 : ℝ) (258538906847/500000000000 : ℝ) (103415562737/200000000000 : ℝ) (258538906847/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8945/65536 : ℝ))) 5 (103415562737/200000000000 : ℝ) (258538906847/500000000000 : ℝ) (103415562737/200000000000 : ℝ) (258538906847/500000000000 : ℝ) (103415562737/200000000000 : ℝ) (258538906847/500000000000 : ℝ) (103415562737/200000000000 : ℝ) (258538906847/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8945/65536 : ℝ))) 6 (103415562737/200000000000 : ℝ) (258538906847/500000000000 : ℝ) (103415562737/200000000000 : ℝ) (258538906847/500000000000 : ℝ) (103415562737/200000000000 : ℝ) (258538906847/500000000000 : ℝ) (103415562737/200000000000 : ℝ) (258538906847/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8945/65536 : ℝ))) 7 (103415562737/200000000000 : ℝ) (258538906847/500000000000 : ℝ) (103415562737/200000000000 : ℝ) (258538906847/500000000000 : ℝ) (103415562737/200000000000 : ℝ) (258538906847/500000000000 : ℝ) (103415562737/200000000000 : ℝ) (258538906847/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8945/65536 : ℝ)) hmem 8 (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ) (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8945/65536 : ℝ))) hcmem 8 (103415562737/200000000000 : ℝ) (258538906847/500000000000 : ℝ) (103415562737/200000000000 : ℝ) (258538906847/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8945/65536 : ℝ)) (495160812717/500000000000 : ℝ) (990321625437/1000000000000 : ℝ) (103415562737/200000000000 : ℝ) (258538906847/500000000000 : ℝ) (820161763149/1000000000000 : ℝ) (820161763167/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0334_exp_lower
  have heNumeric : (201900982851/100000000000 : ℝ)/4 ≤ Real.exp (-5341305889/7812500000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201900982851/100000000000 : ℝ)/4 ≤ Real.exp ((559/4096 : ℝ)-(820161763167/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (559/4096 : ℝ) (8945/65536 : ℝ) (820161763167/1000000000000 : ℝ) (201900982851/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0335; no trusted numerical premise.
theorem cover7_leaf0335_exp_radius : (997565376961056681/1000000000000000000 : ℝ) ≤ Real.exp ((-639/32768 : ℝ)/8) ∧ Real.exp ((-639/32768 : ℝ)/8) ≤ (498782688480528341/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-639/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0335_exp_lower : (36723561893239073/40000000000000000 : ℝ) ≤ Real.exp ((-10938994126863/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938994126863/16000000000000 : ℝ)/8) ≤ (459044523665488413/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938994126863/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0335_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252376233829/125000000000 : ℝ) ≤ 4*Real.exp (8945/65536 : ℝ)*Real.exp (-mu (radius 7 (4473/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (252376233829/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4473/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0335_exp_radius
  have hrNumeric : (98068817691/100000000000 : ℝ) ≤ Real.exp (-639/32768 : ℝ) ∧ Real.exp (-639/32768 : ℝ) ≤ (980688176911/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98068817691/100000000000 : ℝ) ≤ (radius 7 (4473/32768 : ℝ)) ∧ (radius 7 (4473/32768 : ℝ)) ≤ (980688176911/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4473/32768 : ℝ)) (98068817691/100000000000 : ℝ) (980688176911/1000000000000 : ℝ) (195577860881/1000000000000 : ℝ) (195577860887/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4473/32768 : ℝ)) (98068817691/100000000000 : ℝ) (980688176911/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4473/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98068817691/100000000000 : ℝ) (980688176911/1000000000000 : ℝ) (198068817691/200000000000 : ℝ) (123793011057/125000000000 : ℝ) (990297014491/1000000000000 : ℝ) (247574253623/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4473/32768 : ℝ)) 1 (198068817691/200000000000 : ℝ) (123793011057/125000000000 : ℝ) (990297014491/1000000000000 : ℝ) (247574253623/250000000000 : ℝ) (990320551473/1000000000000 : ℝ) (495160275737/500000000000 : ℝ) (990320551193/1000000000000 : ℝ) (198064110239/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4473/32768 : ℝ)) 2 (990320551473/1000000000000 : ℝ) (495160275737/500000000000 : ℝ) (990320551193/1000000000000 : ℝ) (198064110239/200000000000 : ℝ) (990320551333/1000000000000 : ℝ) (198064110267/200000000000 : ℝ) (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4473/32768 : ℝ)) 3 (990320551333/1000000000000 : ℝ) (198064110267/200000000000 : ℝ) (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ) (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ) (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4473/32768 : ℝ)) 4 (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ) (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ) (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ) (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4473/32768 : ℝ)) 5 (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ) (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ) (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ) (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4473/32768 : ℝ)) 6 (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ) (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ) (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ) (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4473/32768 : ℝ)) 7 (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ) (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ) (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ) (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4473/32768 : ℝ))) (195577860881/1000000000000 : ℝ) (195577860887/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4473/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195577860881/1000000000000 : ℝ) (195577860887/1000000000000 : ℝ) (14944723261/25000000000 : ℝ) (149447232611/250000000000 : ℝ) (221120928951/500000000000 : ℝ) (44224185791/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4473/32768 : ℝ))) 1 (14944723261/25000000000 : ℝ) (149447232611/250000000000 : ℝ) (221120928951/500000000000 : ℝ) (44224185791/100000000000 : ℝ) (520015394171/1000000000000 : ℝ) (520015394177/1000000000000 : ℝ) (257083297411/500000000000 : ℝ) (514166594829/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4473/32768 : ℝ))) 2 (520015394171/1000000000000 : ℝ) (520015394177/1000000000000 : ℝ) (257083297411/500000000000 : ℝ) (514166594829/1000000000000 : ℝ) (8079546789/15625000000 : ℝ) (517090994503/1000000000000 : ℝ) (517082724983/1000000000000 : ℝ) (51708272499/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4473/32768 : ℝ))) 3 (8079546789/15625000000 : ℝ) (517090994503/1000000000000 : ℝ) (517082724983/1000000000000 : ℝ) (51708272499/100000000000 : ℝ) (517086859739/1000000000000 : ℝ) (517086859747/1000000000000 : ℝ) (258543429861/500000000000 : ℝ) (51708685973/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4473/32768 : ℝ))) 4 (517086859739/1000000000000 : ℝ) (517086859747/1000000000000 : ℝ) (258543429861/500000000000 : ℝ) (51708685973/100000000000 : ℝ) (51708685973/100000000000 : ℝ) (517086859739/1000000000000 : ℝ) (51708685973/100000000000 : ℝ) (517086859739/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4473/32768 : ℝ))) 5 (51708685973/100000000000 : ℝ) (517086859739/1000000000000 : ℝ) (51708685973/100000000000 : ℝ) (517086859739/1000000000000 : ℝ) (51708685973/100000000000 : ℝ) (517086859739/1000000000000 : ℝ) (51708685973/100000000000 : ℝ) (517086859739/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4473/32768 : ℝ))) 6 (51708685973/100000000000 : ℝ) (517086859739/1000000000000 : ℝ) (51708685973/100000000000 : ℝ) (517086859739/1000000000000 : ℝ) (51708685973/100000000000 : ℝ) (517086859739/1000000000000 : ℝ) (51708685973/100000000000 : ℝ) (517086859739/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4473/32768 : ℝ))) 7 (51708685973/100000000000 : ℝ) (517086859739/1000000000000 : ℝ) (51708685973/100000000000 : ℝ) (517086859739/1000000000000 : ℝ) (51708685973/100000000000 : ℝ) (517086859739/1000000000000 : ℝ) (51708685973/100000000000 : ℝ) (517086859739/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4473/32768 : ℝ)) hmem 8 (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ) (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4473/32768 : ℝ))) hcmem 8 (51708685973/100000000000 : ℝ) (517086859739/1000000000000 : ℝ) (51708685973/100000000000 : ℝ) (517086859739/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4473/32768 : ℝ)) (247580137833/250000000000 : ℝ) (198064110267/200000000000 : ℝ) (51708685973/100000000000 : ℝ) (517086859739/1000000000000 : ℝ) (32807080043/40000000000 : ℝ) (820177001093/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0335_exp_lower
  have heNumeric : (252376233829/125000000000 : ℝ)/4 ≤ Real.exp (-10938994126863/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252376233829/125000000000 : ℝ)/4 ≤ Real.exp ((8945/65536 : ℝ)-(820177001093/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8945/65536 : ℝ) (4473/32768 : ℝ) (820177001093/1000000000000 : ℝ) (252376233829/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0336; no trusted numerical premise.
theorem cover7_leaf0336_exp_radius : (62347819071631233/62500000000000000 : ℝ) ≤ Real.exp ((-8947/458752 : ℝ)/8) ∧ Real.exp ((-8947/458752 : ℝ)/8) ≤ (997565105146099729/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8947/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0336_exp_lower : (459044524928093963/500000000000000000 : ℝ) ≤ Real.exp ((-5469496887399/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469496887399/8000000000000 : ℝ)/8) ≤ (918089049856187927/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469496887399/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0336_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019009915059/1000000000000 : ℝ) ≤ 4*Real.exp (4473/32768 : ℝ)*Real.exp (-mu (radius 7 (8947/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019009915059/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8947/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0336_exp_radius
  have hrNumeric : (490343019591/500000000000 : ℝ) ≤ Real.exp (-8947/458752 : ℝ) ∧ Real.exp (-8947/458752 : ℝ) ≤ (980686039183/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490343019591/500000000000 : ℝ) ≤ (radius 7 (8947/65536 : ℝ)) ∧ (radius 7 (8947/65536 : ℝ)) ≤ (980686039183/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8947/65536 : ℝ)) (490343019591/500000000000 : ℝ) (980686039183/1000000000000 : ℝ) (6112143119/31250000000 : ℝ) (97794289907/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8947/65536 : ℝ)) (490343019591/500000000000 : ℝ) (980686039183/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8947/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490343019591/500000000000 : ℝ) (980686039183/1000000000000 : ℝ) (990343019591/1000000000000 : ℝ) (123792877449/125000000000 : ℝ) (990295935153/1000000000000 : ℝ) (198059187031/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8947/65536 : ℝ)) 1 (990343019591/1000000000000 : ℝ) (123792877449/125000000000 : ℝ) (990295935153/1000000000000 : ℝ) (198059187031/200000000000 : ℝ) (247579869343/250000000000 : ℝ) (495159738687/500000000000 : ℝ) (247579869273/250000000000 : ℝ) (495159738547/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8947/65536 : ℝ)) 2 (247579869343/250000000000 : ℝ) (495159738687/500000000000 : ℝ) (247579869273/250000000000 : ℝ) (495159738547/500000000000 : ℝ) (61894967327/62500000000 : ℝ) (495159738617/500000000000 : ℝ) (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8947/65536 : ℝ)) 3 (61894967327/62500000000 : ℝ) (495159738617/500000000000 : ℝ) (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ) (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ) (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8947/65536 : ℝ)) 4 (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ) (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ) (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ) (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8947/65536 : ℝ)) 5 (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ) (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ) (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ) (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8947/65536 : ℝ)) 6 (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ) (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ) (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ) (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8947/65536 : ℝ)) 7 (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ) (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ) (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ) (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8947/65536 : ℝ))) (6112143119/31250000000 : ℝ) (97794289907/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8947/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (6112143119/31250000000 : ℝ) (97794289907/500000000000 : ℝ) (37362143119/62500000000 : ℝ) (597794289907/1000000000000 : ℝ) (110563494147/250000000000 : ℝ) (88450795319/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8947/65536 : ℝ))) 1 (37362143119/62500000000 : ℝ) (597794289907/1000000000000 : ℝ) (110563494147/250000000000 : ℝ) (88450795319/200000000000 : ℝ) (260012066623/500000000000 : ℝ) (520024133251/1000000000000 : ℝ) (514175944489/1000000000000 : ℝ) (102835188899/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8947/65536 : ℝ))) 2 (260012066623/500000000000 : ℝ) (520024133251/1000000000000 : ℝ) (514175944489/1000000000000 : ℝ) (102835188899/200000000000 : ℝ) (517100038867/1000000000000 : ℝ) (517100038873/1000000000000 : ℝ) (20683670849/40000000000 : ℝ) (517091771231/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8947/65536 : ℝ))) 3 (517100038867/1000000000000 : ℝ) (517100038873/1000000000000 : ℝ) (20683670849/40000000000 : ℝ) (517091771231/1000000000000 : ℝ) (258547952523/500000000000 : ℝ) (129273976263/250000000000 : ℝ) (517095905029/1000000000000 : ℝ) (129273976259/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8947/65536 : ℝ))) 4 (258547952523/500000000000 : ℝ) (129273976263/250000000000 : ℝ) (517095905029/1000000000000 : ℝ) (129273976259/250000000000 : ℝ) (517095905037/1000000000000 : ℝ) (129273976261/250000000000 : ℝ) (517095905037/1000000000000 : ℝ) (129273976261/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8947/65536 : ℝ))) 5 (517095905037/1000000000000 : ℝ) (129273976261/250000000000 : ℝ) (517095905037/1000000000000 : ℝ) (129273976261/250000000000 : ℝ) (517095905037/1000000000000 : ℝ) (129273976261/250000000000 : ℝ) (517095905037/1000000000000 : ℝ) (129273976261/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8947/65536 : ℝ))) 6 (517095905037/1000000000000 : ℝ) (129273976261/250000000000 : ℝ) (517095905037/1000000000000 : ℝ) (129273976261/250000000000 : ℝ) (517095905037/1000000000000 : ℝ) (129273976261/250000000000 : ℝ) (517095905037/1000000000000 : ℝ) (129273976261/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8947/65536 : ℝ))) 7 (517095905037/1000000000000 : ℝ) (129273976261/250000000000 : ℝ) (517095905037/1000000000000 : ℝ) (129273976261/250000000000 : ℝ) (517095905037/1000000000000 : ℝ) (129273976261/250000000000 : ℝ) (517095905037/1000000000000 : ℝ) (129273976261/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8947/65536 : ℝ)) hmem 8 (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ) (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8947/65536 : ℝ))) hcmem 8 (517095905037/1000000000000 : ℝ) (129273976261/250000000000 : ℝ) (517095905037/1000000000000 : ℝ) (129273976261/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8947/65536 : ℝ)) (990319477231/1000000000000 : ℝ) (495159738617/500000000000 : ℝ) (517095905037/1000000000000 : ℝ) (129273976261/250000000000 : ℝ) (820192237863/1000000000000 : ℝ) (410096118939/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0336_exp_lower
  have heNumeric : (2019009915059/1000000000000 : ℝ)/4 ≤ Real.exp (-5469496887399/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019009915059/1000000000000 : ℝ)/4 ≤ Real.exp ((4473/32768 : ℝ)-(410096118939/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4473/32768 : ℝ) (8947/65536 : ℝ) (410096118939/500000000000 : ℝ) (2019009915059/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0337; no trusted numerical premise.
theorem cover7_leaf0337_exp_radius : (24939120833280421/25000000000000000 : ℝ) ≤ Real.exp ((-2237/114688 : ℝ)/8) ∧ Real.exp ((-2237/114688 : ℝ)/8) ≤ (997564833331216841/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2237/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0337_exp_lower : (918089052511767679/1000000000000000000 : ℝ) ≤ Real.exp ((-10938993404557/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938993404557/16000000000000 : ℝ)/8) ≤ (1434514144549637/1562500000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938993404557/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0337_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019009961779/1000000000000 : ℝ) ≤ 4*Real.exp (8947/65536 : ℝ)*Real.exp (-mu (radius 7 (2237/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019009961779/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2237/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0337_exp_radius
  have hrNumeric : (980683901459/1000000000000 : ℝ) ≤ Real.exp (-2237/114688 : ℝ) ∧ Real.exp (-2237/114688 : ℝ) ≤ (49034195073/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980683901459/1000000000000 : ℝ) ≤ (radius 7 (2237/16384 : ℝ)) ∧ (radius 7 (2237/16384 : ℝ)) ≤ (49034195073/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2237/16384 : ℝ)) (980683901459/1000000000000 : ℝ) (49034195073/50000000000 : ℝ) (195599298099/1000000000000 : ℝ) (39119859621/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2237/16384 : ℝ)) (980683901459/1000000000000 : ℝ) (49034195073/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2237/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980683901459/1000000000000 : ℝ) (49034195073/50000000000 : ℝ) (990341950729/1000000000000 : ℝ) (99034195073/100000000000 : ℝ) (990294855817/1000000000000 : ℝ) (990294855819/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2237/16384 : ℝ)) 1 (990341950729/1000000000000 : ℝ) (99034195073/100000000000 : ℝ) (990294855817/1000000000000 : ℝ) (990294855819/1000000000000 : ℝ) (990318403273/1000000000000 : ℝ) (39612736131/40000000000 : ℝ) (990318402993/1000000000000 : ℝ) (198063680599/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2237/16384 : ℝ)) 2 (990318403273/1000000000000 : ℝ) (39612736131/40000000000 : ℝ) (990318402993/1000000000000 : ℝ) (198063680599/200000000000 : ℝ) (990318403133/1000000000000 : ℝ) (198063680627/200000000000 : ℝ) (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2237/16384 : ℝ)) 3 (990318403133/1000000000000 : ℝ) (198063680627/200000000000 : ℝ) (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ) (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ) (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2237/16384 : ℝ)) 4 (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ) (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ) (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ) (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2237/16384 : ℝ)) 5 (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ) (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ) (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ) (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2237/16384 : ℝ)) 6 (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ) (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ) (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ) (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2237/16384 : ℝ)) 7 (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ) (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ) (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ) (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2237/16384 : ℝ))) (195599298099/1000000000000 : ℝ) (39119859621/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2237/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195599298099/1000000000000 : ℝ) (39119859621/200000000000 : ℝ) (597799649049/1000000000000 : ℝ) (597799649053/1000000000000 : ℝ) (221133047111/500000000000 : ℝ) (44226609423/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2237/16384 : ℝ))) 1 (597799649049/1000000000000 : ℝ) (597799649053/1000000000000 : ℝ) (221133047111/500000000000 : ℝ) (44226609423/100000000000 : ℝ) (104006574327/200000000000 : ℝ) (260016435821/500000000000 : ℝ) (128546323341/250000000000 : ℝ) (514185293371/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2237/16384 : ℝ))) 2 (104006574327/200000000000 : ℝ) (260016435821/500000000000 : ℝ) (128546323341/250000000000 : ℝ) (514185293371/1000000000000 : ℝ) (517109082499/1000000000000 : ℝ) (517109082507/1000000000000 : ℝ) (517100816727/1000000000000 : ℝ) (103420163347/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2237/16384 : ℝ))) 3 (517109082499/1000000000000 : ℝ) (517109082507/1000000000000 : ℝ) (517100816727/1000000000000 : ℝ) (103420163347/200000000000 : ℝ) (517104949613/1000000000000 : ℝ) (517104949621/1000000000000 : ℝ) (129276237399/250000000000 : ℝ) (103420989921/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2237/16384 : ℝ))) 4 (517104949613/1000000000000 : ℝ) (517104949621/1000000000000 : ℝ) (129276237399/250000000000 : ℝ) (103420989921/200000000000 : ℝ) (129276237401/250000000000 : ℝ) (517104949613/1000000000000 : ℝ) (129276237401/250000000000 : ℝ) (517104949613/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2237/16384 : ℝ))) 5 (129276237401/250000000000 : ℝ) (517104949613/1000000000000 : ℝ) (129276237401/250000000000 : ℝ) (517104949613/1000000000000 : ℝ) (129276237401/250000000000 : ℝ) (517104949613/1000000000000 : ℝ) (129276237401/250000000000 : ℝ) (517104949613/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2237/16384 : ℝ))) 6 (129276237401/250000000000 : ℝ) (517104949613/1000000000000 : ℝ) (129276237401/250000000000 : ℝ) (517104949613/1000000000000 : ℝ) (129276237401/250000000000 : ℝ) (517104949613/1000000000000 : ℝ) (129276237401/250000000000 : ℝ) (517104949613/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2237/16384 : ℝ))) 7 (129276237401/250000000000 : ℝ) (517104949613/1000000000000 : ℝ) (129276237401/250000000000 : ℝ) (517104949613/1000000000000 : ℝ) (129276237401/250000000000 : ℝ) (517104949613/1000000000000 : ℝ) (129276237401/250000000000 : ℝ) (517104949613/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2237/16384 : ℝ)) hmem 8 (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ) (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2237/16384 : ℝ))) hcmem 8 (129276237401/250000000000 : ℝ) (517104949613/1000000000000 : ℝ) (129276237401/250000000000 : ℝ) (517104949613/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2237/16384 : ℝ)) (247579600783/250000000000 : ℝ) (198063680627/200000000000 : ℝ) (129276237401/250000000000 : ℝ) (517104949613/1000000000000 : ℝ) (820207473509/1000000000000 : ℝ) (820207473527/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0337_exp_lower
  have heNumeric : (2019009961779/1000000000000 : ℝ)/4 ≤ Real.exp (-10938993404557/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019009961779/1000000000000 : ℝ)/4 ≤ Real.exp ((8947/65536 : ℝ)-(820207473527/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8947/65536 : ℝ) (2237/16384 : ℝ) (820207473527/1000000000000 : ℝ) (2019009961779/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0338; no trusted numerical premise.
theorem cover7_leaf0338_exp_radius : (199512912303281603/200000000000000000 : ℝ) ≤ Real.exp ((-8949/458752 : ℝ)/8) ∧ Real.exp ((-8949/458752 : ℝ)/8) ≤ (62347785094775501/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8949/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0338_exp_lower : (459044527648685901/500000000000000000 : ℝ) ≤ Real.exp ((-2734748254047/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734748254047/4000000000000 : ℝ)/8) ≤ (918089055297371803/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734748254047/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0338_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009505005393/500000000000 : ℝ) ≤ 4*Real.exp (2237/16384 : ℝ)*Real.exp (-mu (radius 7 (8949/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009505005393/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8949/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0338_exp_radius
  have hrNumeric : (49034088187/50000000000 : ℝ) ≤ Real.exp (-8949/458752 : ℝ) ∧ Real.exp (-8949/458752 : ℝ) ≤ (980681763741/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49034088187/50000000000 : ℝ) ≤ (radius 7 (8949/65536 : ℝ)) ∧ (radius 7 (8949/65536 : ℝ)) ≤ (980681763741/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8949/65536 : ℝ)) (49034088187/50000000000 : ℝ) (980681763741/1000000000000 : ℝ) (2445125197/12500000000 : ℝ) (97805007883/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8949/65536 : ℝ)) (49034088187/50000000000 : ℝ) (980681763741/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8949/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49034088187/50000000000 : ℝ) (980681763741/1000000000000 : ℝ) (99034088187/100000000000 : ℝ) (990340881871/1000000000000 : ℝ) (495146888241/500000000000 : ℝ) (247573444121/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8949/65536 : ℝ)) 1 (99034088187/100000000000 : ℝ) (990340881871/1000000000000 : ℝ) (495146888241/500000000000 : ℝ) (247573444121/250000000000 : ℝ) (123789666147/125000000000 : ℝ) (495158664589/500000000000 : ℝ) (198063465779/200000000000 : ℝ) (495158664449/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8949/65536 : ℝ)) 2 (123789666147/125000000000 : ℝ) (495158664589/500000000000 : ℝ) (198063465779/200000000000 : ℝ) (495158664449/500000000000 : ℝ) (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ) (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8949/65536 : ℝ)) 3 (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ) (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ) (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ) (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8949/65536 : ℝ)) 4 (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ) (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ) (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ) (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8949/65536 : ℝ)) 5 (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ) (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ) (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ) (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8949/65536 : ℝ)) 6 (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ) (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ) (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ) (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8949/65536 : ℝ)) 7 (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ) (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ) (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ) (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8949/65536 : ℝ))) (2445125197/12500000000 : ℝ) (97805007883/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8949/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2445125197/12500000000 : ℝ) (97805007883/500000000000 : ℝ) (14945125197/25000000000 : ℝ) (597805007883/1000000000000 : ℝ) (442278210813/1000000000000 : ℝ) (22113910541/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8949/65536 : ℝ))) 1 (14945125197/25000000000 : ℝ) (597805007883/1000000000000 : ℝ) (442278210813/1000000000000 : ℝ) (22113910541/50000000000 : ℝ) (260020804673/500000000000 : ℝ) (65005201169/125000000000 : ℝ) (257097320727/500000000000 : ℝ) (25709732073/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8949/65536 : ℝ))) 2 (260020804673/500000000000 : ℝ) (65005201169/125000000000 : ℝ) (257097320727/500000000000 : ℝ) (25709732073/50000000000 : ℝ) (2585590627/5000000000 : ℝ) (258559062703/500000000000 : ℝ) (258554930749/500000000000 : ℝ) (103421972301/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8949/65536 : ℝ))) 3 (2585590627/5000000000 : ℝ) (258559062703/500000000000 : ℝ) (258554930749/500000000000 : ℝ) (103421972301/200000000000 : ℝ) (517113993449/1000000000000 : ℝ) (32319624591/62500000000 : ℝ) (64639249179/125000000000 : ℝ) (517113993439/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8949/65536 : ℝ))) 4 (517113993449/1000000000000 : ℝ) (32319624591/62500000000 : ℝ) (64639249179/125000000000 : ℝ) (517113993439/1000000000000 : ℝ) (3231962459/6250000000 : ℝ) (64639249181/125000000000 : ℝ) (3231962459/6250000000 : ℝ) (64639249181/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8949/65536 : ℝ))) 5 (3231962459/6250000000 : ℝ) (64639249181/125000000000 : ℝ) (3231962459/6250000000 : ℝ) (64639249181/125000000000 : ℝ) (3231962459/6250000000 : ℝ) (64639249181/125000000000 : ℝ) (3231962459/6250000000 : ℝ) (64639249181/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8949/65536 : ℝ))) 6 (3231962459/6250000000 : ℝ) (64639249181/125000000000 : ℝ) (3231962459/6250000000 : ℝ) (64639249181/125000000000 : ℝ) (3231962459/6250000000 : ℝ) (64639249181/125000000000 : ℝ) (3231962459/6250000000 : ℝ) (64639249181/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8949/65536 : ℝ))) 7 (3231962459/6250000000 : ℝ) (64639249181/125000000000 : ℝ) (3231962459/6250000000 : ℝ) (64639249181/125000000000 : ℝ) (3231962459/6250000000 : ℝ) (64639249181/125000000000 : ℝ) (3231962459/6250000000 : ℝ) (64639249181/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8949/65536 : ℝ)) hmem 8 (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ) (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8949/65536 : ℝ))) hcmem 8 (3231962459/6250000000 : ℝ) (64639249181/125000000000 : ℝ) (3231962459/6250000000 : ℝ) (64639249181/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8949/65536 : ℝ)) (198063465807/200000000000 : ℝ) (495158664519/500000000000 : ℝ) (3231962459/6250000000 : ℝ) (64639249181/125000000000 : ℝ) (820222708027/1000000000000 : ℝ) (820222708043/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0338_exp_lower
  have heNumeric : (1009505005393/500000000000 : ℝ)/4 ≤ Real.exp (-2734748254047/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009505005393/500000000000 : ℝ)/4 ≤ Real.exp ((2237/16384 : ℝ)-(820222708043/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2237/16384 : ℝ) (8949/65536 : ℝ) (820222708043/1000000000000 : ℝ) (1009505005393/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0339; no trusted numerical premise.
theorem cover7_leaf0339_exp_radius : (498782144850836627/500000000000000000 : ℝ) ≤ Real.exp ((-4475/229376 : ℝ)/8) ∧ Real.exp ((-4475/229376 : ℝ)/8) ≤ (199512857940334651/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4475/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0339_exp_lower : (459044529106557529/500000000000000000 : ℝ) ≤ Real.exp ((-437559704387/640000000000 : ℝ)/8) ∧ Real.exp ((-437559704387/640000000000 : ℝ)/8) ≤ (918089058213115059/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-437559704387/640000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0339_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504752515521/250000000000 : ℝ) ≤ 4*Real.exp (8949/65536 : ℝ)*Real.exp (-mu (radius 7 (4475/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (504752515521/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4475/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0339_exp_radius
  have hrNumeric : (39227185041/40000000000 : ℝ) ≤ Real.exp (-4475/229376 : ℝ) ∧ Real.exp (-4475/229376 : ℝ) ≤ (490339813013/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39227185041/40000000000 : ℝ) ≤ (radius 7 (4475/32768 : ℝ)) ∧ (radius 7 (4475/32768 : ℝ)) ≤ (490339813013/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4475/32768 : ℝ)) (39227185041/40000000000 : ℝ) (490339813013/500000000000 : ℝ) (19562073279/100000000000 : ℝ) (48905183199/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4475/32768 : ℝ)) (39227185041/40000000000 : ℝ) (490339813013/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4475/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39227185041/40000000000 : ℝ) (490339813013/500000000000 : ℝ) (247584953253/250000000000 : ℝ) (990339813013/1000000000000 : ℝ) (247573174287/250000000000 : ℝ) (990292697149/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4475/32768 : ℝ)) 1 (247584953253/250000000000 : ℝ) (990339813013/1000000000000 : ℝ) (247573174287/250000000000 : ℝ) (990292697149/1000000000000 : ℝ) (24757906377/25000000000 : ℝ) (990316255081/1000000000000 : ℝ) (990316254799/1000000000000 : ℝ) (990316254801/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4475/32768 : ℝ)) 2 (24757906377/25000000000 : ℝ) (990316255081/1000000000000 : ℝ) (990316254799/1000000000000 : ℝ) (990316254801/1000000000000 : ℝ) (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ) (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4475/32768 : ℝ)) 3 (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ) (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ) (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ) (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4475/32768 : ℝ)) 4 (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ) (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ) (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ) (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4475/32768 : ℝ)) 5 (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ) (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ) (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ) (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4475/32768 : ℝ)) 6 (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ) (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ) (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ) (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4475/32768 : ℝ)) 7 (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ) (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ) (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ) (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4475/32768 : ℝ))) (19562073279/100000000000 : ℝ) (48905183199/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4475/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19562073279/100000000000 : ℝ) (48905183199/250000000000 : ℝ) (119562073279/200000000000 : ℝ) (298905183199/500000000000 : ℝ) (221145163179/500000000000 : ℝ) (88458065273/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4475/32768 : ℝ))) 1 (119562073279/200000000000 : ℝ) (298905183199/500000000000 : ℝ) (221145163179/500000000000 : ℝ) (88458065273/200000000000 : ℝ) (65006293297/125000000000 : ℝ) (260025173191/500000000000 : ℝ) (128550997189/250000000000 : ℝ) (257101994381/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4475/32768 : ℝ))) 2 (65006293297/125000000000 : ℝ) (260025173191/500000000000 : ℝ) (128550997189/250000000000 : ℝ) (257101994381/500000000000 : ℝ) (258563583783/500000000000 : ℝ) (129281791893/250000000000 : ℝ) (517118905533/1000000000000 : ℝ) (25855945277/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4475/32768 : ℝ))) 3 (258563583783/500000000000 : ℝ) (129281791893/250000000000 : ℝ) (517118905533/1000000000000 : ℝ) (25855945277/50000000000 : ℝ) (517123036549/1000000000000 : ℝ) (129280759139/250000000000 : ℝ) (129280759133/250000000000 : ℝ) (25856151827/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4475/32768 : ℝ))) 4 (517123036549/1000000000000 : ℝ) (129280759139/250000000000 : ℝ) (129280759133/250000000000 : ℝ) (25856151827/50000000000 : ℝ) (25856151827/50000000000 : ℝ) (129280759137/250000000000 : ℝ) (25856151827/50000000000 : ℝ) (129280759137/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4475/32768 : ℝ))) 5 (25856151827/50000000000 : ℝ) (129280759137/250000000000 : ℝ) (25856151827/50000000000 : ℝ) (129280759137/250000000000 : ℝ) (25856151827/50000000000 : ℝ) (129280759137/250000000000 : ℝ) (25856151827/50000000000 : ℝ) (129280759137/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4475/32768 : ℝ))) 6 (25856151827/50000000000 : ℝ) (129280759137/250000000000 : ℝ) (25856151827/50000000000 : ℝ) (129280759137/250000000000 : ℝ) (25856151827/50000000000 : ℝ) (129280759137/250000000000 : ℝ) (25856151827/50000000000 : ℝ) (129280759137/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4475/32768 : ℝ))) 7 (25856151827/50000000000 : ℝ) (129280759137/250000000000 : ℝ) (25856151827/50000000000 : ℝ) (129280759137/250000000000 : ℝ) (25856151827/50000000000 : ℝ) (129280759137/250000000000 : ℝ) (25856151827/50000000000 : ℝ) (129280759137/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4475/32768 : ℝ)) hmem 8 (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ) (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4475/32768 : ℝ))) hcmem 8 (25856151827/50000000000 : ℝ) (129280759137/250000000000 : ℝ) (25856151827/50000000000 : ℝ) (129280759137/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4475/32768 : ℝ)) (990316254939/1000000000000 : ℝ) (990316254941/1000000000000 : ℝ) (25856151827/50000000000 : ℝ) (129280759137/250000000000 : ℝ) (82023794141/100000000000 : ℝ) (32809517657/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0339_exp_lower
  have heNumeric : (504752515521/250000000000 : ℝ)/4 ≤ Real.exp (-437559704387/640000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504752515521/250000000000 : ℝ)/4 ≤ Real.exp ((8949/65536 : ℝ)-(32809517657/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8949/65536 : ℝ) (4475/32768 : ℝ) (32809517657/40000000000 : ℝ) (504752515521/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0340; no trusted numerical premise.
theorem cover7_leaf0340_exp_radius : (997564017887012557/1000000000000000000 : ℝ) ≤ Real.exp ((-8951/458752 : ℝ)/8) ∧ Real.exp ((-8951/458752 : ℝ)/8) ≤ (498782008943506279/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8951/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0340_exp_lower : (57380566328744721/62500000000000000 : ℝ) ≤ Real.exp ((-1093899218489/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093899218489/1600000000000 : ℝ)/8) ≤ (918089061259915537/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093899218489/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0340_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009505057843/500000000000 : ℝ) ≤ 4*Real.exp (4475/32768 : ℝ)*Real.exp (-mu (radius 7 (8951/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009505057843/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8951/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0340_exp_radius
  have hrNumeric : (245169372079/250000000000 : ℝ) ≤ Real.exp (-8951/458752 : ℝ) ∧ Real.exp (-8951/458752 : ℝ) ≤ (980677488317/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245169372079/250000000000 : ℝ) ≤ (radius 7 (8951/65536 : ℝ)) ∧ (radius 7 (8951/65536 : ℝ)) ≤ (980677488317/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8951/65536 : ℝ)) (245169372079/250000000000 : ℝ) (980677488317/1000000000000 : ℝ) (195631449179/1000000000000 : ℝ) (39126289837/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8951/65536 : ℝ)) (245169372079/250000000000 : ℝ) (980677488317/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8951/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245169372079/250000000000 : ℝ) (980677488317/1000000000000 : ℝ) (495169372079/500000000000 : ℝ) (990338744159/1000000000000 : ℝ) (198058323563/200000000000 : ℝ) (990291617817/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8951/65536 : ℝ)) 1 (495169372079/500000000000 : ℝ) (990338744159/1000000000000 : ℝ) (198058323563/200000000000 : ℝ) (990291617817/1000000000000 : ℝ) (495157590493/500000000000 : ℝ) (247578795247/250000000000 : ℝ) (495157590353/500000000000 : ℝ) (247578795177/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8951/65536 : ℝ)) 2 (495157590493/500000000000 : ℝ) (247578795247/250000000000 : ℝ) (495157590353/500000000000 : ℝ) (247578795177/250000000000 : ℝ) (495157590423/500000000000 : ℝ) (61894698803/62500000000 : ℝ) (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8951/65536 : ℝ)) 3 (495157590423/500000000000 : ℝ) (61894698803/62500000000 : ℝ) (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ) (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ) (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8951/65536 : ℝ)) 4 (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ) (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ) (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ) (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8951/65536 : ℝ)) 5 (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ) (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ) (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ) (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8951/65536 : ℝ)) 6 (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ) (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ) (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ) (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8951/65536 : ℝ)) 7 (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ) (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ) (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ) (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8951/65536 : ℝ))) (195631449179/1000000000000 : ℝ) (39126289837/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8951/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195631449179/1000000000000 : ℝ) (39126289837/200000000000 : ℝ) (597815724589/1000000000000 : ℝ) (597815724593/1000000000000 : ℝ) (221151220423/500000000000 : ℝ) (221151220427/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8951/65536 : ℝ))) 1 (597815724589/1000000000000 : ℝ) (597815724593/1000000000000 : ℝ) (221151220423/500000000000 : ℝ) (221151220427/500000000000 : ℝ) (520059082717/1000000000000 : ℝ) (130014770681/250000000000 : ℝ) (257106667631/500000000000 : ℝ) (514213335269/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8951/65536 : ℝ))) 2 (520059082717/1000000000000 : ℝ) (130014770681/250000000000 : ℝ) (257106667631/500000000000 : ℝ) (514213335269/1000000000000 : ℝ) (517136208989/1000000000000 : ℝ) (517136208997/1000000000000 : ℝ) (258563974413/500000000000 : ℝ) (258563974417/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8951/65536 : ℝ))) 3 (517136208989/1000000000000 : ℝ) (517136208997/1000000000000 : ℝ) (258563974413/500000000000 : ℝ) (258563974417/500000000000 : ℝ) (517132078907/1000000000000 : ℝ) (129283019729/250000000000 : ℝ) (517132078891/1000000000000 : ℝ) (5171320789/10000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8951/65536 : ℝ))) 4 (517132078907/1000000000000 : ℝ) (129283019729/250000000000 : ℝ) (517132078891/1000000000000 : ℝ) (5171320789/10000000000 : ℝ) (517132078899/1000000000000 : ℝ) (129283019727/250000000000 : ℝ) (258566039449/500000000000 : ℝ) (129283019727/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8951/65536 : ℝ))) 5 (517132078899/1000000000000 : ℝ) (129283019727/250000000000 : ℝ) (258566039449/500000000000 : ℝ) (129283019727/250000000000 : ℝ) (258566039449/500000000000 : ℝ) (129283019727/250000000000 : ℝ) (258566039449/500000000000 : ℝ) (129283019727/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8951/65536 : ℝ))) 6 (258566039449/500000000000 : ℝ) (129283019727/250000000000 : ℝ) (258566039449/500000000000 : ℝ) (129283019727/250000000000 : ℝ) (258566039449/500000000000 : ℝ) (129283019727/250000000000 : ℝ) (258566039449/500000000000 : ℝ) (129283019727/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8951/65536 : ℝ))) 7 (258566039449/500000000000 : ℝ) (129283019727/250000000000 : ℝ) (258566039449/500000000000 : ℝ) (129283019727/250000000000 : ℝ) (258566039449/500000000000 : ℝ) (129283019727/250000000000 : ℝ) (258566039449/500000000000 : ℝ) (129283019727/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8951/65536 : ℝ)) hmem 8 (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ) (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8951/65536 : ℝ))) hcmem 8 (258566039449/500000000000 : ℝ) (129283019727/250000000000 : ℝ) (258566039449/500000000000 : ℝ) (129283019727/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8951/65536 : ℝ)) (198063036169/200000000000 : ℝ) (61894698803/62500000000 : ℝ) (258566039449/500000000000 : ℝ) (129283019727/250000000000 : ℝ) (410126586823/500000000000 : ℝ) (164050634733/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0340_exp_lower
  have heNumeric : (1009505057843/500000000000 : ℝ)/4 ≤ Real.exp (-1093899218489/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009505057843/500000000000 : ℝ)/4 ≤ Real.exp ((4475/32768 : ℝ)-(164050634733/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4475/32768 : ℝ) (8951/65536 : ℝ) (164050634733/200000000000 : ℝ) (1009505057843/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0341; no trusted numerical premise.
theorem cover7_leaf0341_exp_radius : (997563746072425923/1000000000000000000 : ℝ) ≤ Real.exp ((-1119/57344 : ℝ)/8) ∧ Real.exp ((-1119/57344 : ℝ)/8) ≤ (249390936518106481/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1119/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0341_exp_lower : (229522266109185097/250000000000000000 : ℝ) ≤ Real.exp ((-10938991741977/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938991741977/16000000000000 : ℝ)/8) ≤ (918089064436740389/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938991741977/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0341_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019010171577/1000000000000 : ℝ) ≤ 4*Real.exp (8951/65536 : ℝ)*Real.exp (-mu (radius 7 (1119/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019010171577/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1119/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0341_exp_radius
  have hrNumeric : (980675350611/1000000000000 : ℝ) ≤ Real.exp (-1119/57344 : ℝ) ∧ Real.exp (-1119/57344 : ℝ) ≤ (245168837653/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980675350611/1000000000000 : ℝ) ≤ (radius 7 (1119/8192 : ℝ)) ∧ (radius 7 (1119/8192 : ℝ)) ≤ (245168837653/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1119/8192 : ℝ)) (980675350611/1000000000000 : ℝ) (245168837653/250000000000 : ℝ) (195642164939/1000000000000 : ℝ) (39128432989/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1119/8192 : ℝ)) (980675350611/1000000000000 : ℝ) (245168837653/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1119/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980675350611/1000000000000 : ℝ) (245168837653/250000000000 : ℝ) (198067535061/200000000000 : ℝ) (495168837653/500000000000 : ℝ) (247572634621/250000000000 : ℝ) (198058107697/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1119/8192 : ℝ)) 1 (198067535061/200000000000 : ℝ) (495168837653/500000000000 : ℝ) (247572634621/250000000000 : ℝ) (198058107697/200000000000 : ℝ) (495157053447/500000000000 : ℝ) (61894631681/62500000000 : ℝ) (495157053307/500000000000 : ℝ) (123789263327/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1119/8192 : ℝ)) 2 (495157053447/500000000000 : ℝ) (61894631681/62500000000 : ℝ) (495157053307/500000000000 : ℝ) (123789263327/125000000000 : ℝ) (495157053377/500000000000 : ℝ) (247578526689/250000000000 : ℝ) (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1119/8192 : ℝ)) 3 (495157053377/500000000000 : ℝ) (247578526689/250000000000 : ℝ) (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ) (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ) (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1119/8192 : ℝ)) 4 (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ) (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ) (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ) (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1119/8192 : ℝ)) 5 (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ) (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ) (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ) (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1119/8192 : ℝ)) 6 (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ) (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ) (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ) (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1119/8192 : ℝ)) 7 (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ) (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ) (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ) (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1119/8192 : ℝ))) (195642164939/1000000000000 : ℝ) (39128432989/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1119/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195642164939/1000000000000 : ℝ) (39128432989/200000000000 : ℝ) (597821082469/1000000000000 : ℝ) (597821082473/1000000000000 : ℝ) (110578638573/250000000000 : ℝ) (4423145543/10000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1119/8192 : ℝ))) 1 (597821082469/1000000000000 : ℝ) (597821082473/1000000000000 : ℝ) (110578638573/250000000000 : ℝ) (4423145543/10000000000 : ℝ) (26003390919/50000000000 : ℝ) (520067818387/1000000000000 : ℝ) (64277835123/125000000000 : ℝ) (514222680991/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1119/8192 : ℝ))) 2 (26003390919/50000000000 : ℝ) (520067818387/1000000000000 : ℝ) (64277835123/125000000000 : ℝ) (514222680991/1000000000000 : ℝ) (258572624841/500000000000 : ℝ) (517145249689/1000000000000 : ℝ) (517136991387/1000000000000 : ℝ) (103427398279/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1119/8192 : ℝ))) 3 (258572624841/500000000000 : ℝ) (517145249689/1000000000000 : ℝ) (517136991387/1000000000000 : ℝ) (103427398279/200000000000 : ℝ) (258570560267/500000000000 : ℝ) (258570560271/500000000000 : ℝ) (258570560259/500000000000 : ℝ) (258570560263/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1119/8192 : ℝ))) 4 (258570560267/500000000000 : ℝ) (258570560271/500000000000 : ℝ) (258570560259/500000000000 : ℝ) (258570560263/500000000000 : ℝ) (258570560263/500000000000 : ℝ) (258570560267/500000000000 : ℝ) (20685644821/40000000000 : ℝ) (258570560267/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1119/8192 : ℝ))) 5 (258570560263/500000000000 : ℝ) (258570560267/500000000000 : ℝ) (20685644821/40000000000 : ℝ) (258570560267/500000000000 : ℝ) (20685644821/40000000000 : ℝ) (258570560267/500000000000 : ℝ) (20685644821/40000000000 : ℝ) (258570560267/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1119/8192 : ℝ))) 6 (20685644821/40000000000 : ℝ) (258570560267/500000000000 : ℝ) (20685644821/40000000000 : ℝ) (258570560267/500000000000 : ℝ) (20685644821/40000000000 : ℝ) (258570560267/500000000000 : ℝ) (20685644821/40000000000 : ℝ) (258570560267/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1119/8192 : ℝ))) 7 (20685644821/40000000000 : ℝ) (258570560267/500000000000 : ℝ) (20685644821/40000000000 : ℝ) (258570560267/500000000000 : ℝ) (20685644821/40000000000 : ℝ) (258570560267/500000000000 : ℝ) (20685644821/40000000000 : ℝ) (258570560267/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1119/8192 : ℝ)) hmem 8 (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ) (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1119/8192 : ℝ))) hcmem 8 (20685644821/40000000000 : ℝ) (258570560267/500000000000 : ℝ) (20685644821/40000000000 : ℝ) (258570560267/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1119/8192 : ℝ)) (990314106753/1000000000000 : ℝ) (247578526689/250000000000 : ℝ) (20685644821/40000000000 : ℝ) (258570560267/500000000000 : ℝ) (164053680951/200000000000 : ℝ) (205067101193/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0341_exp_lower
  have heNumeric : (2019010171577/1000000000000 : ℝ)/4 ≤ Real.exp (-10938991741977/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019010171577/1000000000000 : ℝ)/4 ≤ Real.exp ((8951/65536 : ℝ)-(205067101193/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8951/65536 : ℝ) (1119/8192 : ℝ) (205067101193/250000000000 : ℝ) (2019010171577/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0342; no trusted numerical premise.
theorem cover7_leaf0342_exp_radius : (124695434282239169/125000000000000000 : ℝ) ≤ Real.exp ((-1279/65536 : ℝ)/8) ∧ Real.exp ((-1279/65536 : ℝ)/8) ≤ (997563474257913353/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1279/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0342_exp_lower : (57380566734024559/62500000000000000 : ℝ) ≤ Real.exp ((-1367373910103/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367373910103/2000000000000 : ℝ)/8) ≤ (183617813548878589/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367373910103/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0342_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019010229769/1000000000000 : ℝ) ≤ 4*Real.exp (1119/8192 : ℝ)*Real.exp (-mu (radius 7 (8953/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019010229769/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8953/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0342_exp_radius
  have hrNumeric : (980673212911/1000000000000 : ℝ) ≤ Real.exp (-1279/65536 : ℝ) ∧ Real.exp (-1279/65536 : ℝ) ≤ (61292075807/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980673212911/1000000000000 : ℝ) ≤ (radius 7 (8953/65536 : ℝ)) ∧ (radius 7 (8953/65536 : ℝ)) ≤ (61292075807/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8953/65536 : ℝ)) (980673212911/1000000000000 : ℝ) (61292075807/62500000000 : ℝ) (97826440031/500000000000 : ℝ) (48913220017/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8953/65536 : ℝ)) (980673212911/1000000000000 : ℝ) (61292075807/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8953/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980673212911/1000000000000 : ℝ) (61292075807/62500000000 : ℝ) (198067321291/200000000000 : ℝ) (123792075807/125000000000 : ℝ) (990289459153/1000000000000 : ℝ) (198057891831/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8953/65536 : ℝ)) 1 (198067321291/200000000000 : ℝ) (123792075807/125000000000 : ℝ) (990289459153/1000000000000 : ℝ) (198057891831/200000000000 : ℝ) (247578258201/250000000000 : ℝ) (495156516403/500000000000 : ℝ) (990313032523/1000000000000 : ℝ) (39612521301/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8953/65536 : ℝ)) 2 (247578258201/250000000000 : ℝ) (495156516403/500000000000 : ℝ) (990313032523/1000000000000 : ℝ) (39612521301/40000000000 : ℝ) (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ) (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8953/65536 : ℝ)) 3 (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ) (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ) (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ) (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8953/65536 : ℝ)) 4 (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ) (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ) (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ) (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8953/65536 : ℝ)) 5 (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ) (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ) (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ) (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8953/65536 : ℝ)) 6 (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ) (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ) (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ) (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8953/65536 : ℝ)) 7 (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ) (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ) (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ) (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8953/65536 : ℝ))) (97826440031/500000000000 : ℝ) (48913220017/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8953/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97826440031/500000000000 : ℝ) (48913220017/250000000000 : ℝ) (597826440031/1000000000000 : ℝ) (298913220017/500000000000 : ℝ) (221163333343/500000000000 : ℝ) (221163333347/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8953/65536 : ℝ))) 1 (597826440031/1000000000000 : ℝ) (298913220017/500000000000 : ℝ) (221163333343/500000000000 : ℝ) (221163333347/500000000000 : ℝ) (260038276679/500000000000 : ℝ) (130019138341/250000000000 : ℝ) (257116012957/500000000000 : ℝ) (1606975081/3125000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8953/65536 : ℝ))) 2 (260038276679/500000000000 : ℝ) (130019138341/250000000000 : ℝ) (257116012957/500000000000 : ℝ) (1606975081/3125000000 : ℝ) (129288572409/250000000000 : ℝ) (258577144821/500000000000 : ℝ) (64643254151/125000000000 : ℝ) (103429206643/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8953/65536 : ℝ))) 3 (129288572409/250000000000 : ℝ) (258577144821/500000000000 : ℝ) (64643254151/125000000000 : ℝ) (103429206643/200000000000 : ℝ) (258575080711/500000000000 : ℝ) (517150161429/1000000000000 : ℝ) (103430032281/200000000000 : ℝ) (517150161413/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8953/65536 : ℝ))) 4 (258575080711/500000000000 : ℝ) (517150161429/1000000000000 : ℝ) (103430032281/200000000000 : ℝ) (517150161413/1000000000000 : ℝ) (517150161413/1000000000000 : ℝ) (517150161421/1000000000000 : ℝ) (517150161413/1000000000000 : ℝ) (517150161421/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8953/65536 : ℝ))) 5 (517150161413/1000000000000 : ℝ) (517150161421/1000000000000 : ℝ) (517150161413/1000000000000 : ℝ) (517150161421/1000000000000 : ℝ) (517150161413/1000000000000 : ℝ) (517150161421/1000000000000 : ℝ) (517150161413/1000000000000 : ℝ) (517150161421/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8953/65536 : ℝ))) 6 (517150161413/1000000000000 : ℝ) (517150161421/1000000000000 : ℝ) (517150161413/1000000000000 : ℝ) (517150161421/1000000000000 : ℝ) (517150161413/1000000000000 : ℝ) (517150161421/1000000000000 : ℝ) (517150161413/1000000000000 : ℝ) (517150161421/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8953/65536 : ℝ))) 7 (517150161413/1000000000000 : ℝ) (517150161421/1000000000000 : ℝ) (517150161413/1000000000000 : ℝ) (517150161421/1000000000000 : ℝ) (517150161413/1000000000000 : ℝ) (517150161421/1000000000000 : ℝ) (517150161413/1000000000000 : ℝ) (517150161421/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8953/65536 : ℝ)) hmem 8 (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ) (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8953/65536 : ℝ))) hcmem 8 (517150161413/1000000000000 : ℝ) (517150161421/1000000000000 : ℝ) (517150161413/1000000000000 : ℝ) (517150161421/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8953/65536 : ℝ)) (990313032663/1000000000000 : ℝ) (495156516333/500000000000 : ℝ) (517150161413/1000000000000 : ℝ) (517150161421/1000000000000 : ℝ) (820283634723/1000000000000 : ℝ) (820283634739/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0342_exp_lower
  have heNumeric : (2019010229769/1000000000000 : ℝ)/4 ≤ Real.exp (-1367373910103/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019010229769/1000000000000 : ℝ)/4 ≤ Real.exp ((1119/8192 : ℝ)-(820283634739/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1119/8192 : ℝ) (8953/65536 : ℝ) (820283634739/1000000000000 : ℝ) (2019010229769/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0343; no trusted numerical premise.
theorem cover7_leaf0343_exp_radius : (498781601221737423/500000000000000000 : ℝ) ≤ Real.exp ((-4477/229376 : ℝ)/8) ∧ Real.exp ((-4477/229376 : ℝ)/8) ≤ (997563202443474847/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4477/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0343_exp_lower : (91808907118149607/100000000000000000 : ℝ) ≤ Real.exp ((-10938990801623/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938990801623/16000000000000 : ℝ)/8) ≤ (918089071181496071/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938990801623/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0343_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009505145119/500000000000 : ℝ) ≤ 4*Real.exp (8953/65536 : ℝ)*Real.exp (-mu (radius 7 (4477/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009505145119/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4477/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0343_exp_radius
  have hrNumeric : (196134215043/200000000000 : ℝ) ≤ Real.exp (-4477/229376 : ℝ) ∧ Real.exp (-4477/229376 : ℝ) ≤ (61291942201/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196134215043/200000000000 : ℝ) ≤ (radius 7 (4477/32768 : ℝ)) ∧ (radius 7 (4477/32768 : ℝ)) ≤ (61291942201/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4477/32768 : ℝ)) (196134215043/200000000000 : ℝ) (61291942201/62500000000 : ℝ) (48915898639/250000000000 : ℝ) (97831797281/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4477/32768 : ℝ)) (196134215043/200000000000 : ℝ) (61291942201/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4477/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196134215043/200000000000 : ℝ) (61291942201/62500000000 : ℝ) (990335537607/1000000000000 : ℝ) (123791942201/125000000000 : ℝ) (61893023739/62500000000 : ℝ) (39611535193/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4477/32768 : ℝ)) 1 (990335537607/1000000000000 : ℝ) (123791942201/125000000000 : ℝ) (61893023739/62500000000 : ℝ) (39611535193/40000000000 : ℝ) (198062391743/200000000000 : ℝ) (990311958717/1000000000000 : ℝ) (495155979217/500000000000 : ℝ) (247577989609/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4477/32768 : ℝ)) 2 (198062391743/200000000000 : ℝ) (990311958717/1000000000000 : ℝ) (495155979217/500000000000 : ℝ) (247577989609/250000000000 : ℝ) (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ) (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4477/32768 : ℝ)) 3 (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ) (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ) (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ) (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4477/32768 : ℝ)) 4 (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ) (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ) (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ) (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4477/32768 : ℝ)) 5 (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ) (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ) (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ) (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4477/32768 : ℝ)) 6 (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ) (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ) (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ) (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4477/32768 : ℝ)) 7 (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ) (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ) (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ) (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4477/32768 : ℝ))) (48915898639/250000000000 : ℝ) (97831797281/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4477/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48915898639/250000000000 : ℝ) (97831797281/500000000000 : ℝ) (298915898639/500000000000 : ℝ) (597831797281/1000000000000 : ℝ) (442338778037/1000000000000 : ℝ) (88467755609/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4477/32768 : ℝ))) 1 (298915898639/500000000000 : ℝ) (597831797281/1000000000000 : ℝ) (442338778037/1000000000000 : ℝ) (88467755609/200000000000 : ℝ) (520085287657/1000000000000 : ℝ) (520085287663/1000000000000 : ℝ) (257120685029/500000000000 : ℝ) (102848274013/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4477/32768 : ℝ))) 2 (520085287657/1000000000000 : ℝ) (520085287663/1000000000000 : ℝ) (257120685029/500000000000 : ℝ) (102848274013/200000000000 : ℝ) (517163328857/1000000000000 : ℝ) (16161354027/31250000000 : ℝ) (517155074297/1000000000000 : ℝ) (103431014861/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4477/32768 : ℝ))) 3 (517163328857/1000000000000 : ℝ) (16161354027/31250000000 : ℝ) (517155074297/1000000000000 : ℝ) (103431014861/200000000000 : ℝ) (517159201577/1000000000000 : ℝ) (103431840317/200000000000 : ℝ) (12928980039/25000000000 : ℝ) (517159201569/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4477/32768 : ℝ))) 4 (517159201577/1000000000000 : ℝ) (103431840317/200000000000 : ℝ) (12928980039/25000000000 : ℝ) (517159201569/1000000000000 : ℝ) (16161225049/31250000000 : ℝ) (517159201577/1000000000000 : ℝ) (16161225049/31250000000 : ℝ) (517159201577/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4477/32768 : ℝ))) 5 (16161225049/31250000000 : ℝ) (517159201577/1000000000000 : ℝ) (16161225049/31250000000 : ℝ) (517159201577/1000000000000 : ℝ) (16161225049/31250000000 : ℝ) (517159201577/1000000000000 : ℝ) (16161225049/31250000000 : ℝ) (517159201577/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4477/32768 : ℝ))) 6 (16161225049/31250000000 : ℝ) (517159201577/1000000000000 : ℝ) (16161225049/31250000000 : ℝ) (517159201577/1000000000000 : ℝ) (16161225049/31250000000 : ℝ) (517159201577/1000000000000 : ℝ) (16161225049/31250000000 : ℝ) (517159201577/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4477/32768 : ℝ))) 7 (16161225049/31250000000 : ℝ) (517159201577/1000000000000 : ℝ) (16161225049/31250000000 : ℝ) (517159201577/1000000000000 : ℝ) (16161225049/31250000000 : ℝ) (517159201577/1000000000000 : ℝ) (16161225049/31250000000 : ℝ) (517159201577/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4477/32768 : ℝ)) hmem 8 (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ) (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4477/32768 : ℝ))) hcmem 8 (16161225049/31250000000 : ℝ) (517159201577/1000000000000 : ℝ) (16161225049/31250000000 : ℝ) (517159201577/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4477/32768 : ℝ)) (495155979287/500000000000 : ℝ) (990311958577/1000000000000 : ℝ) (16161225049/31250000000 : ℝ) (517159201577/1000000000000 : ℝ) (20507471589/25000000000 : ℝ) (410149431789/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0343_exp_lower
  have heNumeric : (1009505145119/500000000000 : ℝ)/4 ≤ Real.exp (-10938990801623/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009505145119/500000000000 : ℝ)/4 ≤ Real.exp ((8953/65536 : ℝ)-(410149431789/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8953/65536 : ℝ) (4477/32768 : ℝ) (410149431789/500000000000 : ℝ) (1009505145119/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0344; no trusted numerical premise.
theorem cover7_leaf0344_exp_radius : (997562930629110403/1000000000000000000 : ℝ) ≤ Real.exp ((-8955/458752 : ℝ)/8) ∧ Real.exp ((-8955/458752 : ℝ)/8) ≤ (249390732657277601/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8955/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0344_exp_lower : (918089074749426903/1000000000000000000 : ℝ) ≤ Real.exp ((-5469495152091/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469495152091/8000000000000 : ℝ)/8) ≤ (114761134343678363/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469495152091/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0344_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019010353009/1000000000000 : ℝ) ≤ 4*Real.exp (4477/32768 : ℝ)*Real.exp (-mu (radius 7 (8955/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019010353009/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8955/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0344_exp_radius
  have hrNumeric : (245167234381/250000000000 : ℝ) ≤ Real.exp (-8955/458752 : ℝ) ∧ Real.exp (-8955/458752 : ℝ) ≤ (39226757501/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245167234381/250000000000 : ℝ) ≤ (radius 7 (8955/65536 : ℝ)) ∧ (radius 7 (8955/65536 : ℝ)) ≤ (39226757501/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8955/65536 : ℝ)) (245167234381/250000000000 : ℝ) (39226757501/40000000000 : ℝ) (97837154207/500000000000 : ℝ) (9783715421/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8955/65536 : ℝ)) (245167234381/250000000000 : ℝ) (39226757501/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8955/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245167234381/250000000000 : ℝ) (39226757501/40000000000 : ℝ) (495167234381/500000000000 : ℝ) (990334468763/1000000000000 : ℝ) (61892956281/62500000000 : ℝ) (990287300497/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8955/65536 : ℝ)) 1 (495167234381/500000000000 : ℝ) (990334468763/1000000000000 : ℝ) (61892956281/62500000000 : ℝ) (990287300497/1000000000000 : ℝ) (990310884629/1000000000000 : ℝ) (99031088463/100000000000 : ℝ) (247577721087/250000000000 : ℝ) (19806217687/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8955/65536 : ℝ)) 2 (990310884629/1000000000000 : ℝ) (99031088463/100000000000 : ℝ) (247577721087/250000000000 : ℝ) (19806217687/20000000000 : ℝ) (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ) (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8955/65536 : ℝ)) 3 (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ) (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ) (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ) (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8955/65536 : ℝ)) 4 (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ) (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ) (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ) (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8955/65536 : ℝ)) 5 (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ) (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ) (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ) (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8955/65536 : ℝ)) 6 (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ) (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ) (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ) (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8955/65536 : ℝ)) 7 (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ) (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ) (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ) (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8955/65536 : ℝ))) (97837154207/500000000000 : ℝ) (9783715421/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8955/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97837154207/500000000000 : ℝ) (9783715421/50000000000 : ℝ) (597837154207/1000000000000 : ℝ) (59783715421/100000000000 : ℝ) (221175444169/500000000000 : ℝ) (221175444173/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8955/65536 : ℝ))) 1 (597837154207/1000000000000 : ℝ) (59783715421/100000000000 : ℝ) (221175444169/500000000000 : ℝ) (221175444173/500000000000 : ℝ) (65011752659/125000000000 : ℝ) (260047010639/500000000000 : ℝ) (128562678353/250000000000 : ℝ) (514250713419/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8955/65536 : ℝ))) 2 (65011752659/125000000000 : ℝ) (260047010639/500000000000 : ℝ) (128562678353/250000000000 : ℝ) (514250713419/1000000000000 : ℝ) (258586183671/500000000000 : ℝ) (517172367349/1000000000000 : ℝ) (64645514331/125000000000 : ℝ) (16161378583/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8955/65536 : ℝ))) 3 (258586183671/500000000000 : ℝ) (517172367349/1000000000000 : ℝ) (64645514331/125000000000 : ℝ) (16161378583/31250000000 : ℝ) (103433648199/200000000000 : ℝ) (517168241003/1000000000000 : ℝ) (258584120489/500000000000 : ℝ) (517168240987/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8955/65536 : ℝ))) 4 (103433648199/200000000000 : ℝ) (517168241003/1000000000000 : ℝ) (258584120489/500000000000 : ℝ) (517168240987/1000000000000 : ℝ) (258584120493/500000000000 : ℝ) (103433648199/200000000000 : ℝ) (258584120493/500000000000 : ℝ) (103433648199/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8955/65536 : ℝ))) 5 (258584120493/500000000000 : ℝ) (103433648199/200000000000 : ℝ) (258584120493/500000000000 : ℝ) (103433648199/200000000000 : ℝ) (258584120493/500000000000 : ℝ) (103433648199/200000000000 : ℝ) (258584120493/500000000000 : ℝ) (103433648199/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8955/65536 : ℝ))) 6 (258584120493/500000000000 : ℝ) (103433648199/200000000000 : ℝ) (258584120493/500000000000 : ℝ) (103433648199/200000000000 : ℝ) (258584120493/500000000000 : ℝ) (103433648199/200000000000 : ℝ) (258584120493/500000000000 : ℝ) (103433648199/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8955/65536 : ℝ))) 7 (258584120493/500000000000 : ℝ) (103433648199/200000000000 : ℝ) (258584120493/500000000000 : ℝ) (103433648199/200000000000 : ℝ) (258584120493/500000000000 : ℝ) (103433648199/200000000000 : ℝ) (258584120493/500000000000 : ℝ) (103433648199/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8955/65536 : ℝ)) hmem 8 (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ) (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8955/65536 : ℝ))) hcmem 8 (258584120493/500000000000 : ℝ) (103433648199/200000000000 : ℝ) (258584120493/500000000000 : ℝ) (103433648199/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8955/65536 : ℝ)) (123788860561/125000000000 : ℝ) (99031088449/100000000000 : ℝ) (258584120493/500000000000 : ℝ) (103433648199/200000000000 : ℝ) (41015704563/50000000000 : ℝ) (820314091277/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0344_exp_lower
  have heNumeric : (2019010353009/1000000000000 : ℝ)/4 ≤ Real.exp (-5469495152091/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019010353009/1000000000000 : ℝ)/4 ≤ Real.exp ((4477/32768 : ℝ)-(820314091277/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4477/32768 : ℝ) (8955/65536 : ℝ) (820314091277/1000000000000 : ℝ) (2019010353009/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0345; no trusted numerical premise.
theorem cover7_leaf0345_exp_radius : (997562658814820023/1000000000000000000 : ℝ) ≤ Real.exp ((-2239/114688 : ℝ)/8) ∧ Real.exp ((-2239/114688 : ℝ)/8) ≤ (124695332351852503/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2239/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0345_exp_lower : (918089078447841159/1000000000000000000 : ℝ) ≤ Real.exp ((-10938989788549/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938989788549/16000000000000 : ℝ)/8) ≤ (22952226961196029/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938989788549/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0345_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504752604519/250000000000 : ℝ) ≤ 4*Real.exp (8955/65536 : ℝ)*Real.exp (-mu (radius 7 (2239/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (504752604519/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2239/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0345_exp_radius
  have hrNumeric : (490333399919/500000000000 : ℝ) ≤ Real.exp (-2239/114688 : ℝ) ∧ Real.exp (-2239/114688 : ℝ) ≤ (980666799839/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490333399919/500000000000 : ℝ) ≤ (radius 7 (2239/16384 : ℝ)) ∧ (radius 7 (2239/16384 : ℝ)) ≤ (980666799839/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2239/16384 : ℝ)) (490333399919/500000000000 : ℝ) (980666799839/1000000000000 : ℝ) (97842510819/500000000000 : ℝ) (48921255411/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2239/16384 : ℝ)) (490333399919/500000000000 : ℝ) (980666799839/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2239/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490333399919/500000000000 : ℝ) (980666799839/1000000000000 : ℝ) (990333399919/1000000000000 : ℝ) (12379167499/12500000000 : ℝ) (990286221169/1000000000000 : ℝ) (99028622117/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2239/16384 : ℝ)) 1 (990333399919/1000000000000 : ℝ) (12379167499/12500000000 : ℝ) (990286221169/1000000000000 : ℝ) (99028622117/100000000000 : ℝ) (61894363159/62500000000 : ℝ) (198061962109/200000000000 : ℝ) (990309810263/1000000000000 : ℝ) (198061962053/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2239/16384 : ℝ)) 2 (61894363159/62500000000 : ℝ) (198061962109/200000000000 : ℝ) (990309810263/1000000000000 : ℝ) (198061962053/200000000000 : ℝ) (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ) (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2239/16384 : ℝ)) 3 (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ) (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ) (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ) (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2239/16384 : ℝ)) 4 (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ) (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ) (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ) (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2239/16384 : ℝ)) 5 (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ) (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ) (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ) (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2239/16384 : ℝ)) 6 (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ) (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ) (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ) (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2239/16384 : ℝ)) 7 (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ) (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ) (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ) (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2239/16384 : ℝ))) (97842510819/500000000000 : ℝ) (48921255411/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2239/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97842510819/500000000000 : ℝ) (48921255411/250000000000 : ℝ) (597842510819/1000000000000 : ℝ) (298921255411/500000000000 : ℝ) (442362997591/1000000000000 : ℝ) (442362997599/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2239/16384 : ℝ))) 1 (597842510819/1000000000000 : ℝ) (298921255411/500000000000 : ℝ) (442362997591/1000000000000 : ℝ) (442362997599/1000000000000 : ℝ) (104020550841/200000000000 : ℝ) (520102754211/1000000000000 : ℝ) (64282506997/125000000000 : ℝ) (514260055983/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2239/16384 : ℝ))) 2 (104020550841/200000000000 : ℝ) (520102754211/1000000000000 : ℝ) (64282506997/125000000000 : ℝ) (514260055983/1000000000000 : ℝ) (51718140509/100000000000 : ℝ) (517181405097/1000000000000 : ℝ) (517173154263/1000000000000 : ℝ) (51717315427/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2239/16384 : ℝ))) 3 (51718140509/100000000000 : ℝ) (517181405097/1000000000000 : ℝ) (517173154263/1000000000000 : ℝ) (51717315427/100000000000 : ℝ) (129294319919/250000000000 : ℝ) (129294319921/250000000000 : ℝ) (25858863983/50000000000 : ℝ) (129294319917/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2239/16384 : ℝ))) 4 (129294319919/250000000000 : ℝ) (129294319921/250000000000 : ℝ) (25858863983/50000000000 : ℝ) (129294319917/250000000000 : ℝ) (129294319917/250000000000 : ℝ) (129294319919/250000000000 : ℝ) (517177279667/1000000000000 : ℝ) (129294319919/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2239/16384 : ℝ))) 5 (129294319917/250000000000 : ℝ) (129294319919/250000000000 : ℝ) (517177279667/1000000000000 : ℝ) (129294319919/250000000000 : ℝ) (517177279667/1000000000000 : ℝ) (129294319919/250000000000 : ℝ) (517177279667/1000000000000 : ℝ) (129294319919/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2239/16384 : ℝ))) 6 (517177279667/1000000000000 : ℝ) (129294319919/250000000000 : ℝ) (517177279667/1000000000000 : ℝ) (129294319919/250000000000 : ℝ) (517177279667/1000000000000 : ℝ) (129294319919/250000000000 : ℝ) (517177279667/1000000000000 : ℝ) (129294319919/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2239/16384 : ℝ))) 7 (517177279667/1000000000000 : ℝ) (129294319919/250000000000 : ℝ) (517177279667/1000000000000 : ℝ) (129294319919/250000000000 : ℝ) (517177279667/1000000000000 : ℝ) (129294319919/250000000000 : ℝ) (517177279667/1000000000000 : ℝ) (129294319919/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2239/16384 : ℝ)) hmem 8 (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ) (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2239/16384 : ℝ))) hcmem 8 (517177279667/1000000000000 : ℝ) (129294319919/250000000000 : ℝ) (517177279667/1000000000000 : ℝ) (129294319919/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2239/16384 : ℝ)) (990309810403/1000000000000 : ℝ) (198061962081/200000000000 : ℝ) (517177279667/1000000000000 : ℝ) (129294319919/250000000000 : ℝ) (410164658911/500000000000 : ℝ) (820329317839/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0345_exp_lower
  have heNumeric : (504752604519/250000000000 : ℝ)/4 ≤ Real.exp (-10938989788549/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504752604519/250000000000 : ℝ)/4 ≤ Real.exp ((8955/65536 : ℝ)-(820329317839/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8955/65536 : ℝ) (2239/16384 : ℝ) (820329317839/1000000000000 : ℝ) (504752604519/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0346; no trusted numerical premise.
theorem cover7_leaf0346_exp_radius : (997562387000603707/1000000000000000000 : ℝ) ≤ Real.exp ((-8957/458752 : ℝ)/8) ∧ Real.exp ((-8957/458752 : ℝ)/8) ≤ (249390596750150927/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8957/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0346_exp_lower : (918089082275935513/1000000000000000000 : ℝ) ≤ Real.exp ((-2734747313709/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734747313709/4000000000000 : ℝ)/8) ≤ (459044541137967757/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734747313709/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0346_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (126188155339/62500000000 : ℝ) ≤ 4*Real.exp (2239/16384 : ℝ)*Real.exp (-mu (radius 7 (8957/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (126188155339/62500000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8957/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0346_exp_radius
  have hrNumeric : (245166165539/250000000000 : ℝ) ≤ Real.exp (-8957/458752 : ℝ) ∧ Real.exp (-8957/458752 : ℝ) ≤ (980664662157/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245166165539/250000000000 : ℝ) ≤ (radius 7 (8957/65536 : ℝ)) ∧ (radius 7 (8957/65536 : ℝ)) ≤ (980664662157/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8957/65536 : ℝ)) (245166165539/250000000000 : ℝ) (980664662157/1000000000000 : ℝ) (195695734231/1000000000000 : ℝ) (195695734237/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8957/65536 : ℝ)) (245166165539/250000000000 : ℝ) (980664662157/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8957/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245166165539/250000000000 : ℝ) (980664662157/1000000000000 : ℝ) (495166165539/500000000000 : ℝ) (990332331079/1000000000000 : ℝ) (990285141843/1000000000000 : ℝ) (198057028369/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8957/65536 : ℝ)) 1 (495166165539/500000000000 : ℝ) (990332331079/1000000000000 : ℝ) (990285141843/1000000000000 : ℝ) (198057028369/200000000000 : ℝ) (49515436823/50000000000 : ℝ) (495154368231/500000000000 : ℝ) (990308736179/1000000000000 : ℝ) (990308736181/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8957/65536 : ℝ)) 2 (49515436823/50000000000 : ℝ) (495154368231/500000000000 : ℝ) (990308736179/1000000000000 : ℝ) (990308736181/1000000000000 : ℝ) (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ) (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8957/65536 : ℝ)) 3 (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ) (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ) (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ) (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8957/65536 : ℝ)) 4 (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ) (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ) (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ) (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8957/65536 : ℝ)) 5 (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ) (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ) (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ) (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8957/65536 : ℝ)) 6 (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ) (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ) (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ) (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8957/65536 : ℝ)) 7 (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ) (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ) (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ) (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8957/65536 : ℝ))) (195695734231/1000000000000 : ℝ) (195695734237/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8957/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195695734231/1000000000000 : ℝ) (195695734237/1000000000000 : ℝ) (119569573423/200000000000 : ℝ) (597847867119/1000000000000 : ℝ) (442375105799/1000000000000 : ℝ) (442375105807/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8957/65536 : ℝ))) 1 (119569573423/200000000000 : ℝ) (597847867119/1000000000000 : ℝ) (442375105799/1000000000000 : ℝ) (442375105807/1000000000000 : ℝ) (520111486457/1000000000000 : ℝ) (520111486463/1000000000000 : ℝ) (257134698877/500000000000 : ℝ) (514269397761/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8957/65536 : ℝ))) 2 (520111486457/1000000000000 : ℝ) (520111486463/1000000000000 : ℝ) (257134698877/500000000000 : ℝ) (514269397761/1000000000000 : ℝ) (103438088421/200000000000 : ℝ) (4040550329/7812500000 : ℝ) (517182193143/1000000000000 : ℝ) (517182193151/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8957/65536 : ℝ))) 3 (103438088421/200000000000 : ℝ) (4040550329/7812500000 : ℝ) (517182193143/1000000000000 : ℝ) (517182193151/1000000000000 : ℝ) (64648289703/125000000000 : ℝ) (8081036213/15625000000 : ℝ) (517186317607/1000000000000 : ℝ) (32324144851/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8957/65536 : ℝ))) 4 (64648289703/125000000000 : ℝ) (8081036213/15625000000 : ℝ) (517186317607/1000000000000 : ℝ) (32324144851/62500000000 : ℝ) (103437263523/200000000000 : ℝ) (64648289703/125000000000 : ℝ) (103437263523/200000000000 : ℝ) (64648289703/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8957/65536 : ℝ))) 5 (103437263523/200000000000 : ℝ) (64648289703/125000000000 : ℝ) (103437263523/200000000000 : ℝ) (64648289703/125000000000 : ℝ) (103437263523/200000000000 : ℝ) (64648289703/125000000000 : ℝ) (103437263523/200000000000 : ℝ) (64648289703/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8957/65536 : ℝ))) 6 (103437263523/200000000000 : ℝ) (64648289703/125000000000 : ℝ) (103437263523/200000000000 : ℝ) (64648289703/125000000000 : ℝ) (103437263523/200000000000 : ℝ) (64648289703/125000000000 : ℝ) (103437263523/200000000000 : ℝ) (64648289703/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8957/65536 : ℝ))) 7 (103437263523/200000000000 : ℝ) (64648289703/125000000000 : ℝ) (103437263523/200000000000 : ℝ) (64648289703/125000000000 : ℝ) (103437263523/200000000000 : ℝ) (64648289703/125000000000 : ℝ) (103437263523/200000000000 : ℝ) (64648289703/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8957/65536 : ℝ)) hmem 8 (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ) (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8957/65536 : ℝ))) hcmem 8 (103437263523/200000000000 : ℝ) (64648289703/125000000000 : ℝ) (103437263523/200000000000 : ℝ) (64648289703/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8957/65536 : ℝ)) (990308736319/1000000000000 : ℝ) (495154368161/500000000000 : ℝ) (103437263523/200000000000 : ℝ) (64648289703/125000000000 : ℝ) (820344543253/1000000000000 : ℝ) (820344543271/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0346_exp_lower
  have heNumeric : (126188155339/62500000000 : ℝ)/4 ≤ Real.exp (-2734747313709/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (126188155339/62500000000 : ℝ)/4 ≤ Real.exp ((2239/16384 : ℝ)-(820344543271/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2239/16384 : ℝ) (8957/65536 : ℝ) (820344543271/1000000000000 : ℝ) (126188155339/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0347; no trusted numerical premise.
theorem cover7_leaf0347_exp_radius : (498781057593230727/500000000000000000 : ℝ) ≤ Real.exp ((-4479/229376 : ℝ)/8) ∧ Real.exp ((-4479/229376 : ℝ)/8) ≤ (199512423037292291/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4479/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0347_exp_lower : (459044543117199267/500000000000000000 : ℝ) ≤ Real.exp ((-10938988702947/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938988702947/16000000000000 : ℝ)/8) ≤ (183617817246879707/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938988702947/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0347_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009505277533/500000000000 : ℝ) ≤ 4*Real.exp (8957/65536 : ℝ)*Real.exp (-mu (radius 7 (4479/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009505277533/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4479/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0347_exp_radius
  have hrNumeric : (980662524479/1000000000000 : ℝ) ≤ Real.exp (-4479/229376 : ℝ) ∧ Real.exp (-4479/229376 : ℝ) ≤ (3064570389/3125000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980662524479/1000000000000 : ℝ) ≤ (radius 7 (4479/32768 : ℝ)) ∧ (radius 7 (4479/32768 : ℝ)) ≤ (3064570389/3125000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4479/32768 : ℝ)) (980662524479/1000000000000 : ℝ) (3064570389/3125000000 : ℝ) (19570644619/100000000000 : ℝ) (48926611549/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4479/32768 : ℝ)) (980662524479/1000000000000 : ℝ) (3064570389/3125000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4479/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980662524479/1000000000000 : ℝ) (3064570389/3125000000 : ℝ) (990331262239/1000000000000 : ℝ) (6189570389/6250000000 : ℝ) (495142031259/500000000000 : ℝ) (24757101563/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4479/32768 : ℝ)) 1 (990331262239/1000000000000 : ℝ) (6189570389/6250000000 : ℝ) (495142031259/500000000000 : ℝ) (24757101563/25000000000 : ℝ) (495153831189/500000000000 : ℝ) (49515383119/50000000000 : ℝ) (990307662097/1000000000000 : ℝ) (990307662099/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4479/32768 : ℝ)) 2 (495153831189/500000000000 : ℝ) (49515383119/50000000000 : ℝ) (990307662097/1000000000000 : ℝ) (990307662099/1000000000000 : ℝ) (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ) (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4479/32768 : ℝ)) 3 (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ) (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ) (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ) (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4479/32768 : ℝ)) 4 (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ) (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ) (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ) (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4479/32768 : ℝ)) 5 (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ) (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ) (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ) (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4479/32768 : ℝ)) 6 (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ) (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ) (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ) (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4479/32768 : ℝ)) 7 (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ) (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ) (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ) (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4479/32768 : ℝ))) (19570644619/100000000000 : ℝ) (48926611549/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4479/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19570644619/100000000000 : ℝ) (48926611549/250000000000 : ℝ) (119570644619/200000000000 : ℝ) (298926611549/500000000000 : ℝ) (442387212959/1000000000000 : ℝ) (442387212967/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4479/32768 : ℝ))) 1 (119570644619/200000000000 : ℝ) (298926611549/500000000000 : ℝ) (442387212959/1000000000000 : ℝ) (442387212967/1000000000000 : ℝ) (520120218027/1000000000000 : ℝ) (520120218033/1000000000000 : ℝ) (514278738743/1000000000000 : ℝ) (411422991/800000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4479/32768 : ℝ))) 2 (520120218027/1000000000000 : ℝ) (520120218033/1000000000000 : ℝ) (514278738743/1000000000000 : ℝ) (411422991/800000000 : ℝ) (103439895677/200000000000 : ℝ) (64649934799/125000000000 : ℝ) (64648903911/125000000000 : ℝ) (103438246259/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4479/32768 : ℝ))) 3 (103439895677/200000000000 : ℝ) (64649934799/125000000000 : ℝ) (64648903911/125000000000 : ℝ) (103438246259/200000000000 : ℝ) (129298838709/250000000000 : ℝ) (129298838711/250000000000 : ℝ) (25859767741/50000000000 : ℝ) (129298838707/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4479/32768 : ℝ))) 4 (129298838709/250000000000 : ℝ) (129298838711/250000000000 : ℝ) (25859767741/50000000000 : ℝ) (129298838707/250000000000 : ℝ) (129298838707/250000000000 : ℝ) (129298838709/250000000000 : ℝ) (517195354827/1000000000000 : ℝ) (129298838709/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4479/32768 : ℝ))) 5 (129298838707/250000000000 : ℝ) (129298838709/250000000000 : ℝ) (517195354827/1000000000000 : ℝ) (129298838709/250000000000 : ℝ) (517195354827/1000000000000 : ℝ) (129298838709/250000000000 : ℝ) (517195354827/1000000000000 : ℝ) (129298838709/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4479/32768 : ℝ))) 6 (517195354827/1000000000000 : ℝ) (129298838709/250000000000 : ℝ) (517195354827/1000000000000 : ℝ) (129298838709/250000000000 : ℝ) (517195354827/1000000000000 : ℝ) (129298838709/250000000000 : ℝ) (517195354827/1000000000000 : ℝ) (129298838709/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4479/32768 : ℝ))) 7 (517195354827/1000000000000 : ℝ) (129298838709/250000000000 : ℝ) (517195354827/1000000000000 : ℝ) (129298838709/250000000000 : ℝ) (517195354827/1000000000000 : ℝ) (129298838709/250000000000 : ℝ) (517195354827/1000000000000 : ℝ) (129298838709/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4479/32768 : ℝ)) hmem 8 (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ) (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4479/32768 : ℝ))) hcmem 8 (517195354827/1000000000000 : ℝ) (129298838709/250000000000 : ℝ) (517195354827/1000000000000 : ℝ) (129298838709/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4479/32768 : ℝ)) (990307662237/1000000000000 : ℝ) (6189422889/6250000000 : ℝ) (517195354827/1000000000000 : ℝ) (129298838709/250000000000 : ℝ) (820359767549/1000000000000 : ℝ) (820359767567/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0347_exp_lower
  have heNumeric : (1009505277533/500000000000 : ℝ)/4 ≤ Real.exp (-10938988702947/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009505277533/500000000000 : ℝ)/4 ≤ Real.exp ((8957/65536 : ℝ)-(820359767567/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8957/65536 : ℝ) (4479/32768 : ℝ) (820359767567/1000000000000 : ℝ) (1009505277533/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0348; no trusted numerical premise.
theorem cover7_leaf0348_exp_radius : (199512368674478653/200000000000000000 : ℝ) ≤ Real.exp ((-8959/458752 : ℝ)/8) ∧ Real.exp ((-8959/458752 : ℝ)/8) ≤ (498780921686196633/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8959/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0348_exp_lower : (918089090323689267/1000000000000000000 : ℝ) ≤ Real.exp ((-5469494066409/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469494066409/8000000000000 : ℝ)/8) ≤ (229522272580922317/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469494066409/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0348_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201901062701/100000000000 : ℝ) ≤ 4*Real.exp (4479/32768 : ℝ)*Real.exp (-mu (radius 7 (8959/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (201901062701/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8959/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0348_exp_radius
  have hrNumeric : (980660386807/1000000000000 : ℝ) ≤ Real.exp (-8959/458752 : ℝ) ∧ Real.exp (-8959/458752 : ℝ) ≤ (122582548351/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980660386807/1000000000000 : ℝ) ≤ (radius 7 (8959/65536 : ℝ)) ∧ (radius 7 (8959/65536 : ℝ)) ≤ (122582548351/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8959/65536 : ℝ)) (980660386807/1000000000000 : ℝ) (122582548351/125000000000 : ℝ) (97858578757/500000000000 : ℝ) (2446464469/12500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8959/65536 : ℝ)) (980660386807/1000000000000 : ℝ) (122582548351/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8959/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980660386807/1000000000000 : ℝ) (122582548351/125000000000 : ℝ) (990330193403/1000000000000 : ℝ) (247582548351/250000000000 : ℝ) (198056596639/200000000000 : ℝ) (990282983197/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8959/65536 : ℝ)) 1 (990330193403/1000000000000 : ℝ) (247582548351/250000000000 : ℝ) (198056596639/200000000000 : ℝ) (990282983197/1000000000000 : ℝ) (990306588299/1000000000000 : ℝ) (990306588301/1000000000000 : ℝ) (990306588017/1000000000000 : ℝ) (49515329401/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8959/65536 : ℝ)) 2 (990306588299/1000000000000 : ℝ) (990306588301/1000000000000 : ℝ) (990306588017/1000000000000 : ℝ) (49515329401/50000000000 : ℝ) (495153294079/500000000000 : ℝ) (990306588161/1000000000000 : ℝ) (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8959/65536 : ℝ)) 3 (495153294079/500000000000 : ℝ) (990306588161/1000000000000 : ℝ) (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ) (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ) (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8959/65536 : ℝ)) 4 (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ) (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ) (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ) (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8959/65536 : ℝ)) 5 (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ) (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ) (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ) (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8959/65536 : ℝ)) 6 (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ) (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ) (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ) (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8959/65536 : ℝ)) 7 (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ) (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ) (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ) (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8959/65536 : ℝ))) (97858578757/500000000000 : ℝ) (2446464469/12500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8959/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97858578757/500000000000 : ℝ) (2446464469/12500000000 : ℝ) (597858578757/1000000000000 : ℝ) (14946464469/25000000000 : ℝ) (44239931907/100000000000 : ℝ) (221199659539/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8959/65536 : ℝ))) 1 (597858578757/1000000000000 : ℝ) (14946464469/25000000000 : ℝ) (44239931907/100000000000 : ℝ) (221199659539/500000000000 : ℝ) (520128948913/1000000000000 : ℝ) (520128948919/1000000000000 : ℝ) (257144039471/500000000000 : ℝ) (514288078949/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8959/65536 : ℝ))) 2 (520128948913/1000000000000 : ℝ) (520128948919/1000000000000 : ℝ) (257144039471/500000000000 : ℝ) (514288078949/1000000000000 : ℝ) (517208513927/1000000000000 : ℝ) (258604256967/500000000000 : ℝ) (103440053739/200000000000 : ℝ) (258600134351/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8959/65536 : ℝ))) 3 (517208513927/1000000000000 : ℝ) (258604256967/500000000000 : ℝ) (103440053739/200000000000 : ℝ) (258600134351/500000000000 : ℝ) (517204391311/1000000000000 : ℝ) (258602195659/500000000000 : ℝ) (258602195647/500000000000 : ℝ) (258602195651/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8959/65536 : ℝ))) 4 (517204391311/1000000000000 : ℝ) (258602195659/500000000000 : ℝ) (258602195647/500000000000 : ℝ) (258602195651/500000000000 : ℝ) (258602195651/500000000000 : ℝ) (51720439131/100000000000 : ℝ) (258602195651/500000000000 : ℝ) (51720439131/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8959/65536 : ℝ))) 5 (258602195651/500000000000 : ℝ) (51720439131/100000000000 : ℝ) (258602195651/500000000000 : ℝ) (51720439131/100000000000 : ℝ) (258602195651/500000000000 : ℝ) (51720439131/100000000000 : ℝ) (258602195651/500000000000 : ℝ) (51720439131/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8959/65536 : ℝ))) 6 (258602195651/500000000000 : ℝ) (51720439131/100000000000 : ℝ) (258602195651/500000000000 : ℝ) (51720439131/100000000000 : ℝ) (258602195651/500000000000 : ℝ) (51720439131/100000000000 : ℝ) (258602195651/500000000000 : ℝ) (51720439131/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8959/65536 : ℝ))) 7 (258602195651/500000000000 : ℝ) (51720439131/100000000000 : ℝ) (258602195651/500000000000 : ℝ) (51720439131/100000000000 : ℝ) (258602195651/500000000000 : ℝ) (51720439131/100000000000 : ℝ) (258602195651/500000000000 : ℝ) (51720439131/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8959/65536 : ℝ)) hmem 8 (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ) (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8959/65536 : ℝ))) hcmem 8 (258602195651/500000000000 : ℝ) (51720439131/100000000000 : ℝ) (258602195651/500000000000 : ℝ) (51720439131/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8959/65536 : ℝ)) (990306588157/1000000000000 : ℝ) (990306588161/1000000000000 : ℝ) (258602195651/500000000000 : ℝ) (51720439131/100000000000 : ℝ) (410187495353/500000000000 : ℝ) (820374990723/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0348_exp_lower
  have heNumeric : (201901062701/100000000000 : ℝ)/4 ≤ Real.exp (-5469494066409/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201901062701/100000000000 : ℝ)/4 ≤ Real.exp ((4479/32768 : ℝ)-(820374990723/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4479/32768 : ℝ) (8959/65536 : ℝ) (820374990723/1000000000000 : ℝ) (201901062701/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0349; no trusted numerical premise.
theorem cover7_leaf0349_exp_radius : (997561571558399139/1000000000000000000 : ℝ) ≤ Real.exp ((-5/256 : ℝ)/8) ∧ Real.exp ((-5/256 : ℝ)/8) ≤ (49878078577919957/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5/256 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0349_exp_lower : (459044547271100529/500000000000000000 : ℝ) ≤ Real.exp ((-10938987544673/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938987544673/16000000000000 : ℝ)/8) ≤ (918089094542201059/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938987544673/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0349_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019010701227/1000000000000 : ℝ) ≤ 4*Real.exp (8959/65536 : ℝ)*Real.exp (-mu (radius 7 (35/256 : ℝ))) ∧ (2019/1000 : ℝ) < (2019010701227/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (35/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0349_exp_radius
  have hrNumeric : (980658249139/1000000000000 : ℝ) ≤ Real.exp (-5/256 : ℝ) ∧ Real.exp (-5/256 : ℝ) ≤ (49032912457/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980658249139/1000000000000 : ℝ) ≤ (radius 7 (35/256 : ℝ)) ∧ (radius 7 (35/256 : ℝ)) ≤ (49032912457/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (35/256 : ℝ)) (980658249139/1000000000000 : ℝ) (49032912457/50000000000 : ℝ) (195727868209/1000000000000 : ℝ) (39145573643/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (35/256 : ℝ)) (980658249139/1000000000000 : ℝ) (49032912457/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (35/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980658249139/1000000000000 : ℝ) (49032912457/50000000000 : ℝ) (990329124569/1000000000000 : ℝ) (99032912457/100000000000 : ℝ) (990281903873/1000000000000 : ℝ) (495140951937/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (35/256 : ℝ)) 1 (990329124569/1000000000000 : ℝ) (99032912457/100000000000 : ℝ) (990281903873/1000000000000 : ℝ) (495140951937/500000000000 : ℝ) (990305514221/1000000000000 : ℝ) (495152757111/500000000000 : ℝ) (990305513939/1000000000000 : ℝ) (990305513941/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (35/256 : ℝ)) 2 (990305514221/1000000000000 : ℝ) (495152757111/500000000000 : ℝ) (990305513939/1000000000000 : ℝ) (990305513941/1000000000000 : ℝ) (6189409463/6250000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (35/256 : ℝ)) 3 (6189409463/6250000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (35/256 : ℝ)) 4 (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (35/256 : ℝ)) 5 (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (35/256 : ℝ)) 6 (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (35/256 : ℝ)) 7 (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (35/256 : ℝ))) (195727868209/1000000000000 : ℝ) (39145573643/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (35/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195727868209/1000000000000 : ℝ) (39145573643/200000000000 : ℝ) (74732991763/125000000000 : ℝ) (149465983527/250000000000 : ℝ) (442411424139/1000000000000 : ℝ) (442411424147/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (35/256 : ℝ))) 1 (74732991763/125000000000 : ℝ) (149465983527/250000000000 : ℝ) (442411424139/1000000000000 : ℝ) (442411424147/1000000000000 : ℝ) (520137679121/1000000000000 : ℝ) (65017209891/125000000000 : ℝ) (128574354589/250000000000 : ℝ) (128574354591/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (35/256 : ℝ))) 2 (520137679121/1000000000000 : ℝ) (65017209891/125000000000 : ℝ) (128574354589/250000000000 : ℝ) (128574354591/250000000000 : ℝ) (258608774369/500000000000 : ℝ) (258608774373/500000000000 : ℝ) (51720930537/100000000000 : ℝ) (258604652689/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (35/256 : ℝ))) 3 (258608774369/500000000000 : ℝ) (258608774373/500000000000 : ℝ) (51720930537/100000000000 : ℝ) (258604652689/500000000000 : ℝ) (258606713527/500000000000 : ℝ) (258606713531/500000000000 : ℝ) (517213427037/1000000000000 : ℝ) (258606713523/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (35/256 : ℝ))) 4 (258606713527/500000000000 : ℝ) (258606713531/500000000000 : ℝ) (517213427037/1000000000000 : ℝ) (258606713523/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (35/256 : ℝ))) 5 (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (35/256 : ℝ))) 6 (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (35/256 : ℝ))) 7 (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (35/256 : ℝ)) hmem 8 (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (35/256 : ℝ))) hcmem 8 (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (35/256 : ℝ)) (990305514079/1000000000000 : ℝ) (495152757041/500000000000 : ℝ) (103442685409/200000000000 : ℝ) (258606713527/500000000000 : ℝ) (164078042547/200000000000 : ℝ) (820390212753/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0349_exp_lower
  have heNumeric : (2019010701227/1000000000000 : ℝ)/4 ≤ Real.exp (-10938987544673/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019010701227/1000000000000 : ℝ)/4 ≤ Real.exp ((8959/65536 : ℝ)-(820390212753/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8959/65536 : ℝ) (35/256 : ℝ) (820390212753/1000000000000 : ℝ) (2019010701227/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0325_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0325_certificate
#check SmaleRate.Proofs.cover7_leaf0326_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0326_certificate
#check SmaleRate.Proofs.cover7_leaf0327_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0327_certificate
#check SmaleRate.Proofs.cover7_leaf0328_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0328_certificate
#check SmaleRate.Proofs.cover7_leaf0329_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0329_certificate
#check SmaleRate.Proofs.cover7_leaf0330_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0330_certificate
#check SmaleRate.Proofs.cover7_leaf0331_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0331_certificate
#check SmaleRate.Proofs.cover7_leaf0332_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0332_certificate
#check SmaleRate.Proofs.cover7_leaf0333_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0333_certificate
#check SmaleRate.Proofs.cover7_leaf0334_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0334_certificate
#check SmaleRate.Proofs.cover7_leaf0335_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0335_certificate
#check SmaleRate.Proofs.cover7_leaf0336_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0336_certificate
#check SmaleRate.Proofs.cover7_leaf0337_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0337_certificate
#check SmaleRate.Proofs.cover7_leaf0338_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0338_certificate
#check SmaleRate.Proofs.cover7_leaf0339_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0339_certificate
#check SmaleRate.Proofs.cover7_leaf0340_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0340_certificate
#check SmaleRate.Proofs.cover7_leaf0341_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0341_certificate
#check SmaleRate.Proofs.cover7_leaf0342_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0342_certificate
#check SmaleRate.Proofs.cover7_leaf0343_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0343_certificate
#check SmaleRate.Proofs.cover7_leaf0344_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0344_certificate
#check SmaleRate.Proofs.cover7_leaf0345_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0345_certificate
#check SmaleRate.Proofs.cover7_leaf0346_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0346_certificate
#check SmaleRate.Proofs.cover7_leaf0347_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0347_certificate
#check SmaleRate.Proofs.cover7_leaf0348_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0348_certificate
#check SmaleRate.Proofs.cover7_leaf0349_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0349_certificate
