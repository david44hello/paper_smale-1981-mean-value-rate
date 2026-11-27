/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0575; no trusted numerical premise.
theorem cover8_leaf0575_exp_radius : (998015706136788851/1000000000000000000 : ℝ) ≤ Real.exp ((-8331/524288 : ℝ)/8) ∧ Real.exp ((-8331/524288 : ℝ)/8) ≤ (249503926534197213/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8331/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0575_exp_lower : (920113538117648083/1000000000000000000 : ℝ) ≤ Real.exp ((-17051280497893/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051280497893/25600000000000 : ℝ)/8) ≤ (230028384529412021/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051280497893/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0575_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903147507/1000000000000 : ℝ) ≤ 4*Real.exp (66647/524288 : ℝ)*Real.exp (-mu (radius 8 (8331/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903147507/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8331/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0575_exp_radius
  have hrNumeric : (984235460469/1000000000000 : ℝ) ≤ Real.exp (-8331/524288 : ℝ) ∧ Real.exp (-8331/524288 : ℝ) ≤ (98423546047/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984235460469/1000000000000 : ℝ) ≤ (radius 8 (8331/65536 : ℝ)) ∧ (radius 8 (8331/65536 : ℝ)) ≤ (98423546047/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8331/65536 : ℝ)) (984235460469/1000000000000 : ℝ) (98423546047/100000000000 : ℝ) (44215776563/250000000000 : ℝ) (176863106259/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8331/65536 : ℝ)) (984235460469/1000000000000 : ℝ) (98423546047/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8331/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984235460469/1000000000000 : ℝ) (98423546047/100000000000 : ℝ) (496058865117/500000000000 : ℝ) (198423546047/200000000000 : ℝ) (992086417843/1000000000000 : ℝ) (248021604461/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8331/65536 : ℝ)) 1 (496058865117/500000000000 : ℝ) (198423546047/200000000000 : ℝ) (992086417843/1000000000000 : ℝ) (248021604461/250000000000 : ℝ) (496051037019/500000000000 : ℝ) (24802551851/25000000000 : ℝ) (496051036957/500000000000 : ℝ) (248025518479/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8331/65536 : ℝ)) 2 (496051037019/500000000000 : ℝ) (24802551851/25000000000 : ℝ) (496051036957/500000000000 : ℝ) (248025518479/250000000000 : ℝ) (124012759247/125000000000 : ℝ) (496051036989/500000000000 : ℝ) (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8331/65536 : ℝ)) 3 (124012759247/125000000000 : ℝ) (496051036989/500000000000 : ℝ) (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ) (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ) (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8331/65536 : ℝ)) 4 (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ) (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ) (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ) (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8331/65536 : ℝ)) 5 (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ) (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ) (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ) (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8331/65536 : ℝ)) 6 (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ) (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ) (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ) (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8331/65536 : ℝ)) 7 (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ) (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ) (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ) (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8331/65536 : ℝ))) (44215776563/250000000000 : ℝ) (176863106259/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8331/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44215776563/250000000000 : ℝ) (176863106259/1000000000000 : ℝ) (294215776563/500000000000 : ℝ) (58843155313/100000000000 : ℝ) (84110191119/200000000000 : ℝ) (105137738901/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8331/65536 : ℝ))) 1 (294215776563/500000000000 : ℝ) (58843155313/100000000000 : ℝ) (84110191119/200000000000 : ℝ) (105137738901/250000000000 : ℝ) (12612281359/25000000000 : ℝ) (504491254367/1000000000000 : ℝ) (7772796801/15625000000 : ℝ) (62182374409/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8331/65536 : ℝ))) 2 (12612281359/25000000000 : ℝ) (504491254367/1000000000000 : ℝ) (7772796801/15625000000 : ℝ) (62182374409/125000000000 : ℝ) (125243781203/250000000000 : ℝ) (25048756241/50000000000 : ℝ) (500962785557/1000000000000 : ℝ) (100192557113/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8331/65536 : ℝ))) 3 (125243781203/250000000000 : ℝ) (25048756241/50000000000 : ℝ) (500962785557/1000000000000 : ℝ) (100192557113/200000000000 : ℝ) (31310559699/62500000000 : ℝ) (500968955193/1000000000000 : ℝ) (250484477573/500000000000 : ℝ) (100193791031/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8331/65536 : ℝ))) 4 (31310559699/62500000000 : ℝ) (500968955193/1000000000000 : ℝ) (250484477573/500000000000 : ℝ) (100193791031/200000000000 : ℝ) (100193791033/200000000000 : ℝ) (250484477587/500000000000 : ℝ) (125242238791/250000000000 : ℝ) (250484477587/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8331/65536 : ℝ))) 5 (100193791033/200000000000 : ℝ) (250484477587/500000000000 : ℝ) (125242238791/250000000000 : ℝ) (250484477587/500000000000 : ℝ) (125242238791/250000000000 : ℝ) (250484477587/500000000000 : ℝ) (125242238791/250000000000 : ℝ) (250484477587/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8331/65536 : ℝ))) 6 (125242238791/250000000000 : ℝ) (250484477587/500000000000 : ℝ) (125242238791/250000000000 : ℝ) (250484477587/500000000000 : ℝ) (125242238791/250000000000 : ℝ) (250484477587/500000000000 : ℝ) (125242238791/250000000000 : ℝ) (250484477587/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8331/65536 : ℝ))) 7 (125242238791/250000000000 : ℝ) (250484477587/500000000000 : ℝ) (125242238791/250000000000 : ℝ) (250484477587/500000000000 : ℝ) (125242238791/250000000000 : ℝ) (250484477587/500000000000 : ℝ) (125242238791/250000000000 : ℝ) (250484477587/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8331/65536 : ℝ)) hmem 8 (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ) (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8331/65536 : ℝ))) hcmem 8 (125242238791/250000000000 : ℝ) (250484477587/500000000000 : ℝ) (125242238791/250000000000 : ℝ) (250484477587/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8331/65536 : ℝ)) (39684082959/40000000000 : ℝ) (496051036989/500000000000 : ℝ) (125242238791/250000000000 : ℝ) (250484477587/500000000000 : ℝ) (793184708761/1000000000000 : ℝ) (39659235439/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0575_exp_lower
  have heNumeric : (2054903147507/1000000000000 : ℝ)/4 ≤ Real.exp (-17051280497893/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903147507/1000000000000 : ℝ)/4 ≤ Real.exp ((66647/524288 : ℝ)-(39659235439/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66647/524288 : ℝ) (8331/65536 : ℝ) (39659235439/50000000000 : ℝ) (2054903147507/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0576; no trusted numerical premise.
theorem cover8_leaf0576_exp_radius : (62375979774600217/62500000000000000 : ℝ) ≤ Real.exp ((-66649/4194304 : ℝ)/8) ∧ Real.exp ((-66649/4194304 : ℝ)/8) ≤ (998015676393603473/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66649/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0576_exp_lower : (920113537482727511/1000000000000000000 : ℝ) ≤ Real.exp ((-10657050399509/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657050399509/16000000000000 : ℝ)/8) ≤ (115014192185340939/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657050399509/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0576_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903136163/1000000000000 : ℝ) ≤ 4*Real.exp (8331/65536 : ℝ)*Real.exp (-mu (radius 8 (66649/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903136163/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66649/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0576_exp_radius
  have hrNumeric : (984235225809/1000000000000 : ℝ) ≤ Real.exp (-66649/4194304 : ℝ) ∧ Real.exp (-66649/4194304 : ℝ) ≤ (98423522581/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984235225809/1000000000000 : ℝ) ≤ (radius 8 (66649/524288 : ℝ)) ∧ (radius 8 (66649/524288 : ℝ)) ≤ (98423522581/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66649/524288 : ℝ)) (984235225809/1000000000000 : ℝ) (98423522581/100000000000 : ℝ) (4421610303/25000000000 : ℝ) (176864412127/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66649/524288 : ℝ)) (984235225809/1000000000000 : ℝ) (98423522581/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66649/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984235225809/1000000000000 : ℝ) (98423522581/100000000000 : ℝ) (124014701613/125000000000 : ℝ) (198423522581/200000000000 : ℝ) (992086299577/1000000000000 : ℝ) (496043149789/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66649/524288 : ℝ)) 1 (124014701613/125000000000 : ℝ) (198423522581/200000000000 : ℝ) (992086299577/1000000000000 : ℝ) (496043149789/500000000000 : ℝ) (12401274453/12500000000 : ℝ) (496050978121/500000000000 : ℝ) (248025489029/250000000000 : ℝ) (496050978059/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66649/524288 : ℝ)) 2 (12401274453/12500000000 : ℝ) (496050978121/500000000000 : ℝ) (248025489029/250000000000 : ℝ) (496050978059/500000000000 : ℝ) (496050978089/500000000000 : ℝ) (49605097809/50000000000 : ℝ) (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66649/524288 : ℝ)) 3 (496050978089/500000000000 : ℝ) (49605097809/50000000000 : ℝ) (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ) (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ) (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66649/524288 : ℝ)) 4 (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ) (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ) (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ) (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66649/524288 : ℝ)) 5 (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ) (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ) (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ) (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66649/524288 : ℝ)) 6 (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ) (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ) (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ) (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66649/524288 : ℝ)) 7 (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ) (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ) (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ) (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66649/524288 : ℝ))) (4421610303/25000000000 : ℝ) (176864412127/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66649/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4421610303/25000000000 : ℝ) (176864412127/1000000000000 : ℝ) (29421610303/50000000000 : ℝ) (36777012879/62500000000 : ℝ) (328556647/781250000 : ℝ) (420552508169/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66649/524288 : ℝ))) 1 (29421610303/50000000000 : ℝ) (36777012879/62500000000 : ℝ) (328556647/781250000 : ℝ) (420552508169/1000000000000 : ℝ) (50449235711/100000000000 : ℝ) (504492357117/1000000000000 : ℝ) (497460189503/1000000000000 : ℝ) (497460189511/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66649/524288 : ℝ))) 2 (50449235711/100000000000 : ℝ) (504492357117/1000000000000 : ℝ) (497460189503/1000000000000 : ℝ) (497460189511/1000000000000 : ℝ) (250488136653/500000000000 : ℝ) (250488136657/500000000000 : ℝ) (500963934401/1000000000000 : ℝ) (500963934409/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66649/524288 : ℝ))) 3 (250488136653/500000000000 : ℝ) (250488136657/500000000000 : ℝ) (500963934401/1000000000000 : ℝ) (500963934409/1000000000000 : ℝ) (500970103853/1000000000000 : ℝ) (250485051931/500000000000 : ℝ) (100194020763/200000000000 : ℝ) (31310631489/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66649/524288 : ℝ))) 4 (500970103853/1000000000000 : ℝ) (250485051931/500000000000 : ℝ) (100194020763/200000000000 : ℝ) (31310631489/62500000000 : ℝ) (250485051917/500000000000 : ℝ) (500970103843/1000000000000 : ℝ) (500970103833/1000000000000 : ℝ) (500970103843/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66649/524288 : ℝ))) 5 (250485051917/500000000000 : ℝ) (500970103843/1000000000000 : ℝ) (500970103833/1000000000000 : ℝ) (500970103843/1000000000000 : ℝ) (500970103833/1000000000000 : ℝ) (500970103843/1000000000000 : ℝ) (500970103833/1000000000000 : ℝ) (500970103843/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66649/524288 : ℝ))) 6 (500970103833/1000000000000 : ℝ) (500970103843/1000000000000 : ℝ) (500970103833/1000000000000 : ℝ) (500970103843/1000000000000 : ℝ) (500970103833/1000000000000 : ℝ) (500970103843/1000000000000 : ℝ) (500970103833/1000000000000 : ℝ) (500970103843/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66649/524288 : ℝ))) 7 (500970103833/1000000000000 : ℝ) (500970103843/1000000000000 : ℝ) (500970103833/1000000000000 : ℝ) (500970103843/1000000000000 : ℝ) (500970103833/1000000000000 : ℝ) (500970103843/1000000000000 : ℝ) (500970103833/1000000000000 : ℝ) (500970103843/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66649/524288 : ℝ)) hmem 8 (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ) (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66649/524288 : ℝ))) hcmem 8 (500970103833/1000000000000 : ℝ) (500970103843/1000000000000 : ℝ) (500970103833/1000000000000 : ℝ) (500970103843/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66649/524288 : ℝ)) (992101956177/1000000000000 : ℝ) (49605097809/50000000000 : ℝ) (500970103833/1000000000000 : ℝ) (500970103843/1000000000000 : ℝ) (79318662163/100000000000 : ℝ) (793186621649/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0576_exp_lower
  have heNumeric : (2054903136163/1000000000000 : ℝ)/4 ≤ Real.exp (-10657050399509/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903136163/1000000000000 : ℝ)/4 ≤ Real.exp ((8331/65536 : ℝ)-(793186621649/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8331/65536 : ℝ) (66649/524288 : ℝ) (793186621649/1000000000000 : ℝ) (2054903136163/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0577; no trusted numerical premise.
theorem cover8_leaf0577_exp_radius : (998015646650418979/1000000000000000000 : ℝ) ≤ Real.exp ((-33325/2097152 : ℝ)/8) ∧ Real.exp ((-33325/2097152 : ℝ)/8) ≤ (49900782332520949/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33325/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0577_exp_lower : (230028384212555559/250000000000000000 : ℝ) ≤ Real.exp ((-85256403899991/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256403899991/128000000000000 : ℝ)/8) ≤ (920113536850222237/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256403899991/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0577_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903124863/1000000000000 : ℝ) ≤ 4*Real.exp (66649/524288 : ℝ)*Real.exp (-mu (radius 8 (33325/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903124863/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33325/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0577_exp_radius
  have hrNumeric : (984234991149/1000000000000 : ℝ) ≤ Real.exp (-33325/2097152 : ℝ) ∧ Real.exp (-33325/2097152 : ℝ) ≤ (19684699823/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984234991149/1000000000000 : ℝ) ≤ (radius 8 (33325/262144 : ℝ)) ∧ (radius 8 (33325/262144 : ℝ)) ≤ (19684699823/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33325/262144 : ℝ)) (984234991149/1000000000000 : ℝ) (19684699823/20000000000 : ℝ) (88432858989/500000000000 : ℝ) (5527053687/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33325/262144 : ℝ)) (984234991149/1000000000000 : ℝ) (19684699823/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33325/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984234991149/1000000000000 : ℝ) (19684699823/20000000000 : ℝ) (496058747787/500000000000 : ℝ) (39684699823/40000000000 : ℝ) (992086181311/1000000000000 : ℝ) (15501346583/15625000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33325/262144 : ℝ)) 1 (496058747787/500000000000 : ℝ) (39684699823/40000000000 : ℝ) (992086181311/1000000000000 : ℝ) (15501346583/15625000000 : ℝ) (496050919221/500000000000 : ℝ) (248025459611/250000000000 : ℝ) (496050919159/500000000000 : ℝ) (12401272979/12500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33325/262144 : ℝ)) 2 (496050919221/500000000000 : ℝ) (248025459611/250000000000 : ℝ) (496050919159/500000000000 : ℝ) (12401272979/12500000000 : ℝ) (49605091919/50000000000 : ℝ) (496050919191/500000000000 : ℝ) (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33325/262144 : ℝ)) 3 (49605091919/50000000000 : ℝ) (496050919191/500000000000 : ℝ) (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ) (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ) (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33325/262144 : ℝ)) 4 (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ) (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ) (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ) (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33325/262144 : ℝ)) 5 (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ) (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ) (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ) (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33325/262144 : ℝ)) 6 (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ) (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ) (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ) (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33325/262144 : ℝ)) 7 (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ) (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ) (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ) (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33325/262144 : ℝ))) (88432858989/500000000000 : ℝ) (5527053687/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33325/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88432858989/500000000000 : ℝ) (5527053687/31250000000 : ℝ) (588432858989/1000000000000 : ℝ) (36777053687/62500000000 : ℝ) (105138515177/250000000000 : ℝ) (105138515179/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33325/262144 : ℝ))) 1 (588432858989/1000000000000 : ℝ) (36777053687/62500000000 : ℝ) (105138515177/250000000000 : ℝ) (105138515179/250000000000 : ℝ) (63061682481/125000000000 : ℝ) (252246729927/500000000000 : ℝ) (497461383729/1000000000000 : ℝ) (62182672967/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33325/262144 : ℝ))) 2 (63061682481/125000000000 : ℝ) (252246729927/500000000000 : ℝ) (497461383729/1000000000000 : ℝ) (62182672967/125000000000 : ℝ) (125244355447/250000000000 : ℝ) (100195484359/200000000000 : ℝ) (15655158851/31250000000 : ℝ) (12524127081/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33325/262144 : ℝ))) 3 (125244355447/250000000000 : ℝ) (100195484359/200000000000 : ℝ) (15655158851/31250000000 : ℝ) (12524127081/25000000000 : ℝ) (50097125251/100000000000 : ℝ) (250485626259/500000000000 : ℝ) (62621406559/125000000000 : ℝ) (391383791/781250000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33325/262144 : ℝ))) 4 (50097125251/100000000000 : ℝ) (250485626259/500000000000 : ℝ) (62621406559/125000000000 : ℝ) (391383791/781250000 : ℝ) (500971252491/1000000000000 : ℝ) (500971252499/1000000000000 : ℝ) (50097125249/100000000000 : ℝ) (500971252499/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33325/262144 : ℝ))) 5 (500971252491/1000000000000 : ℝ) (500971252499/1000000000000 : ℝ) (50097125249/100000000000 : ℝ) (500971252499/1000000000000 : ℝ) (50097125249/100000000000 : ℝ) (500971252499/1000000000000 : ℝ) (50097125249/100000000000 : ℝ) (500971252499/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33325/262144 : ℝ))) 6 (50097125249/100000000000 : ℝ) (500971252499/1000000000000 : ℝ) (50097125249/100000000000 : ℝ) (500971252499/1000000000000 : ℝ) (50097125249/100000000000 : ℝ) (500971252499/1000000000000 : ℝ) (50097125249/100000000000 : ℝ) (500971252499/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33325/262144 : ℝ))) 7 (50097125249/100000000000 : ℝ) (500971252499/1000000000000 : ℝ) (50097125249/100000000000 : ℝ) (500971252499/1000000000000 : ℝ) (50097125249/100000000000 : ℝ) (500971252499/1000000000000 : ℝ) (50097125249/100000000000 : ℝ) (500971252499/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33325/262144 : ℝ)) hmem 8 (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ) (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33325/262144 : ℝ))) hcmem 8 (50097125249/100000000000 : ℝ) (500971252499/1000000000000 : ℝ) (50097125249/100000000000 : ℝ) (500971252499/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33325/262144 : ℝ)) (992101838379/1000000000000 : ℝ) (496050919191/500000000000 : ℝ) (50097125249/100000000000 : ℝ) (500971252499/1000000000000 : ℝ) (793188534479/1000000000000 : ℝ) (793188534497/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0577_exp_lower
  have heNumeric : (2054903124863/1000000000000 : ℝ)/4 ≤ Real.exp (-85256403899991/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903124863/1000000000000 : ℝ)/4 ≤ Real.exp ((66649/524288 : ℝ)-(793188534497/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66649/524288 : ℝ) (33325/262144 : ℝ) (793188534497/1000000000000 : ℝ) (2054903124863/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0578; no trusted numerical premise.
theorem cover8_leaf0578_exp_radius : (998015616907235373/1000000000000000000 : ℝ) ≤ Real.exp ((-66651/4194304 : ℝ)/8) ∧ Real.exp ((-66651/4194304 : ℝ)/8) ≤ (499007808453617687/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66651/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0578_exp_lower : (460056768109893609/500000000000000000 : ℝ) ≤ Real.exp ((-42628202300803/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628202300803/64000000000000 : ℝ)/8) ≤ (920113536219787219/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628202300803/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0578_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903113599/1000000000000 : ℝ) ≤ 4*Real.exp (33325/262144 : ℝ)*Real.exp (-mu (radius 8 (66651/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903113599/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66651/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0578_exp_radius
  have hrNumeric : (984234756489/1000000000000 : ℝ) ≤ Real.exp (-66651/4194304 : ℝ) ∧ Real.exp (-66651/4194304 : ℝ) ≤ (98423475649/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984234756489/1000000000000 : ℝ) ≤ (radius 8 (66651/524288 : ℝ)) ∧ (radius 8 (66651/524288 : ℝ)) ≤ (98423475649/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66651/524288 : ℝ)) (984234756489/1000000000000 : ℝ) (98423475649/100000000000 : ℝ) (88433511913/500000000000 : ℝ) (22108377979/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66651/524288 : ℝ)) (984234756489/1000000000000 : ℝ) (98423475649/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66651/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984234756489/1000000000000 : ℝ) (98423475649/100000000000 : ℝ) (248029344561/250000000000 : ℝ) (198423475649/200000000000 : ℝ) (198417212609/200000000000 : ℝ) (496043031523/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66651/524288 : ℝ)) 1 (248029344561/250000000000 : ℝ) (198423475649/200000000000 : ℝ) (198417212609/200000000000 : ℝ) (496043031523/500000000000 : ℝ) (248025430161/250000000000 : ℝ) (496050860323/500000000000 : ℝ) (24802543013/25000000000 : ℝ) (496050860261/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66651/524288 : ℝ)) 2 (248025430161/250000000000 : ℝ) (496050860323/500000000000 : ℝ) (24802543013/25000000000 : ℝ) (496050860261/500000000000 : ℝ) (496050860291/500000000000 : ℝ) (124012715073/125000000000 : ℝ) (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66651/524288 : ℝ)) 3 (496050860291/500000000000 : ℝ) (124012715073/125000000000 : ℝ) (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ) (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ) (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66651/524288 : ℝ)) 4 (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ) (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ) (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ) (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66651/524288 : ℝ)) 5 (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ) (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ) (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ) (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66651/524288 : ℝ)) 6 (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ) (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ) (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ) (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66651/524288 : ℝ)) 7 (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ) (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ) (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ) (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66651/524288 : ℝ))) (88433511913/500000000000 : ℝ) (22108377979/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66651/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88433511913/500000000000 : ℝ) (22108377979/125000000000 : ℝ) (588433511913/1000000000000 : ℝ) (147108377979/250000000000 : ℝ) (210277806619/500000000000 : ℝ) (210277806623/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66651/524288 : ℝ))) 1 (588433511913/1000000000000 : ℝ) (147108377979/250000000000 : ℝ) (210277806619/500000000000 : ℝ) (210277806623/500000000000 : ℝ) (20179782503/40000000000 : ℝ) (504494562581/1000000000000 : ℝ) (497462577941/1000000000000 : ℝ) (124365644487/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66651/524288 : ℝ))) 2 (20179782503/40000000000 : ℝ) (504494562581/1000000000000 : ℝ) (497462577941/1000000000000 : ℝ) (124365644487/250000000000 : ℝ) (250489285129/500000000000 : ℝ) (100195714053/200000000000 : ℝ) (500966232051/1000000000000 : ℝ) (250483116029/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66651/524288 : ℝ))) 3 (250489285129/500000000000 : ℝ) (100195714053/200000000000 : ℝ) (500966232051/1000000000000 : ℝ) (250483116029/500000000000 : ℝ) (250486200577/500000000000 : ℝ) (250486200581/500000000000 : ℝ) (125243100279/250000000000 : ℝ) (125243100281/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66651/524288 : ℝ))) 4 (250486200577/500000000000 : ℝ) (250486200581/500000000000 : ℝ) (125243100279/250000000000 : ℝ) (125243100281/250000000000 : ℝ) (100194480227/200000000000 : ℝ) (500972401143/1000000000000 : ℝ) (250486200567/500000000000 : ℝ) (500972401143/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66651/524288 : ℝ))) 5 (100194480227/200000000000 : ℝ) (500972401143/1000000000000 : ℝ) (250486200567/500000000000 : ℝ) (500972401143/1000000000000 : ℝ) (250486200567/500000000000 : ℝ) (500972401143/1000000000000 : ℝ) (250486200567/500000000000 : ℝ) (500972401143/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66651/524288 : ℝ))) 6 (250486200567/500000000000 : ℝ) (500972401143/1000000000000 : ℝ) (250486200567/500000000000 : ℝ) (500972401143/1000000000000 : ℝ) (250486200567/500000000000 : ℝ) (500972401143/1000000000000 : ℝ) (250486200567/500000000000 : ℝ) (500972401143/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66651/524288 : ℝ))) 7 (250486200567/500000000000 : ℝ) (500972401143/1000000000000 : ℝ) (250486200567/500000000000 : ℝ) (500972401143/1000000000000 : ℝ) (250486200567/500000000000 : ℝ) (500972401143/1000000000000 : ℝ) (250486200567/500000000000 : ℝ) (500972401143/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66651/524288 : ℝ)) hmem 8 (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ) (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66651/524288 : ℝ))) hcmem 8 (250486200567/500000000000 : ℝ) (500972401143/1000000000000 : ℝ) (250486200567/500000000000 : ℝ) (500972401143/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66651/524288 : ℝ)) (992101720581/1000000000000 : ℝ) (124012715073/125000000000 : ℝ) (250486200567/500000000000 : ℝ) (500972401143/1000000000000 : ℝ) (793190447309/1000000000000 : ℝ) (793190447327/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0578_exp_lower
  have heNumeric : (2054903113599/1000000000000 : ℝ)/4 ≤ Real.exp (-42628202300803/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903113599/1000000000000 : ℝ)/4 ≤ Real.exp ((33325/262144 : ℝ)-(793190447327/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33325/262144 : ℝ) (66651/524288 : ℝ) (793190447327/1000000000000 : ℝ) (2054903113599/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0579; no trusted numerical premise.
theorem cover8_leaf0579_exp_radius : (998015587164052653/1000000000000000000 : ℝ) ≤ Real.exp ((-16663/1048576 : ℝ)/8) ∧ Real.exp ((-16663/1048576 : ℝ)/8) ≤ (499007793582026327/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16663/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0579_exp_lower : (920113535591537469/1000000000000000000 : ℝ) ≤ Real.exp ((-85256405300789/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256405300789/128000000000000 : ℝ)/8) ≤ (92011353559153747/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256405300789/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0579_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451551187/500000000000 : ℝ) ≤ 4*Real.exp (66651/524288 : ℝ)*Real.exp (-mu (radius 8 (16663/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451551187/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16663/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0579_exp_radius
  have hrNumeric : (984234521829/1000000000000 : ℝ) ≤ Real.exp (-16663/1048576 : ℝ) ∧ Real.exp (-16663/1048576 : ℝ) ≤ (98423452183/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984234521829/1000000000000 : ℝ) ≤ (radius 8 (16663/131072 : ℝ)) ∧ (radius 8 (16663/131072 : ℝ)) ≤ (98423452183/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16663/131072 : ℝ)) (984234521829/1000000000000 : ℝ) (98423452183/100000000000 : ℝ) (176868329663/1000000000000 : ℝ) (17686832967/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16663/131072 : ℝ)) (984234521829/1000000000000 : ℝ) (98423452183/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16663/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984234521829/1000000000000 : ℝ) (98423452183/100000000000 : ℝ) (496058630457/500000000000 : ℝ) (198423452183/200000000000 : ℝ) (992085944779/1000000000000 : ℝ) (49604297239/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16663/131072 : ℝ)) 1 (496058630457/500000000000 : ℝ) (198423452183/200000000000 : ℝ) (992085944779/1000000000000 : ℝ) (49604297239/50000000000 : ℝ) (496050801423/500000000000 : ℝ) (31003175089/31250000000 : ℝ) (496050801361/500000000000 : ℝ) (248025400681/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16663/131072 : ℝ)) 2 (496050801423/500000000000 : ℝ) (31003175089/31250000000 : ℝ) (496050801361/500000000000 : ℝ) (248025400681/250000000000 : ℝ) (31003175087/31250000000 : ℝ) (496050801393/500000000000 : ℝ) (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16663/131072 : ℝ)) 3 (31003175087/31250000000 : ℝ) (496050801393/500000000000 : ℝ) (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ) (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ) (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16663/131072 : ℝ)) 4 (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ) (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ) (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ) (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16663/131072 : ℝ)) 5 (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ) (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ) (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ) (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16663/131072 : ℝ)) 6 (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ) (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ) (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ) (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16663/131072 : ℝ)) 7 (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ) (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ) (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ) (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16663/131072 : ℝ))) (176868329663/1000000000000 : ℝ) (17686832967/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16663/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176868329663/1000000000000 : ℝ) (17686832967/100000000000 : ℝ) (588434164831/1000000000000 : ℝ) (117686832967/200000000000 : ℝ) (420557165749/1000000000000 : ℝ) (210278582879/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16663/131072 : ℝ))) 1 (588434164831/1000000000000 : ℝ) (117686832967/200000000000 : ℝ) (420557165749/1000000000000 : ℝ) (210278582879/500000000000 : ℝ) (50449566529/100000000000 : ℝ) (504495665297/1000000000000 : ℝ) (497463772139/1000000000000 : ℝ) (497463772147/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16663/131072 : ℝ))) 2 (50449566529/100000000000 : ℝ) (504495665297/1000000000000 : ℝ) (497463772139/1000000000000 : ℝ) (497463772147/1000000000000 : ℝ) (250489859357/500000000000 : ℝ) (250489859361/500000000000 : ℝ) (500967380857/1000000000000 : ℝ) (100193476173/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16663/131072 : ℝ))) 3 (250489859357/500000000000 : ℝ) (250489859361/500000000000 : ℝ) (500967380857/1000000000000 : ℝ) (100193476173/200000000000 : ℝ) (100194709957/200000000000 : ℝ) (250486774897/500000000000 : ℝ) (500973549747/1000000000000 : ℝ) (125243387439/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16663/131072 : ℝ))) 4 (100194709957/200000000000 : ℝ) (250486774897/500000000000 : ℝ) (500973549747/1000000000000 : ℝ) (125243387439/250000000000 : ℝ) (250486774883/500000000000 : ℝ) (20038941991/40000000000 : ℝ) (100194709953/200000000000 : ℝ) (20038941991/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16663/131072 : ℝ))) 5 (250486774883/500000000000 : ℝ) (20038941991/40000000000 : ℝ) (100194709953/200000000000 : ℝ) (20038941991/40000000000 : ℝ) (100194709953/200000000000 : ℝ) (20038941991/40000000000 : ℝ) (100194709953/200000000000 : ℝ) (20038941991/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16663/131072 : ℝ))) 6 (100194709953/200000000000 : ℝ) (20038941991/40000000000 : ℝ) (100194709953/200000000000 : ℝ) (20038941991/40000000000 : ℝ) (100194709953/200000000000 : ℝ) (20038941991/40000000000 : ℝ) (100194709953/200000000000 : ℝ) (20038941991/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16663/131072 : ℝ))) 7 (100194709953/200000000000 : ℝ) (20038941991/40000000000 : ℝ) (100194709953/200000000000 : ℝ) (20038941991/40000000000 : ℝ) (100194709953/200000000000 : ℝ) (20038941991/40000000000 : ℝ) (100194709953/200000000000 : ℝ) (20038941991/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16663/131072 : ℝ)) hmem 8 (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ) (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16663/131072 : ℝ))) hcmem 8 (100194709953/200000000000 : ℝ) (20038941991/40000000000 : ℝ) (100194709953/200000000000 : ℝ) (20038941991/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16663/131072 : ℝ)) (992101602783/1000000000000 : ℝ) (496050801393/500000000000 : ℝ) (100194709953/200000000000 : ℝ) (20038941991/40000000000 : ℝ) (793192360119/1000000000000 : ℝ) (396596180069/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0579_exp_lower
  have heNumeric : (1027451551187/500000000000 : ℝ)/4 ≤ Real.exp (-85256405300789/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451551187/500000000000 : ℝ)/4 ≤ Real.exp ((66651/524288 : ℝ)-(396596180069/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66651/524288 : ℝ) (16663/131072 : ℝ) (396596180069/500000000000 : ℝ) (1027451551187/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0580; no trusted numerical premise.
theorem cover8_leaf0580_exp_radius : (998015557420870819/1000000000000000000 : ℝ) ≤ Real.exp ((-66653/4194304 : ℝ)/8) ∧ Real.exp ((-66653/4194304 : ℝ)/8) ≤ (49900777871043541/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66653/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0580_exp_lower : (184022706993278621/200000000000000000 : ℝ) ≤ Real.exp ((-21314101499129/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314101499129/32000000000000 : ℝ)/8) ≤ (460056767483196553/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314101499129/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0580_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980618241/200000000000 : ℝ) ≤ 4*Real.exp (16663/131072 : ℝ)*Real.exp (-mu (radius 8 (66653/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980618241/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66653/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0580_exp_radius
  have hrNumeric : (98423428717/100000000000 : ℝ) ≤ Real.exp (-66653/4194304 : ℝ) ∧ Real.exp (-66653/4194304 : ℝ) ≤ (984234287171/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98423428717/100000000000 : ℝ) ≤ (radius 8 (66653/524288 : ℝ)) ∧ (radius 8 (66653/524288 : ℝ)) ≤ (984234287171/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66653/524288 : ℝ)) (98423428717/100000000000 : ℝ) (984234287171/1000000000000 : ℝ) (88434817743/500000000000 : ℝ) (44217408873/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66653/524288 : ℝ)) (98423428717/100000000000 : ℝ) (984234287171/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66653/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98423428717/100000000000 : ℝ) (984234287171/1000000000000 : ℝ) (198423428717/200000000000 : ℝ) (496058571793/500000000000 : ℝ) (496042913257/500000000000 : ℝ) (198417165303/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66653/524288 : ℝ)) 1 (198423428717/200000000000 : ℝ) (496058571793/500000000000 : ℝ) (496042913257/500000000000 : ℝ) (198417165303/200000000000 : ℝ) (992101485049/1000000000000 : ℝ) (992101485051/1000000000000 : ℝ) (39684059397/40000000000 : ℝ) (992101484927/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66653/524288 : ℝ)) 2 (992101485049/1000000000000 : ℝ) (992101485051/1000000000000 : ℝ) (39684059397/40000000000 : ℝ) (992101484927/1000000000000 : ℝ) (992101484987/1000000000000 : ℝ) (992101484989/1000000000000 : ℝ) (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66653/524288 : ℝ)) 3 (992101484987/1000000000000 : ℝ) (992101484989/1000000000000 : ℝ) (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ) (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ) (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66653/524288 : ℝ)) 4 (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ) (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ) (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ) (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66653/524288 : ℝ)) 5 (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ) (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ) (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ) (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66653/524288 : ℝ)) 6 (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ) (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ) (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ) (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66653/524288 : ℝ)) 7 (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ) (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ) (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ) (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66653/524288 : ℝ))) (88434817743/500000000000 : ℝ) (44217408873/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66653/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88434817743/500000000000 : ℝ) (44217408873/250000000000 : ℝ) (588434817743/1000000000000 : ℝ) (294217408873/500000000000 : ℝ) (210279359119/500000000000 : ℝ) (210279359123/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66653/524288 : ℝ))) 1 (588434817743/1000000000000 : ℝ) (294217408873/500000000000 : ℝ) (210279359119/500000000000 : ℝ) (210279359123/500000000000 : ℝ) (50449676799/100000000000 : ℝ) (126124191999/250000000000 : ℝ) (6218312079/12500000000 : ℝ) (497464966327/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66653/524288 : ℝ))) 2 (50449676799/100000000000 : ℝ) (126124191999/250000000000 : ℝ) (6218312079/12500000000 : ℝ) (497464966327/1000000000000 : ℝ) (100196173431/200000000000 : ℝ) (250490433581/500000000000 : ℝ) (500968529647/1000000000000 : ℝ) (250484264827/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66653/524288 : ℝ))) 3 (100196173431/200000000000 : ℝ) (250490433581/500000000000 : ℝ) (500968529647/1000000000000 : ℝ) (250484264827/500000000000 : ℝ) (500974698401/1000000000000 : ℝ) (62621837301/125000000000 : ℝ) (500974698363/1000000000000 : ℝ) (500974698371/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66653/524288 : ℝ))) 4 (500974698401/1000000000000 : ℝ) (62621837301/125000000000 : ℝ) (500974698363/1000000000000 : ℝ) (500974698371/1000000000000 : ℝ) (250487349191/500000000000 : ℝ) (50097469839/100000000000 : ℝ) (500974698381/1000000000000 : ℝ) (50097469839/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66653/524288 : ℝ))) 5 (250487349191/500000000000 : ℝ) (50097469839/100000000000 : ℝ) (500974698381/1000000000000 : ℝ) (50097469839/100000000000 : ℝ) (500974698381/1000000000000 : ℝ) (50097469839/100000000000 : ℝ) (500974698381/1000000000000 : ℝ) (50097469839/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66653/524288 : ℝ))) 6 (500974698381/1000000000000 : ℝ) (50097469839/100000000000 : ℝ) (500974698381/1000000000000 : ℝ) (50097469839/100000000000 : ℝ) (500974698381/1000000000000 : ℝ) (50097469839/100000000000 : ℝ) (500974698381/1000000000000 : ℝ) (50097469839/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66653/524288 : ℝ))) 7 (500974698381/1000000000000 : ℝ) (50097469839/100000000000 : ℝ) (500974698381/1000000000000 : ℝ) (50097469839/100000000000 : ℝ) (500974698381/1000000000000 : ℝ) (50097469839/100000000000 : ℝ) (500974698381/1000000000000 : ℝ) (50097469839/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66653/524288 : ℝ)) hmem 8 (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ) (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66653/524288 : ℝ))) hcmem 8 (500974698381/1000000000000 : ℝ) (50097469839/100000000000 : ℝ) (500974698381/1000000000000 : ℝ) (50097469839/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66653/524288 : ℝ)) (496050742493/500000000000 : ℝ) (992101484989/1000000000000 : ℝ) (500974698381/1000000000000 : ℝ) (50097469839/100000000000 : ℝ) (158638854581/200000000000 : ℝ) (396597136461/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0580_exp_lower
  have heNumeric : (410980618241/200000000000 : ℝ)/4 ≤ Real.exp (-21314101499129/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980618241/200000000000 : ℝ)/4 ≤ Real.exp ((16663/131072 : ℝ)-(396597136461/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16663/131072 : ℝ) (66653/524288 : ℝ) (396597136461/500000000000 : ℝ) (410980618241/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0581; no trusted numerical premise.
theorem cover8_leaf0581_exp_radius : (62375970479855617/62500000000000000 : ℝ) ≤ Real.exp ((-33327/2097152 : ℝ)/8) ∧ Real.exp ((-33327/2097152 : ℝ)/8) ≤ (998015527677689873/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33327/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0581_exp_lower : (115014191792814237/125000000000000000 : ℝ) ≤ Real.exp ((-17051281338167/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051281338167/25600000000000 : ℝ)/8) ≤ (920113534342513897/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051281338167/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0581_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903080059/1000000000000 : ℝ) ≤ 4*Real.exp (66653/524288 : ℝ)*Real.exp (-mu (radius 8 (33327/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903080059/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33327/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0581_exp_radius
  have hrNumeric : (98423405251/100000000000 : ℝ) ≤ Real.exp (-33327/2097152 : ℝ) ∧ Real.exp (-33327/2097152 : ℝ) ≤ (984234052511/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98423405251/100000000000 : ℝ) ≤ (radius 8 (33327/262144 : ℝ)) ∧ (radius 8 (33327/262144 : ℝ)) ≤ (984234052511/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33327/262144 : ℝ)) (98423405251/100000000000 : ℝ) (984234052511/1000000000000 : ℝ) (22108867663/125000000000 : ℝ) (17687094131/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33327/262144 : ℝ)) (98423405251/100000000000 : ℝ) (984234052511/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33327/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98423405251/100000000000 : ℝ) (984234052511/1000000000000 : ℝ) (198423405251/200000000000 : ℝ) (62007314141/62500000000 : ℝ) (124010713531/125000000000 : ℝ) (992085708249/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33327/262144 : ℝ)) 1 (198423405251/200000000000 : ℝ) (62007314141/62500000000 : ℝ) (124010713531/125000000000 : ℝ) (992085708249/1000000000000 : ℝ) (992101367251/1000000000000 : ℝ) (992101367253/1000000000000 : ℝ) (992101367127/1000000000000 : ℝ) (992101367129/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33327/262144 : ℝ)) 2 (992101367251/1000000000000 : ℝ) (992101367253/1000000000000 : ℝ) (992101367127/1000000000000 : ℝ) (992101367129/1000000000000 : ℝ) (992101367189/1000000000000 : ℝ) (992101367191/1000000000000 : ℝ) (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33327/262144 : ℝ)) 3 (992101367189/1000000000000 : ℝ) (992101367191/1000000000000 : ℝ) (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ) (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ) (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33327/262144 : ℝ)) 4 (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ) (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ) (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ) (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33327/262144 : ℝ)) 5 (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ) (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ) (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ) (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33327/262144 : ℝ)) 6 (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ) (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ) (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ) (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33327/262144 : ℝ)) 7 (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ) (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ) (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ) (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33327/262144 : ℝ))) (22108867663/125000000000 : ℝ) (17687094131/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33327/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22108867663/125000000000 : ℝ) (17687094131/100000000000 : ℝ) (147108867663/250000000000 : ℝ) (117687094131/200000000000 : ℝ) (84112054143/200000000000 : ℝ) (420560270723/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33327/262144 : ℝ))) 1 (147108867663/250000000000 : ℝ) (117687094131/200000000000 : ℝ) (84112054143/200000000000 : ℝ) (420560270723/1000000000000 : ℝ) (504497870683/1000000000000 : ℝ) (504497870689/1000000000000 : ℝ) (497466160493/1000000000000 : ℝ) (994932321/2000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33327/262144 : ℝ))) 2 (504497870683/1000000000000 : ℝ) (504497870689/1000000000000 : ℝ) (497466160493/1000000000000 : ℝ) (994932321/2000000000 : ℝ) (125245503897/250000000000 : ℝ) (100196403119/200000000000 : ℝ) (500969678429/1000000000000 : ℝ) (125242419609/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33327/262144 : ℝ))) 3 (125245503897/250000000000 : ℝ) (100196403119/200000000000 : ℝ) (500969678429/1000000000000 : ℝ) (125242419609/250000000000 : ℝ) (15655495219/31250000000 : ℝ) (62621980877/125000000000 : ℝ) (50097584697/100000000000 : ℝ) (250487923489/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33327/262144 : ℝ))) 4 (15655495219/31250000000 : ℝ) (62621980877/125000000000 : ℝ) (50097584697/100000000000 : ℝ) (250487923489/500000000000 : ℝ) (500975846989/1000000000000 : ℝ) (500975846997/1000000000000 : ℝ) (125243961747/250000000000 : ℝ) (500975846997/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33327/262144 : ℝ))) 5 (500975846989/1000000000000 : ℝ) (500975846997/1000000000000 : ℝ) (125243961747/250000000000 : ℝ) (500975846997/1000000000000 : ℝ) (125243961747/250000000000 : ℝ) (500975846997/1000000000000 : ℝ) (125243961747/250000000000 : ℝ) (500975846997/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33327/262144 : ℝ))) 6 (125243961747/250000000000 : ℝ) (500975846997/1000000000000 : ℝ) (125243961747/250000000000 : ℝ) (500975846997/1000000000000 : ℝ) (125243961747/250000000000 : ℝ) (500975846997/1000000000000 : ℝ) (125243961747/250000000000 : ℝ) (500975846997/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33327/262144 : ℝ))) 7 (125243961747/250000000000 : ℝ) (500975846997/1000000000000 : ℝ) (125243961747/250000000000 : ℝ) (500975846997/1000000000000 : ℝ) (125243961747/250000000000 : ℝ) (500975846997/1000000000000 : ℝ) (125243961747/250000000000 : ℝ) (500975846997/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33327/262144 : ℝ)) hmem 8 (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ) (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33327/262144 : ℝ))) hcmem 8 (125243961747/250000000000 : ℝ) (500975846997/1000000000000 : ℝ) (125243961747/250000000000 : ℝ) (500975846997/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33327/262144 : ℝ)) (248025341797/250000000000 : ℝ) (992101367191/1000000000000 : ℝ) (125243961747/250000000000 : ℝ) (500975846997/1000000000000 : ℝ) (793196185677/1000000000000 : ℝ) (158639237139/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0581_exp_lower
  have heNumeric : (2054903080059/1000000000000 : ℝ)/4 ≤ Real.exp (-17051281338167/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903080059/1000000000000 : ℝ)/4 ≤ Real.exp ((66653/524288 : ℝ)-(158639237139/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66653/524288 : ℝ) (33327/262144 : ℝ) (158639237139/200000000000 : ℝ) (2054903080059/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0582; no trusted numerical premise.
theorem cover8_leaf0582_exp_radius : (249503874483627453/250000000000000000 : ℝ) ≤ Real.exp ((-66655/4194304 : ℝ)/8) ∧ Real.exp ((-66655/4194304 : ℝ)/8) ≤ (998015497934509813/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66655/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0582_exp_lower : (460056766860409979/500000000000000000 : ℝ) ≤ Real.exp ((-42628203691361/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628203691361/64000000000000 : ℝ)/8) ≤ (920113533720819959/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628203691361/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0582_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903068951/1000000000000 : ℝ) ≤ 4*Real.exp (33327/262144 : ℝ)*Real.exp (-mu (radius 8 (66655/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903068951/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66655/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0582_exp_radius
  have hrNumeric : (19684676357/20000000000 : ℝ) ≤ Real.exp (-66655/4194304 : ℝ) ∧ Real.exp (-66655/4194304 : ℝ) ≤ (984233817851/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (19684676357/20000000000 : ℝ) ≤ (radius 8 (66655/524288 : ℝ)) ∧ (radius 8 (66655/524288 : ℝ)) ≤ (984233817851/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66655/524288 : ℝ)) (19684676357/20000000000 : ℝ) (984233817851/1000000000000 : ℝ) (176872247111/1000000000000 : ℝ) (88436123559/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66655/524288 : ℝ)) (19684676357/20000000000 : ℝ) (984233817851/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66655/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (19684676357/20000000000 : ℝ) (984233817851/1000000000000 : ℝ) (39684676357/40000000000 : ℝ) (496058454463/500000000000 : ℝ) (496042794991/500000000000 : ℝ) (992085589983/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66655/524288 : ℝ)) 1 (39684676357/40000000000 : ℝ) (496058454463/500000000000 : ℝ) (496042794991/500000000000 : ℝ) (992085589983/1000000000000 : ℝ) (992101249453/1000000000000 : ℝ) (198420249891/200000000000 : ℝ) (992101249329/1000000000000 : ℝ) (992101249331/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66655/524288 : ℝ)) 2 (992101249453/1000000000000 : ℝ) (198420249891/200000000000 : ℝ) (992101249329/1000000000000 : ℝ) (992101249331/1000000000000 : ℝ) (992101249391/1000000000000 : ℝ) (992101249393/1000000000000 : ℝ) (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66655/524288 : ℝ)) 3 (992101249391/1000000000000 : ℝ) (992101249393/1000000000000 : ℝ) (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ) (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ) (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66655/524288 : ℝ)) 4 (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ) (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ) (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ) (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66655/524288 : ℝ)) 5 (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ) (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ) (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ) (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66655/524288 : ℝ)) 6 (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ) (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ) (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ) (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66655/524288 : ℝ)) 7 (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ) (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ) (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ) (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66655/524288 : ℝ))) (176872247111/1000000000000 : ℝ) (88436123559/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66655/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176872247111/1000000000000 : ℝ) (88436123559/500000000000 : ℝ) (117687224711/200000000000 : ℝ) (588436123559/1000000000000 : ℝ) (420561823173/1000000000000 : ℝ) (210280911591/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66655/524288 : ℝ))) 1 (117687224711/200000000000 : ℝ) (588436123559/1000000000000 : ℝ) (420561823173/1000000000000 : ℝ) (210280911591/500000000000 : ℝ) (126124743341/250000000000 : ℝ) (504498973371/1000000000000 : ℝ) (9949347093/20000000000 : ℝ) (248733677329/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66655/524288 : ℝ))) 2 (126124743341/250000000000 : ℝ) (504498973371/1000000000000 : ℝ) (9949347093/20000000000 : ℝ) (248733677329/500000000000 : ℝ) (500983164007/1000000000000 : ℝ) (100196632803/200000000000 : ℝ) (500970827197/1000000000000 : ℝ) (250485413603/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66655/524288 : ℝ))) 3 (500983164007/1000000000000 : ℝ) (100196632803/200000000000 : ℝ) (500970827197/1000000000000 : ℝ) (250485413603/500000000000 : ℝ) (250488497801/500000000000 : ℝ) (500976995611/1000000000000 : ℝ) (125244248891/250000000000 : ℝ) (500976995573/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66655/524288 : ℝ))) 4 (250488497801/500000000000 : ℝ) (500976995611/1000000000000 : ℝ) (125244248891/250000000000 : ℝ) (500976995573/1000000000000 : ℝ) (500976995583/1000000000000 : ℝ) (62622124449/125000000000 : ℝ) (250488497791/500000000000 : ℝ) (62622124449/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66655/524288 : ℝ))) 5 (500976995583/1000000000000 : ℝ) (62622124449/125000000000 : ℝ) (250488497791/500000000000 : ℝ) (62622124449/125000000000 : ℝ) (250488497791/500000000000 : ℝ) (62622124449/125000000000 : ℝ) (250488497791/500000000000 : ℝ) (62622124449/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66655/524288 : ℝ))) 6 (250488497791/500000000000 : ℝ) (62622124449/125000000000 : ℝ) (250488497791/500000000000 : ℝ) (62622124449/125000000000 : ℝ) (250488497791/500000000000 : ℝ) (62622124449/125000000000 : ℝ) (250488497791/500000000000 : ℝ) (62622124449/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66655/524288 : ℝ))) 7 (250488497791/500000000000 : ℝ) (62622124449/125000000000 : ℝ) (250488497791/500000000000 : ℝ) (62622124449/125000000000 : ℝ) (250488497791/500000000000 : ℝ) (62622124449/125000000000 : ℝ) (250488497791/500000000000 : ℝ) (62622124449/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66655/524288 : ℝ)) hmem 8 (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ) (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66655/524288 : ℝ))) hcmem 8 (250488497791/500000000000 : ℝ) (62622124449/125000000000 : ℝ) (250488497791/500000000000 : ℝ) (62622124449/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66655/524288 : ℝ)) (99210124939/100000000000 : ℝ) (992101249393/1000000000000 : ℝ) (250488497791/500000000000 : ℝ) (62622124449/125000000000 : ℝ) (79319809843/100000000000 : ℝ) (793198098449/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0582_exp_lower
  have heNumeric : (2054903068951/1000000000000 : ℝ)/4 ≤ Real.exp (-42628203691361/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903068951/1000000000000 : ℝ)/4 ≤ Real.exp ((33327/262144 : ℝ)-(793198098449/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33327/262144 : ℝ) (66655/524288 : ℝ) (793198098449/1000000000000 : ℝ) (2054903068951/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0583; no trusted numerical premise.
theorem cover8_leaf0583_exp_radius : (499007734095665319/500000000000000000 : ℝ) ≤ Real.exp ((-2083/131072 : ℝ)/8) ∧ Real.exp ((-2083/131072 : ℝ)/8) ≤ (998015468191330639/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2083/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0583_exp_lower : (460056766551173209/500000000000000000 : ℝ) ≤ Real.exp ((-3410256322841/5120000000000 : ℝ)/8) ∧ Real.exp ((-3410256322841/5120000000000 : ℝ)/8) ≤ (920113533102346419/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3410256322841/5120000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0583_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903057901/1000000000000 : ℝ) ≤ 4*Real.exp (66655/524288 : ℝ)*Real.exp (-mu (radius 8 (2083/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903057901/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2083/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0583_exp_radius
  have hrNumeric : (984233583191/1000000000000 : ℝ) ≤ Real.exp (-2083/131072 : ℝ) ∧ Real.exp (-2083/131072 : ℝ) ≤ (123029197899/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984233583191/1000000000000 : ℝ) ≤ (radius 8 (2083/16384 : ℝ)) ∧ (radius 8 (2083/16384 : ℝ)) ≤ (123029197899/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2083/16384 : ℝ)) (984233583191/1000000000000 : ℝ) (123029197899/125000000000 : ℝ) (22109194113/125000000000 : ℝ) (17687355291/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2083/16384 : ℝ)) (984233583191/1000000000000 : ℝ) (123029197899/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2083/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984233583191/1000000000000 : ℝ) (123029197899/125000000000 : ℝ) (198423358319/200000000000 : ℝ) (248029197899/250000000000 : ℝ) (248021367929/250000000000 : ℝ) (496042735859/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2083/16384 : ℝ)) 1 (198423358319/200000000000 : ℝ) (248029197899/250000000000 : ℝ) (248021367929/250000000000 : ℝ) (496042735859/500000000000 : ℝ) (198420226331/200000000000 : ℝ) (992101131657/1000000000000 : ℝ) (992101131531/1000000000000 : ℝ) (496050565767/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2083/16384 : ℝ)) 2 (198420226331/200000000000 : ℝ) (992101131657/1000000000000 : ℝ) (992101131531/1000000000000 : ℝ) (496050565767/500000000000 : ℝ) (992101131593/1000000000000 : ℝ) (248025282899/250000000000 : ℝ) (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2083/16384 : ℝ)) 3 (992101131593/1000000000000 : ℝ) (248025282899/250000000000 : ℝ) (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ) (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ) (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2083/16384 : ℝ)) 4 (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ) (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ) (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ) (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2083/16384 : ℝ)) 5 (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ) (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ) (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ) (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2083/16384 : ℝ)) 6 (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ) (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ) (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ) (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2083/16384 : ℝ)) 7 (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ) (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ) (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ) (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2083/16384 : ℝ))) (22109194113/125000000000 : ℝ) (17687355291/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2083/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22109194113/125000000000 : ℝ) (17687355291/100000000000 : ℝ) (147109194113/250000000000 : ℝ) (117687355291/200000000000 : ℝ) (420563375609/1000000000000 : ℝ) (420563375617/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2083/16384 : ℝ))) 1 (147109194113/250000000000 : ℝ) (117687355291/200000000000 : ℝ) (420563375609/1000000000000 : ℝ) (420563375617/1000000000000 : ℝ) (50450007603/100000000000 : ℝ) (126125019009/250000000000 : ℝ) (497468548791/1000000000000 : ℝ) (248734274399/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2083/16384 : ℝ))) 2 (50450007603/100000000000 : ℝ) (126125019009/250000000000 : ℝ) (497468548791/1000000000000 : ℝ) (248734274399/500000000000 : ℝ) (50098431241/100000000000 : ℝ) (500984312417/1000000000000 : ℝ) (10019439519/20000000000 : ℝ) (500971975957/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2083/16384 : ℝ))) 3 (50098431241/100000000000 : ℝ) (500984312417/1000000000000 : ℝ) (10019439519/20000000000 : ℝ) (500971975957/1000000000000 : ℝ) (25048907209/50000000000 : ℝ) (500978144187/1000000000000 : ℝ) (250489072071/500000000000 : ℝ) (10019562883/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2083/16384 : ℝ))) 4 (25048907209/50000000000 : ℝ) (500978144187/1000000000000 : ℝ) (250489072071/500000000000 : ℝ) (10019562883/20000000000 : ℝ) (500978144161/1000000000000 : ℝ) (500978144169/1000000000000 : ℝ) (3131113401/6250000000 : ℝ) (500978144169/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2083/16384 : ℝ))) 5 (500978144161/1000000000000 : ℝ) (500978144169/1000000000000 : ℝ) (3131113401/6250000000 : ℝ) (500978144169/1000000000000 : ℝ) (3131113401/6250000000 : ℝ) (500978144169/1000000000000 : ℝ) (3131113401/6250000000 : ℝ) (500978144169/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2083/16384 : ℝ))) 6 (3131113401/6250000000 : ℝ) (500978144169/1000000000000 : ℝ) (3131113401/6250000000 : ℝ) (500978144169/1000000000000 : ℝ) (3131113401/6250000000 : ℝ) (500978144169/1000000000000 : ℝ) (3131113401/6250000000 : ℝ) (500978144169/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2083/16384 : ℝ))) 7 (3131113401/6250000000 : ℝ) (500978144169/1000000000000 : ℝ) (3131113401/6250000000 : ℝ) (500978144169/1000000000000 : ℝ) (3131113401/6250000000 : ℝ) (500978144169/1000000000000 : ℝ) (3131113401/6250000000 : ℝ) (500978144169/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2083/16384 : ℝ)) hmem 8 (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ) (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2083/16384 : ℝ))) hcmem 8 (3131113401/6250000000 : ℝ) (500978144169/1000000000000 : ℝ) (3131113401/6250000000 : ℝ) (500978144169/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2083/16384 : ℝ)) (124012641449/125000000000 : ℝ) (248025282899/250000000000 : ℝ) (3131113401/6250000000 : ℝ) (500978144169/1000000000000 : ℝ) (793200011157/1000000000000 : ℝ) (31728000447/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0583_exp_lower
  have heNumeric : (2054903057901/1000000000000 : ℝ)/4 ≤ Real.exp (-3410256322841/5120000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903057901/1000000000000 : ℝ)/4 ≤ Real.exp ((66655/524288 : ℝ)-(31728000447/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66655/524288 : ℝ) (2083/16384 : ℝ) (31728000447/40000000000 : ℝ) (2054903057901/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0584; no trusted numerical premise.
theorem cover8_leaf0584_exp_radius : (19960308768963047/20000000000000000 : ℝ) ≤ Real.exp ((-66657/4194304 : ℝ)/8) ∧ Real.exp ((-66657/4194304 : ℝ)/8) ≤ (998015438448152351/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66657/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0584_exp_lower : (920113532484677977/1000000000000000000 : ℝ) ≤ Real.exp ((-2664262773701/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664262773701/4000000000000 : ℝ)/8) ≤ (460056766242338989/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664262773701/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0584_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451523433/500000000000 : ℝ) ≤ 4*Real.exp (2083/16384 : ℝ)*Real.exp (-mu (radius 8 (66657/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451523433/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66657/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0584_exp_radius
  have hrNumeric : (984233348531/1000000000000 : ℝ) ≤ Real.exp (-66657/4194304 : ℝ) ∧ Real.exp (-66657/4194304 : ℝ) ≤ (246058337133/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984233348531/1000000000000 : ℝ) ≤ (radius 8 (66657/524288 : ℝ)) ∧ (radius 8 (66657/524288 : ℝ)) ≤ (246058337133/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66657/524288 : ℝ)) (984233348531/1000000000000 : ℝ) (246058337133/250000000000 : ℝ) (44218714673/250000000000 : ℝ) (176874858699/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66657/524288 : ℝ)) (984233348531/1000000000000 : ℝ) (246058337133/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66657/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984233348531/1000000000000 : ℝ) (246058337133/250000000000 : ℝ) (198423334853/200000000000 : ℝ) (496058337133/500000000000 : ℝ) (19841707069/20000000000 : ℝ) (248021338363/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66657/524288 : ℝ)) 1 (198423334853/200000000000 : ℝ) (496058337133/500000000000 : ℝ) (19841707069/20000000000 : ℝ) (248021338363/250000000000 : ℝ) (992101013857/1000000000000 : ℝ) (992101013859/1000000000000 : ℝ) (992101013733/1000000000000 : ℝ) (124012626717/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66657/524288 : ℝ)) 2 (992101013857/1000000000000 : ℝ) (992101013859/1000000000000 : ℝ) (992101013733/1000000000000 : ℝ) (124012626717/125000000000 : ℝ) (198420202759/200000000000 : ℝ) (496050506899/500000000000 : ℝ) (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66657/524288 : ℝ)) 3 (198420202759/200000000000 : ℝ) (496050506899/500000000000 : ℝ) (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ) (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ) (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66657/524288 : ℝ)) 4 (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ) (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ) (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ) (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66657/524288 : ℝ)) 5 (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ) (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ) (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ) (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66657/524288 : ℝ)) 6 (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ) (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ) (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ) (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66657/524288 : ℝ)) 7 (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ) (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ) (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ) (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66657/524288 : ℝ))) (44218714673/250000000000 : ℝ) (176874858699/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66657/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44218714673/250000000000 : ℝ) (176874858699/1000000000000 : ℝ) (294218714673/500000000000 : ℝ) (11768748587/20000000000 : ℝ) (420564928033/1000000000000 : ℝ) (420564928043/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66657/524288 : ℝ))) 1 (294218714673/500000000000 : ℝ) (11768748587/20000000000 : ℝ) (420564928033/1000000000000 : ℝ) (420564928043/1000000000000 : ℝ) (504501178689/1000000000000 : ℝ) (504501178697/1000000000000 : ℝ) (497469742923/1000000000000 : ℝ) (124367435733/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66657/524288 : ℝ))) 2 (504501178689/1000000000000 : ℝ) (504501178697/1000000000000 : ℝ) (497469742923/1000000000000 : ℝ) (124367435733/250000000000 : ℝ) (250492730403/500000000000 : ℝ) (100197092163/200000000000 : ℝ) (100194624939/200000000000 : ℝ) (15655410147/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66657/524288 : ℝ))) 3 (250492730403/500000000000 : ℝ) (100197092163/200000000000 : ℝ) (100194624939/200000000000 : ℝ) (15655410147/31250000000 : ℝ) (2003917171/4000000000 : ℝ) (12524482319/25000000000 : ℝ) (62622411589/125000000000 : ℝ) (250489646361/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66657/524288 : ℝ))) 4 (2003917171/4000000000 : ℝ) (12524482319/25000000000 : ℝ) (62622411589/125000000000 : ℝ) (250489646361/500000000000 : ℝ) (500979292731/1000000000000 : ℝ) (500979292741/1000000000000 : ℝ) (50097929273/100000000000 : ℝ) (500979292741/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66657/524288 : ℝ))) 5 (500979292731/1000000000000 : ℝ) (500979292741/1000000000000 : ℝ) (50097929273/100000000000 : ℝ) (500979292741/1000000000000 : ℝ) (50097929273/100000000000 : ℝ) (500979292741/1000000000000 : ℝ) (50097929273/100000000000 : ℝ) (500979292741/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66657/524288 : ℝ))) 6 (50097929273/100000000000 : ℝ) (500979292741/1000000000000 : ℝ) (50097929273/100000000000 : ℝ) (500979292741/1000000000000 : ℝ) (50097929273/100000000000 : ℝ) (500979292741/1000000000000 : ℝ) (50097929273/100000000000 : ℝ) (500979292741/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66657/524288 : ℝ))) 7 (50097929273/100000000000 : ℝ) (500979292741/1000000000000 : ℝ) (50097929273/100000000000 : ℝ) (500979292741/1000000000000 : ℝ) (50097929273/100000000000 : ℝ) (500979292741/1000000000000 : ℝ) (50097929273/100000000000 : ℝ) (500979292741/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66657/524288 : ℝ)) hmem 8 (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ) (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66657/524288 : ℝ))) hcmem 8 (50097929273/100000000000 : ℝ) (500979292741/1000000000000 : ℝ) (50097929273/100000000000 : ℝ) (500979292741/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66657/524288 : ℝ)) (496050506897/500000000000 : ℝ) (496050506899/500000000000 : ℝ) (50097929273/100000000000 : ℝ) (500979292741/1000000000000 : ℝ) (24787560121/31250000000 : ℝ) (396600961947/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0584_exp_lower
  have heNumeric : (1027451523433/500000000000 : ℝ)/4 ≤ Real.exp (-2664262773701/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451523433/500000000000 : ℝ)/4 ≤ Real.exp ((2083/16384 : ℝ)-(396600961947/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2083/16384 : ℝ) (66657/524288 : ℝ) (396600961947/500000000000 : ℝ) (1027451523433/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0585; no trusted numerical premise.
theorem cover8_leaf0585_exp_radius : (998015408704974949/1000000000000000000 : ℝ) ≤ Real.exp ((-33329/2097152 : ℝ)/8) ∧ Real.exp ((-33329/2097152 : ℝ)/8) ≤ (19960308174099499/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33329/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0585_exp_lower : (184022706374161001/200000000000000000 : ℝ) ≤ Real.exp ((-17051281888323/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051281888323/25600000000000 : ℝ)/8) ≤ (460056765935402503/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051281888323/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0585_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451517949/500000000000 : ℝ) ≤ 4*Real.exp (66657/524288 : ℝ)*Real.exp (-mu (radius 8 (33329/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451517949/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33329/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0585_exp_radius
  have hrNumeric : (61514569617/62500000000 : ℝ) ≤ Real.exp (-33329/2097152 : ℝ) ∧ Real.exp (-33329/2097152 : ℝ) ≤ (984233113873/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61514569617/62500000000 : ℝ) ≤ (radius 8 (33329/262144 : ℝ)) ∧ (radius 8 (33329/262144 : ℝ)) ≤ (984233113873/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33329/262144 : ℝ)) (61514569617/62500000000 : ℝ) (984233113873/1000000000000 : ℝ) (35375232893/200000000000 : ℝ) (176876164471/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33329/262144 : ℝ)) (61514569617/62500000000 : ℝ) (984233113873/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33329/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61514569617/62500000000 : ℝ) (984233113873/1000000000000 : ℝ) (124014569617/125000000000 : ℝ) (992116556937/1000000000000 : ℝ) (62005327199/62500000000 : ℝ) (496042617593/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33329/262144 : ℝ)) 1 (124014569617/125000000000 : ℝ) (992116556937/1000000000000 : ℝ) (62005327199/62500000000 : ℝ) (496042617593/500000000000 : ℝ) (49605044803/50000000000 : ℝ) (496050448031/500000000000 : ℝ) (15501576499/15625000000 : ℝ) (496050447969/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33329/262144 : ℝ)) 2 (49605044803/50000000000 : ℝ) (496050448031/500000000000 : ℝ) (15501576499/15625000000 : ℝ) (496050447969/500000000000 : ℝ) (496050447999/500000000000 : ℝ) (31003153/31250000 : ℝ) (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33329/262144 : ℝ)) 3 (496050447999/500000000000 : ℝ) (31003153/31250000 : ℝ) (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ) (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ) (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33329/262144 : ℝ)) 4 (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ) (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ) (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ) (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33329/262144 : ℝ)) 5 (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ) (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ) (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ) (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33329/262144 : ℝ)) 6 (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ) (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ) (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ) (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33329/262144 : ℝ)) 7 (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ) (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ) (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ) (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33329/262144 : ℝ))) (35375232893/200000000000 : ℝ) (176876164471/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33329/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35375232893/200000000000 : ℝ) (176876164471/1000000000000 : ℝ) (73554760279/125000000000 : ℝ) (147109520559/250000000000 : ℝ) (210283240217/500000000000 : ℝ) (210283240221/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33329/262144 : ℝ))) 1 (73554760279/125000000000 : ℝ) (147109520559/250000000000 : ℝ) (210283240217/500000000000 : ℝ) (210283240221/500000000000 : ℝ) (504502281333/1000000000000 : ℝ) (504502281339/1000000000000 : ℝ) (248735468519/500000000000 : ℝ) (99494187409/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33329/262144 : ℝ))) 2 (504502281333/1000000000000 : ℝ) (504502281339/1000000000000 : ℝ) (248735468519/500000000000 : ℝ) (99494187409/200000000000 : ℝ) (100197321837/200000000000 : ℝ) (62623326149/125000000000 : ℝ) (500974273423/1000000000000 : ℝ) (500974273431/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33329/262144 : ℝ))) 3 (100197321837/200000000000 : ℝ) (62623326149/125000000000 : ℝ) (500974273423/1000000000000 : ℝ) (500974273431/1000000000000 : ℝ) (62622555163/125000000000 : ℝ) (15655638791/31250000000 : ℝ) (250490220633/500000000000 : ℝ) (250490220637/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33329/262144 : ℝ))) 4 (62622555163/125000000000 : ℝ) (15655638791/31250000000 : ℝ) (250490220633/500000000000 : ℝ) (250490220637/500000000000 : ℝ) (100196088257/200000000000 : ℝ) (500980441293/1000000000000 : ℝ) (125245110321/250000000000 : ℝ) (500980441293/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33329/262144 : ℝ))) 5 (100196088257/200000000000 : ℝ) (500980441293/1000000000000 : ℝ) (125245110321/250000000000 : ℝ) (500980441293/1000000000000 : ℝ) (125245110321/250000000000 : ℝ) (500980441293/1000000000000 : ℝ) (125245110321/250000000000 : ℝ) (500980441293/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33329/262144 : ℝ))) 6 (125245110321/250000000000 : ℝ) (500980441293/1000000000000 : ℝ) (125245110321/250000000000 : ℝ) (500980441293/1000000000000 : ℝ) (125245110321/250000000000 : ℝ) (500980441293/1000000000000 : ℝ) (125245110321/250000000000 : ℝ) (500980441293/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33329/262144 : ℝ))) 7 (125245110321/250000000000 : ℝ) (500980441293/1000000000000 : ℝ) (125245110321/250000000000 : ℝ) (500980441293/1000000000000 : ℝ) (125245110321/250000000000 : ℝ) (500980441293/1000000000000 : ℝ) (125245110321/250000000000 : ℝ) (500980441293/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33329/262144 : ℝ)) hmem 8 (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ) (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33329/262144 : ℝ))) hcmem 8 (125245110321/250000000000 : ℝ) (500980441293/1000000000000 : ℝ) (125245110321/250000000000 : ℝ) (500980441293/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33329/262144 : ℝ)) (992100895997/1000000000000 : ℝ) (31003153/31250000 : ℝ) (125245110321/250000000000 : ℝ) (500980441293/1000000000000 : ℝ) (793203836563/1000000000000 : ℝ) (39660191829/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0585_exp_lower
  have heNumeric : (1027451517949/500000000000 : ℝ)/4 ≤ Real.exp (-17051281888323/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451517949/500000000000 : ℝ)/4 ≤ Real.exp ((66657/524288 : ℝ)-(39660191829/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66657/524288 : ℝ) (33329/262144 : ℝ) (39660191829/50000000000 : ℝ) (1027451517949/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0586; no trusted numerical premise.
theorem cover8_leaf0586_exp_radius : (499007689480899217/500000000000000000 : ℝ) ≤ Real.exp ((-66659/4194304 : ℝ)/8) ∧ Real.exp ((-66659/4194304 : ℝ)/8) ≤ (199603075792359687/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66659/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0586_exp_lower : (920113531257622119/1000000000000000000 : ℝ) ≤ Real.exp ((-8525641012403/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525641012403/12800000000000 : ℝ)/8) ≤ (23002838281440553/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525641012403/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0586_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451512471/500000000000 : ℝ) ≤ 4*Real.exp (33329/262144 : ℝ)*Real.exp (-mu (radius 8 (66659/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451512471/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66659/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0586_exp_radius
  have hrNumeric : (246058219803/250000000000 : ℝ) ≤ Real.exp (-66659/4194304 : ℝ) ∧ Real.exp (-66659/4194304 : ℝ) ≤ (984232879213/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246058219803/250000000000 : ℝ) ≤ (radius 8 (66659/524288 : ℝ)) ∧ (radius 8 (66659/524288 : ℝ)) ≤ (984232879213/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66659/524288 : ℝ)) (246058219803/250000000000 : ℝ) (984232879213/1000000000000 : ℝ) (176877470233/1000000000000 : ℝ) (176877470239/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66659/524288 : ℝ)) (246058219803/250000000000 : ℝ) (984232879213/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66659/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246058219803/250000000000 : ℝ) (984232879213/1000000000000 : ℝ) (496058219803/500000000000 : ℝ) (992116439607/1000000000000 : ℝ) (496042558459/500000000000 : ℝ) (24802127923/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66659/524288 : ℝ)) 1 (496058219803/500000000000 : ℝ) (992116439607/1000000000000 : ℝ) (496042558459/500000000000 : ℝ) (24802127923/25000000000 : ℝ) (496050389131/500000000000 : ℝ) (124012597283/125000000000 : ℝ) (496050389069/500000000000 : ℝ) (49605038907/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66659/524288 : ℝ)) 2 (496050389131/500000000000 : ℝ) (124012597283/125000000000 : ℝ) (496050389069/500000000000 : ℝ) (49605038907/50000000000 : ℝ) (4960503891/5000000000 : ℝ) (496050389101/500000000000 : ℝ) (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66659/524288 : ℝ)) 3 (4960503891/5000000000 : ℝ) (496050389101/500000000000 : ℝ) (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ) (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ) (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66659/524288 : ℝ)) 4 (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ) (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ) (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ) (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66659/524288 : ℝ)) 5 (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ) (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ) (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ) (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66659/524288 : ℝ)) 6 (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ) (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ) (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ) (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66659/524288 : ℝ)) 7 (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ) (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ) (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ) (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66659/524288 : ℝ))) (176877470233/1000000000000 : ℝ) (176877470239/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66659/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176877470233/1000000000000 : ℝ) (176877470239/1000000000000 : ℝ) (147109683779/250000000000 : ℝ) (7355484189/12500000000 : ℝ) (420568032823/1000000000000 : ℝ) (420568032831/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66659/524288 : ℝ))) 1 (147109683779/250000000000 : ℝ) (7355484189/12500000000 : ℝ) (420568032823/1000000000000 : ℝ) (420568032831/1000000000000 : ℝ) (504503383969/1000000000000 : ℝ) (63062922997/125000000000 : ℝ) (497472131143/1000000000000 : ℝ) (497472131151/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66659/524288 : ℝ))) 2 (504503383969/1000000000000 : ℝ) (63062922997/125000000000 : ℝ) (497472131143/1000000000000 : ℝ) (497472131151/1000000000000 : ℝ) (125246939389/250000000000 : ℝ) (125246939391/250000000000 : ℝ) (500975422143/1000000000000 : ℝ) (62621927769/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66659/524288 : ℝ))) 3 (125246939389/250000000000 : ℝ) (125246939391/250000000000 : ℝ) (500975422143/1000000000000 : ℝ) (62621927769/125000000000 : ℝ) (500981589849/1000000000000 : ℝ) (250490794929/500000000000 : ℝ) (500981589811/1000000000000 : ℝ) (500981589821/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66659/524288 : ℝ))) 4 (500981589849/1000000000000 : ℝ) (250490794929/500000000000 : ℝ) (500981589811/1000000000000 : ℝ) (500981589821/1000000000000 : ℝ) (50098158983/100000000000 : ℝ) (6262269873/12500000000 : ℝ) (500981589829/1000000000000 : ℝ) (6262269873/12500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66659/524288 : ℝ))) 5 (50098158983/100000000000 : ℝ) (6262269873/12500000000 : ℝ) (500981589829/1000000000000 : ℝ) (6262269873/12500000000 : ℝ) (500981589829/1000000000000 : ℝ) (6262269873/12500000000 : ℝ) (500981589829/1000000000000 : ℝ) (6262269873/12500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66659/524288 : ℝ))) 6 (500981589829/1000000000000 : ℝ) (6262269873/12500000000 : ℝ) (500981589829/1000000000000 : ℝ) (6262269873/12500000000 : ℝ) (500981589829/1000000000000 : ℝ) (6262269873/12500000000 : ℝ) (500981589829/1000000000000 : ℝ) (6262269873/12500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66659/524288 : ℝ))) 7 (500981589829/1000000000000 : ℝ) (6262269873/12500000000 : ℝ) (500981589829/1000000000000 : ℝ) (6262269873/12500000000 : ℝ) (500981589829/1000000000000 : ℝ) (6262269873/12500000000 : ℝ) (500981589829/1000000000000 : ℝ) (6262269873/12500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66659/524288 : ℝ)) hmem 8 (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ) (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66659/524288 : ℝ))) hcmem 8 (500981589829/1000000000000 : ℝ) (6262269873/12500000000 : ℝ) (500981589829/1000000000000 : ℝ) (6262269873/12500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66659/524288 : ℝ)) (992100778199/1000000000000 : ℝ) (496050389101/500000000000 : ℝ) (500981589829/1000000000000 : ℝ) (6262269873/12500000000 : ℝ) (793205749239/1000000000000 : ℝ) (39660287463/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0586_exp_lower
  have heNumeric : (1027451512471/500000000000 : ℝ)/4 ≤ Real.exp (-8525641012403/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451512471/500000000000 : ℝ)/4 ≤ Real.exp ((33329/262144 : ℝ)-(39660287463/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33329/262144 : ℝ) (66659/524288 : ℝ) (39660287463/50000000000 : ℝ) (1027451512471/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0587; no trusted numerical premise.
theorem cover8_leaf0587_exp_radius : (199603069843724561/200000000000000000 : ℝ) ≤ Real.exp ((-16665/1048576 : ℝ)/8) ∧ Real.exp ((-16665/1048576 : ℝ)/8) ≤ (499007674609311403/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16665/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0587_exp_lower : (230028382661943661/250000000000000000 : ℝ) ≤ Real.exp ((-85256410802733/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256410802733/128000000000000 : ℝ)/8) ≤ (184022706129554929/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256410802733/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0587_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903014047/1000000000000 : ℝ) ≤ 4*Real.exp (66659/524288 : ℝ)*Real.exp (-mu (radius 8 (16665/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903014047/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16665/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0587_exp_radius
  have hrNumeric : (984232644553/1000000000000 : ℝ) ≤ Real.exp (-16665/1048576 : ℝ) ∧ Real.exp (-16665/1048576 : ℝ) ≤ (492116322277/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984232644553/1000000000000 : ℝ) ≤ (radius 8 (16665/131072 : ℝ)) ∧ (radius 8 (16665/131072 : ℝ)) ≤ (492116322277/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16665/131072 : ℝ)) (984232644553/1000000000000 : ℝ) (492116322277/500000000000 : ℝ) (35375755197/200000000000 : ℝ) (22109846999/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16665/131072 : ℝ)) (984232644553/1000000000000 : ℝ) (492116322277/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16665/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984232644553/1000000000000 : ℝ) (492116322277/500000000000 : ℝ) (248029080569/250000000000 : ℝ) (992116322277/1000000000000 : ℝ) (992084998653/1000000000000 : ℝ) (496042499327/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16665/131072 : ℝ)) 1 (248029080569/250000000000 : ℝ) (992116322277/1000000000000 : ℝ) (992084998653/1000000000000 : ℝ) (496042499327/500000000000 : ℝ) (62006291279/62500000000 : ℝ) (496050330233/500000000000 : ℝ) (49605033017/50000000000 : ℝ) (496050330171/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16665/131072 : ℝ)) 2 (62006291279/62500000000 : ℝ) (496050330233/500000000000 : ℝ) (49605033017/50000000000 : ℝ) (496050330171/500000000000 : ℝ) (496050330201/500000000000 : ℝ) (248025165101/250000000000 : ℝ) (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16665/131072 : ℝ)) 3 (496050330201/500000000000 : ℝ) (248025165101/250000000000 : ℝ) (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ) (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ) (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16665/131072 : ℝ)) 4 (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ) (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ) (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ) (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16665/131072 : ℝ)) 5 (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ) (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ) (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ) (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16665/131072 : ℝ)) 6 (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ) (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ) (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ) (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16665/131072 : ℝ)) 7 (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ) (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ) (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ) (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16665/131072 : ℝ))) (35375755197/200000000000 : ℝ) (22109846999/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16665/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35375755197/200000000000 : ℝ) (22109846999/125000000000 : ℝ) (73554923499/125000000000 : ℝ) (147109846999/250000000000 : ℝ) (420569585187/1000000000000 : ℝ) (420569585197/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16665/131072 : ℝ))) 1 (73554923499/125000000000 : ℝ) (147109846999/250000000000 : ℝ) (420569585187/1000000000000 : ℝ) (420569585197/1000000000000 : ℝ) (504504486589/1000000000000 : ℝ) (504504486597/1000000000000 : ℝ) (49747332523/100000000000 : ℝ) (248736662619/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16665/131072 : ℝ))) 2 (504504486589/1000000000000 : ℝ) (504504486597/1000000000000 : ℝ) (49747332523/100000000000 : ℝ) (248736662619/500000000000 : ℝ) (500988905909/1000000000000 : ℝ) (250494452959/500000000000 : ℝ) (250488285423/500000000000 : ℝ) (100195314171/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16665/131072 : ℝ))) 3 (500988905909/1000000000000 : ℝ) (250494452959/500000000000 : ℝ) (250488285423/500000000000 : ℝ) (100195314171/200000000000 : ℝ) (500982738377/1000000000000 : ℝ) (500982738387/1000000000000 : ℝ) (500982738339/1000000000000 : ℝ) (500982738349/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16665/131072 : ℝ))) 4 (500982738377/1000000000000 : ℝ) (500982738387/1000000000000 : ℝ) (500982738339/1000000000000 : ℝ) (500982738349/1000000000000 : ℝ) (250491369179/500000000000 : ℝ) (7827855287/15625000000 : ℝ) (500982738357/1000000000000 : ℝ) (7827855287/15625000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16665/131072 : ℝ))) 5 (250491369179/500000000000 : ℝ) (7827855287/15625000000 : ℝ) (500982738357/1000000000000 : ℝ) (7827855287/15625000000 : ℝ) (500982738357/1000000000000 : ℝ) (7827855287/15625000000 : ℝ) (500982738357/1000000000000 : ℝ) (7827855287/15625000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16665/131072 : ℝ))) 6 (500982738357/1000000000000 : ℝ) (7827855287/15625000000 : ℝ) (500982738357/1000000000000 : ℝ) (7827855287/15625000000 : ℝ) (500982738357/1000000000000 : ℝ) (7827855287/15625000000 : ℝ) (500982738357/1000000000000 : ℝ) (7827855287/15625000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16665/131072 : ℝ))) 7 (500982738357/1000000000000 : ℝ) (7827855287/15625000000 : ℝ) (500982738357/1000000000000 : ℝ) (7827855287/15625000000 : ℝ) (500982738357/1000000000000 : ℝ) (7827855287/15625000000 : ℝ) (500982738357/1000000000000 : ℝ) (7827855287/15625000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16665/131072 : ℝ)) hmem 8 (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ) (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16665/131072 : ℝ))) hcmem 8 (500982738357/1000000000000 : ℝ) (7827855287/15625000000 : ℝ) (500982738357/1000000000000 : ℝ) (7827855287/15625000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16665/131072 : ℝ)) (992100660401/1000000000000 : ℝ) (248025165101/250000000000 : ℝ) (500982738357/1000000000000 : ℝ) (7827855287/15625000000 : ℝ) (79320766189/100000000000 : ℝ) (793207661911/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0587_exp_lower
  have heNumeric : (2054903014047/1000000000000 : ℝ)/4 ≤ Real.exp (-85256410802733/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903014047/1000000000000 : ℝ)/4 ≤ Real.exp ((66659/524288 : ℝ)-(793207661911/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66659/524288 : ℝ) (16665/131072 : ℝ) (793207661911/1000000000000 : ℝ) (2054903014047/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0588; no trusted numerical premise.
theorem cover8_leaf0588_exp_radius : (998015319475448063/1000000000000000000 : ℝ) ≤ Real.exp ((-66661/4194304 : ℝ)/8) ∧ Real.exp ((-66661/4194304 : ℝ)/8) ≤ (3898497341700969/3906250000000000 : ℝ) := by
  have h := exp_small_bounds ((-66661/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0588_exp_lower : (184022706007884471/200000000000000000 : ℝ) ≤ Real.exp ((-21314102869943/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314102869943/32000000000000 : ℝ)/8) ≤ (230028382509855589/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314102869943/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0588_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903003177/1000000000000 : ℝ) ≤ 4*Real.exp (16665/131072 : ℝ)*Real.exp (-mu (radius 8 (66661/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903003177/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66661/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0588_exp_radius
  have hrNumeric : (984232409893/1000000000000 : ℝ) ≤ Real.exp (-66661/4194304 : ℝ) ∧ Real.exp (-66661/4194304 : ℝ) ≤ (492116204947/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984232409893/1000000000000 : ℝ) ≤ (radius 8 (66661/524288 : ℝ)) ∧ (radius 8 (66661/524288 : ℝ)) ≤ (492116204947/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66661/524288 : ℝ)) (984232409893/1000000000000 : ℝ) (492116204947/500000000000 : ℝ) (88440040867/500000000000 : ℝ) (8844004087/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66661/524288 : ℝ)) (984232409893/1000000000000 : ℝ) (492116204947/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66661/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984232409893/1000000000000 : ℝ) (492116204947/500000000000 : ℝ) (496058102473/500000000000 : ℝ) (992116204947/1000000000000 : ℝ) (992084880387/1000000000000 : ℝ) (248021220097/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66661/524288 : ℝ)) 1 (496058102473/500000000000 : ℝ) (992116204947/1000000000000 : ℝ) (992084880387/1000000000000 : ℝ) (248021220097/250000000000 : ℝ) (496050271333/500000000000 : ℝ) (248025135667/250000000000 : ℝ) (496050271271/500000000000 : ℝ) (62006283909/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66661/524288 : ℝ)) 2 (496050271333/500000000000 : ℝ) (248025135667/250000000000 : ℝ) (496050271271/500000000000 : ℝ) (62006283909/62500000000 : ℝ) (248025135651/250000000000 : ℝ) (496050271303/500000000000 : ℝ) (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66661/524288 : ℝ)) 3 (248025135651/250000000000 : ℝ) (496050271303/500000000000 : ℝ) (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ) (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ) (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66661/524288 : ℝ)) 4 (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ) (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ) (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ) (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66661/524288 : ℝ)) 5 (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ) (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ) (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ) (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66661/524288 : ℝ)) 6 (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ) (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ) (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ) (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66661/524288 : ℝ)) 7 (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ) (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ) (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ) (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66661/524288 : ℝ))) (88440040867/500000000000 : ℝ) (8844004087/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66661/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88440040867/500000000000 : ℝ) (8844004087/50000000000 : ℝ) (588440040867/1000000000000 : ℝ) (58844004087/100000000000 : ℝ) (210285568771/500000000000 : ℝ) (8411422751/20000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66661/524288 : ℝ))) 1 (588440040867/1000000000000 : ℝ) (58844004087/100000000000 : ℝ) (210285568771/500000000000 : ℝ) (8411422751/20000000000 : ℝ) (126126397301/250000000000 : ℝ) (50450558921/100000000000 : ℝ) (497474519309/1000000000000 : ℝ) (124368629829/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66661/524288 : ℝ))) 2 (126126397301/250000000000 : ℝ) (50450558921/100000000000 : ℝ) (497474519309/1000000000000 : ℝ) (124368629829/250000000000 : ℝ) (31311878391/62500000000 : ℝ) (500990054263/1000000000000 : ℝ) (250488859771/500000000000 : ℝ) (500977719549/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66661/524288 : ℝ))) 3 (31311878391/62500000000 : ℝ) (500990054263/1000000000000 : ℝ) (250488859771/500000000000 : ℝ) (500977719549/1000000000000 : ℝ) (500983886899/1000000000000 : ℝ) (250491943453/500000000000 : ℝ) (500983886861/1000000000000 : ℝ) (500983886869/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66661/524288 : ℝ))) 4 (500983886899/1000000000000 : ℝ) (250491943453/500000000000 : ℝ) (500983886861/1000000000000 : ℝ) (500983886869/1000000000000 : ℝ) (3131149293/6250000000 : ℝ) (62622985861/125000000000 : ℝ) (500983886879/1000000000000 : ℝ) (62622985861/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66661/524288 : ℝ))) 5 (3131149293/6250000000 : ℝ) (62622985861/125000000000 : ℝ) (500983886879/1000000000000 : ℝ) (62622985861/125000000000 : ℝ) (500983886879/1000000000000 : ℝ) (62622985861/125000000000 : ℝ) (500983886879/1000000000000 : ℝ) (62622985861/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66661/524288 : ℝ))) 6 (500983886879/1000000000000 : ℝ) (62622985861/125000000000 : ℝ) (500983886879/1000000000000 : ℝ) (62622985861/125000000000 : ℝ) (500983886879/1000000000000 : ℝ) (62622985861/125000000000 : ℝ) (500983886879/1000000000000 : ℝ) (62622985861/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66661/524288 : ℝ))) 7 (500983886879/1000000000000 : ℝ) (62622985861/125000000000 : ℝ) (500983886879/1000000000000 : ℝ) (62622985861/125000000000 : ℝ) (500983886879/1000000000000 : ℝ) (62622985861/125000000000 : ℝ) (500983886879/1000000000000 : ℝ) (62622985861/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66661/524288 : ℝ)) hmem 8 (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ) (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66661/524288 : ℝ))) hcmem 8 (500983886879/1000000000000 : ℝ) (62622985861/125000000000 : ℝ) (500983886879/1000000000000 : ℝ) (62622985861/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66661/524288 : ℝ)) (992100542603/1000000000000 : ℝ) (496050271303/500000000000 : ℝ) (500983886879/1000000000000 : ℝ) (62622985861/125000000000 : ℝ) (793209574531/1000000000000 : ℝ) (793209574549/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0588_exp_lower
  have heNumeric : (2054903003177/1000000000000 : ℝ)/4 ≤ Real.exp (-21314102869943/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903003177/1000000000000 : ℝ)/4 ≤ Real.exp ((16665/131072 : ℝ)-(793209574549/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16665/131072 : ℝ) (66661/524288 : ℝ) (793209574549/1000000000000 : ℝ) (2054903003177/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0589; no trusted numerical premise.
theorem cover8_leaf0589_exp_radius : (31187977804133569/31250000000000000 : ℝ) ≤ Real.exp ((-33331/2097152 : ℝ)/8) ∧ Real.exp ((-33331/2097152 : ℝ)/8) ≤ (998015289732274209/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33331/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0589_exp_lower : (460056764716915203/500000000000000000 : ℝ) ≤ Real.exp ((-85256412153739/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256412153739/128000000000000 : ℝ)/8) ≤ (920113529433830407/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256412153739/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0589_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451496179/500000000000 : ℝ) ≤ 4*Real.exp (66661/524288 : ℝ)*Real.exp (-mu (radius 8 (33331/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451496179/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33331/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0589_exp_radius
  have hrNumeric : (492116087617/500000000000 : ℝ) ≤ Real.exp (-33331/2097152 : ℝ) ∧ Real.exp (-33331/2097152 : ℝ) ≤ (196846435047/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492116087617/500000000000 : ℝ) ≤ (radius 8 (33331/262144 : ℝ)) ∧ (radius 8 (33331/262144 : ℝ)) ≤ (196846435047/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33331/262144 : ℝ)) (492116087617/500000000000 : ℝ) (196846435047/200000000000 : ℝ) (88440693733/500000000000 : ℝ) (176881387473/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33331/262144 : ℝ)) (492116087617/500000000000 : ℝ) (196846435047/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33331/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492116087617/500000000000 : ℝ) (196846435047/200000000000 : ℝ) (992116087617/1000000000000 : ℝ) (496058043809/500000000000 : ℝ) (992084762121/1000000000000 : ℝ) (992084762123/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33331/262144 : ℝ)) 1 (992116087617/1000000000000 : ℝ) (496058043809/500000000000 : ℝ) (992084762121/1000000000000 : ℝ) (992084762123/1000000000000 : ℝ) (992100424869/1000000000000 : ℝ) (992100424871/1000000000000 : ℝ) (198420084949/200000000000 : ℝ) (992100424747/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33331/262144 : ℝ)) 2 (992100424869/1000000000000 : ℝ) (992100424871/1000000000000 : ℝ) (198420084949/200000000000 : ℝ) (992100424747/1000000000000 : ℝ) (992100424807/1000000000000 : ℝ) (992100424809/1000000000000 : ℝ) (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33331/262144 : ℝ)) 3 (992100424807/1000000000000 : ℝ) (992100424809/1000000000000 : ℝ) (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ) (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ) (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33331/262144 : ℝ)) 4 (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ) (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ) (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ) (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33331/262144 : ℝ)) 5 (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ) (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ) (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ) (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33331/262144 : ℝ)) 6 (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ) (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ) (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ) (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33331/262144 : ℝ)) 7 (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ) (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ) (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ) (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33331/262144 : ℝ))) (88440693733/500000000000 : ℝ) (176881387473/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33331/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88440693733/500000000000 : ℝ) (176881387473/1000000000000 : ℝ) (588440693733/1000000000000 : ℝ) (588440693737/1000000000000 : ℝ) (420572689871/1000000000000 : ℝ) (420572689881/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33331/262144 : ℝ))) 1 (588440693733/1000000000000 : ℝ) (588440693737/1000000000000 : ℝ) (420572689871/1000000000000 : ℝ) (420572689881/1000000000000 : ℝ) (252253345901/500000000000 : ℝ) (504506691809/1000000000000 : ℝ) (497475713369/1000000000000 : ℝ) (248737856689/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33331/262144 : ℝ))) 2 (252253345901/500000000000 : ℝ) (504506691809/1000000000000 : ℝ) (497475713369/1000000000000 : ℝ) (248737856689/500000000000 : ℝ) (100198240517/200000000000 : ℝ) (250495601297/500000000000 : ℝ) (25048943411/50000000000 : ℝ) (500978868229/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33331/262144 : ℝ))) 3 (100198240517/200000000000 : ℝ) (250495601297/500000000000 : ℝ) (25048943411/50000000000 : ℝ) (500978868229/1000000000000 : ℝ) (250492517701/500000000000 : ℝ) (125246258853/250000000000 : ℝ) (125246258841/250000000000 : ℝ) (250492517687/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33331/262144 : ℝ))) 4 (250492517701/500000000000 : ℝ) (125246258853/250000000000 : ℝ) (125246258841/250000000000 : ℝ) (250492517687/500000000000 : ℝ) (500985035383/1000000000000 : ℝ) (500985035393/1000000000000 : ℝ) (250492517691/500000000000 : ℝ) (500985035393/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33331/262144 : ℝ))) 5 (500985035383/1000000000000 : ℝ) (500985035393/1000000000000 : ℝ) (250492517691/500000000000 : ℝ) (500985035393/1000000000000 : ℝ) (250492517691/500000000000 : ℝ) (500985035393/1000000000000 : ℝ) (250492517691/500000000000 : ℝ) (500985035393/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33331/262144 : ℝ))) 6 (250492517691/500000000000 : ℝ) (500985035393/1000000000000 : ℝ) (250492517691/500000000000 : ℝ) (500985035393/1000000000000 : ℝ) (250492517691/500000000000 : ℝ) (500985035393/1000000000000 : ℝ) (250492517691/500000000000 : ℝ) (500985035393/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33331/262144 : ℝ))) 7 (250492517691/500000000000 : ℝ) (500985035393/1000000000000 : ℝ) (250492517691/500000000000 : ℝ) (500985035393/1000000000000 : ℝ) (250492517691/500000000000 : ℝ) (500985035393/1000000000000 : ℝ) (250492517691/500000000000 : ℝ) (500985035393/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33331/262144 : ℝ)) hmem 8 (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ) (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33331/262144 : ℝ))) hcmem 8 (250492517691/500000000000 : ℝ) (500985035393/1000000000000 : ℝ) (250492517691/500000000000 : ℝ) (500985035393/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33331/262144 : ℝ)) (496050212403/500000000000 : ℝ) (992100424809/1000000000000 : ℝ) (250492517691/500000000000 : ℝ) (500985035393/1000000000000 : ℝ) (396605743571/500000000000 : ℝ) (793211487163/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0589_exp_lower
  have heNumeric : (1027451496179/500000000000 : ℝ)/4 ≤ Real.exp (-85256412153739/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451496179/500000000000 : ℝ)/4 ≤ Real.exp ((66661/524288 : ℝ)-(793211487163/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66661/524288 : ℝ) (33331/262144 : ℝ) (793211487163/1000000000000 : ℝ) (1027451496179/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0590; no trusted numerical premise.
theorem cover8_leaf0590_exp_radius : (499007629994550619/500000000000000000 : ℝ) ≤ Real.exp ((-66663/4194304 : ℝ)/8) ∧ Real.exp ((-66663/4194304 : ℝ)/8) ≤ (998015259989101239/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66663/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0590_exp_lower : (460056764415269371/500000000000000000 : ℝ) ≤ Real.exp ((-42628206412573/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628206412573/64000000000000 : ℝ)/8) ≤ (920113528830538743/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628206412573/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0590_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902981579/1000000000000 : ℝ) ≤ 4*Real.exp (33331/262144 : ℝ)*Real.exp (-mu (radius 8 (66663/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902981579/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66663/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0590_exp_radius
  have hrNumeric : (39369277623/40000000000 : ℝ) ≤ Real.exp (-66663/4194304 : ℝ) ∧ Real.exp (-66663/4194304 : ℝ) ≤ (30757248143/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39369277623/40000000000 : ℝ) ≤ (radius 8 (66663/524288 : ℝ)) ∧ (radius 8 (66663/524288 : ℝ)) ≤ (30757248143/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66663/524288 : ℝ)) (39369277623/40000000000 : ℝ) (30757248143/31250000000 : ℝ) (176882693189/1000000000000 : ℝ) (44220673299/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66663/524288 : ℝ)) (39369277623/40000000000 : ℝ) (30757248143/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66663/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39369277623/40000000000 : ℝ) (30757248143/31250000000 : ℝ) (992115970287/1000000000000 : ℝ) (62007248143/62500000000 : ℝ) (62005290241/62500000000 : ℝ) (992084643857/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66663/524288 : ℝ)) 1 (992115970287/1000000000000 : ℝ) (62007248143/62500000000 : ℝ) (62005290241/62500000000 : ℝ) (992084643857/1000000000000 : ℝ) (992100307071/1000000000000 : ℝ) (992100307073/1000000000000 : ℝ) (992100306947/1000000000000 : ℝ) (992100306949/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66663/524288 : ℝ)) 2 (992100307071/1000000000000 : ℝ) (992100307073/1000000000000 : ℝ) (992100306947/1000000000000 : ℝ) (992100306949/1000000000000 : ℝ) (992100307009/1000000000000 : ℝ) (992100307011/1000000000000 : ℝ) (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66663/524288 : ℝ)) 3 (992100307009/1000000000000 : ℝ) (992100307011/1000000000000 : ℝ) (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ) (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ) (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66663/524288 : ℝ)) 4 (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ) (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ) (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ) (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66663/524288 : ℝ)) 5 (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ) (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ) (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ) (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66663/524288 : ℝ)) 6 (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ) (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ) (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ) (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66663/524288 : ℝ)) 7 (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ) (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ) (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ) (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66663/524288 : ℝ))) (176882693189/1000000000000 : ℝ) (44220673299/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66663/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176882693189/1000000000000 : ℝ) (44220673299/250000000000 : ℝ) (294220673297/500000000000 : ℝ) (294220673299/500000000000 : ℝ) (52571780273/125000000000 : ℝ) (420574242193/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66663/524288 : ℝ))) 1 (294220673297/500000000000 : ℝ) (294220673299/500000000000 : ℝ) (52571780273/125000000000 : ℝ) (420574242193/1000000000000 : ℝ) (504507794389/1000000000000 : ℝ) (126126948599/250000000000 : ℝ) (497476907417/1000000000000 : ℝ) (19899076297/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66663/524288 : ℝ))) 2 (504507794389/1000000000000 : ℝ) (126126948599/250000000000 : ℝ) (497476907417/1000000000000 : ℝ) (19899076297/40000000000 : ℝ) (500992350903/1000000000000 : ℝ) (500992350911/1000000000000 : ℝ) (500980016887/1000000000000 : ℝ) (100196003379/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66663/524288 : ℝ))) 3 (500992350903/1000000000000 : ℝ) (500992350911/1000000000000 : ℝ) (500980016887/1000000000000 : ℝ) (100196003379/200000000000 : ℝ) (100197236779/200000000000 : ℝ) (500986183903/1000000000000 : ℝ) (500986183857/1000000000000 : ℝ) (250493091933/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66663/524288 : ℝ))) 4 (100197236779/200000000000 : ℝ) (500986183903/1000000000000 : ℝ) (500986183857/1000000000000 : ℝ) (250493091933/500000000000 : ℝ) (125246545969/250000000000 : ℝ) (100197236777/200000000000 : ℝ) (4007889471/8000000000 : ℝ) (100197236777/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66663/524288 : ℝ))) 5 (125246545969/250000000000 : ℝ) (100197236777/200000000000 : ℝ) (4007889471/8000000000 : ℝ) (100197236777/200000000000 : ℝ) (4007889471/8000000000 : ℝ) (100197236777/200000000000 : ℝ) (4007889471/8000000000 : ℝ) (100197236777/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66663/524288 : ℝ))) 6 (4007889471/8000000000 : ℝ) (100197236777/200000000000 : ℝ) (4007889471/8000000000 : ℝ) (100197236777/200000000000 : ℝ) (4007889471/8000000000 : ℝ) (100197236777/200000000000 : ℝ) (4007889471/8000000000 : ℝ) (100197236777/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66663/524288 : ℝ))) 7 (4007889471/8000000000 : ℝ) (100197236777/200000000000 : ℝ) (4007889471/8000000000 : ℝ) (100197236777/200000000000 : ℝ) (4007889471/8000000000 : ℝ) (100197236777/200000000000 : ℝ) (4007889471/8000000000 : ℝ) (100197236777/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66663/524288 : ℝ)) hmem 8 (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ) (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66663/524288 : ℝ))) hcmem 8 (4007889471/8000000000 : ℝ) (100197236777/200000000000 : ℝ) (4007889471/8000000000 : ℝ) (100197236777/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66663/524288 : ℝ)) (15501567297/15625000000 : ℝ) (992100307011/1000000000000 : ℝ) (4007889471/8000000000 : ℝ) (100197236777/200000000000 : ℝ) (396606699869/500000000000 : ℝ) (793213399757/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0590_exp_lower
  have heNumeric : (2054902981579/1000000000000 : ℝ)/4 ≤ Real.exp (-42628206412573/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902981579/1000000000000 : ℝ)/4 ≤ Real.exp ((33331/262144 : ℝ)-(793213399757/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33331/262144 : ℝ) (66663/524288 : ℝ) (793213399757/1000000000000 : ℝ) (2054902981579/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0591; no trusted numerical premise.
theorem cover8_leaf0591_exp_radius : (199603046049185831/200000000000000000 : ℝ) ≤ Real.exp ((-8333/524288 : ℝ)/8) ∧ Real.exp ((-8333/524288 : ℝ)/8) ≤ (249503807561482289/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8333/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0591_exp_lower : (92011352822977739/100000000000000000 : ℝ) ≤ Real.exp ((-85256413493737/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256413493737/128000000000000 : ℝ)/8) ≤ (920113528229777391/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256413493737/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0591_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980594169/200000000000 : ℝ) ≤ 4*Real.exp (66663/524288 : ℝ)*Real.exp (-mu (radius 8 (8333/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (410980594169/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8333/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0591_exp_radius
  have hrNumeric : (246057926479/250000000000 : ℝ) ≤ Real.exp (-8333/524288 : ℝ) ∧ Real.exp (-8333/524288 : ℝ) ≤ (984231705917/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246057926479/250000000000 : ℝ) ≤ (radius 8 (8333/65536 : ℝ)) ∧ (radius 8 (8333/65536 : ℝ)) ≤ (984231705917/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8333/65536 : ℝ)) (246057926479/250000000000 : ℝ) (984231705917/1000000000000 : ℝ) (88441999451/500000000000 : ℝ) (44220999727/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8333/65536 : ℝ)) (246057926479/250000000000 : ℝ) (984231705917/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8333/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246057926479/250000000000 : ℝ) (984231705917/1000000000000 : ℝ) (496057926479/500000000000 : ℝ) (992115852959/1000000000000 : ℝ) (99208452559/100000000000 : ℝ) (992084525591/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8333/65536 : ℝ)) 1 (496057926479/500000000000 : ℝ) (992115852959/1000000000000 : ℝ) (99208452559/100000000000 : ℝ) (992084525591/1000000000000 : ℝ) (496050094637/500000000000 : ℝ) (39684007571/40000000000 : ℝ) (19842003783/20000000000 : ℝ) (31003130911/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8333/65536 : ℝ)) 2 (496050094637/500000000000 : ℝ) (39684007571/40000000000 : ℝ) (19842003783/20000000000 : ℝ) (31003130911/31250000000 : ℝ) (248025047303/250000000000 : ℝ) (496050094607/500000000000 : ℝ) (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8333/65536 : ℝ)) 3 (248025047303/250000000000 : ℝ) (496050094607/500000000000 : ℝ) (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ) (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ) (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8333/65536 : ℝ)) 4 (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ) (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ) (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ) (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8333/65536 : ℝ)) 5 (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ) (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ) (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ) (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8333/65536 : ℝ)) 6 (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ) (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ) (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ) (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8333/65536 : ℝ)) 7 (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ) (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ) (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ) (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8333/65536 : ℝ))) (88441999451/500000000000 : ℝ) (44220999727/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8333/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88441999451/500000000000 : ℝ) (44220999727/250000000000 : ℝ) (588441999451/1000000000000 : ℝ) (294220999727/500000000000 : ℝ) (420575794479/1000000000000 : ℝ) (420575794487/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8333/65536 : ℝ))) 1 (588441999451/1000000000000 : ℝ) (294220999727/500000000000 : ℝ) (420575794479/1000000000000 : ℝ) (420575794487/1000000000000 : ℝ) (100901779393/200000000000 : ℝ) (504508896971/1000000000000 : ℝ) (497478101451/1000000000000 : ℝ) (248739050729/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8333/65536 : ℝ))) 2 (100901779393/200000000000 : ℝ) (504508896971/1000000000000 : ℝ) (497478101451/1000000000000 : ℝ) (248739050729/500000000000 : ℝ) (62624187401/125000000000 : ℝ) (100198699843/200000000000 : ℝ) (500981165541/1000000000000 : ℝ) (125245291387/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8333/65536 : ℝ))) 3 (62624187401/125000000000 : ℝ) (100198699843/200000000000 : ℝ) (500981165541/1000000000000 : ℝ) (125245291387/250000000000 : ℝ) (250493666187/500000000000 : ℝ) (250493666191/500000000000 : ℝ) (31311708271/62500000000 : ℝ) (62623416543/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8333/65536 : ℝ))) 4 (250493666187/500000000000 : ℝ) (250493666191/500000000000 : ℝ) (31311708271/62500000000 : ℝ) (62623416543/125000000000 : ℝ) (100197466471/200000000000 : ℝ) (500987332363/1000000000000 : ℝ) (250493666177/500000000000 : ℝ) (500987332363/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8333/65536 : ℝ))) 5 (100197466471/200000000000 : ℝ) (500987332363/1000000000000 : ℝ) (250493666177/500000000000 : ℝ) (500987332363/1000000000000 : ℝ) (250493666177/500000000000 : ℝ) (500987332363/1000000000000 : ℝ) (250493666177/500000000000 : ℝ) (500987332363/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8333/65536 : ℝ))) 6 (250493666177/500000000000 : ℝ) (500987332363/1000000000000 : ℝ) (250493666177/500000000000 : ℝ) (500987332363/1000000000000 : ℝ) (250493666177/500000000000 : ℝ) (500987332363/1000000000000 : ℝ) (250493666177/500000000000 : ℝ) (500987332363/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8333/65536 : ℝ))) 7 (250493666177/500000000000 : ℝ) (500987332363/1000000000000 : ℝ) (250493666177/500000000000 : ℝ) (500987332363/1000000000000 : ℝ) (250493666177/500000000000 : ℝ) (500987332363/1000000000000 : ℝ) (250493666177/500000000000 : ℝ) (500987332363/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8333/65536 : ℝ)) hmem 8 (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ) (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8333/65536 : ℝ))) hcmem 8 (250493666177/500000000000 : ℝ) (500987332363/1000000000000 : ℝ) (250493666177/500000000000 : ℝ) (500987332363/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8333/65536 : ℝ)) (992100189211/1000000000000 : ℝ) (496050094607/500000000000 : ℝ) (250493666177/500000000000 : ℝ) (500987332363/1000000000000 : ℝ) (99151914039/125000000000 : ℝ) (793215312329/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0591_exp_lower
  have heNumeric : (410980594169/200000000000 : ℝ)/4 ≤ Real.exp (-85256413493737/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980594169/200000000000 : ℝ)/4 ≤ Real.exp ((66663/524288 : ℝ)-(793215312329/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66663/524288 : ℝ) (8333/65536 : ℝ) (793215312329/1000000000000 : ℝ) (410980594169/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0592; no trusted numerical premise.
theorem cover8_leaf0592_exp_radius : (998015200502757959/1000000000000000000 : ℝ) ≤ Real.exp ((-66665/4194304 : ℝ)/8) ∧ Real.exp ((-66665/4194304 : ℝ)/8) ≤ (24950380012568949/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66665/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0592_exp_lower : (460056763815428133/500000000000000000 : ℝ) ≤ Real.exp ((-2131410354007/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131410354007/3200000000000 : ℝ)/8) ≤ (920113527630856267/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131410354007/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0592_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980592029/200000000000 : ℝ) ≤ 4*Real.exp (8333/65536 : ℝ)*Real.exp (-mu (radius 8 (66665/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980592029/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66665/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0592_exp_radius
  have hrNumeric : (984231471257/1000000000000 : ℝ) ≤ Real.exp (-66665/4194304 : ℝ) ∧ Real.exp (-66665/4194304 : ℝ) ≤ (492115735629/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984231471257/1000000000000 : ℝ) ≤ (radius 8 (66665/524288 : ℝ)) ∧ (radius 8 (66665/524288 : ℝ)) ≤ (492115735629/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66665/524288 : ℝ)) (984231471257/1000000000000 : ℝ) (492115735629/500000000000 : ℝ) (35377060921/200000000000 : ℝ) (176885304611/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66665/524288 : ℝ)) (984231471257/1000000000000 : ℝ) (492115735629/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66665/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984231471257/1000000000000 : ℝ) (492115735629/500000000000 : ℝ) (248028933907/250000000000 : ℝ) (992115735629/1000000000000 : ℝ) (248021101831/250000000000 : ℝ) (496042203663/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66665/524288 : ℝ)) 1 (248028933907/250000000000 : ℝ) (992115735629/1000000000000 : ℝ) (248021101831/250000000000 : ℝ) (496042203663/500000000000 : ℝ) (248025017869/250000000000 : ℝ) (496050035739/500000000000 : ℝ) (124012508919/125000000000 : ℝ) (496050035677/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66665/524288 : ℝ)) 2 (248025017869/250000000000 : ℝ) (496050035739/500000000000 : ℝ) (124012508919/125000000000 : ℝ) (496050035677/500000000000 : ℝ) (496050035707/500000000000 : ℝ) (124012508927/125000000000 : ℝ) (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66665/524288 : ℝ)) 3 (496050035707/500000000000 : ℝ) (124012508927/125000000000 : ℝ) (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ) (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ) (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66665/524288 : ℝ)) 4 (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ) (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ) (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ) (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66665/524288 : ℝ)) 5 (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ) (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ) (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ) (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66665/524288 : ℝ)) 6 (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ) (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ) (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ) (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66665/524288 : ℝ)) 7 (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ) (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ) (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ) (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66665/524288 : ℝ))) (35377060921/200000000000 : ℝ) (176885304611/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66665/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35377060921/200000000000 : ℝ) (176885304611/1000000000000 : ℝ) (294221326151/500000000000 : ℝ) (294221326153/500000000000 : ℝ) (105144336689/250000000000 : ℝ) (105144336691/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66665/524288 : ℝ))) 1 (294221326151/500000000000 : ℝ) (294221326153/500000000000 : ℝ) (105144336689/250000000000 : ℝ) (105144336691/250000000000 : ℝ) (504509999529/1000000000000 : ℝ) (100901999907/200000000000 : ℝ) (497479295471/1000000000000 : ℝ) (497479295479/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66665/524288 : ℝ))) 2 (504509999529/1000000000000 : ℝ) (100901999907/200000000000 : ℝ) (497479295471/1000000000000 : ℝ) (497479295479/1000000000000 : ℝ) (200397859/400000000 : ℝ) (500994647507/1000000000000 : ℝ) (250491157091/500000000000 : ℝ) (50098231419/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66665/524288 : ℝ))) 3 (200397859/400000000 : ℝ) (500994647507/1000000000000 : ℝ) (250491157091/500000000000 : ℝ) (50098231419/100000000000 : ℝ) (500988480841/1000000000000 : ℝ) (500988480849/1000000000000 : ℝ) (500988480803/1000000000000 : ℝ) (500988480811/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66665/524288 : ℝ))) 4 (500988480841/1000000000000 : ℝ) (500988480849/1000000000000 : ℝ) (500988480803/1000000000000 : ℝ) (500988480811/1000000000000 : ℝ) (250494240411/500000000000 : ℝ) (50098848083/100000000000 : ℝ) (500988480821/1000000000000 : ℝ) (50098848083/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66665/524288 : ℝ))) 5 (250494240411/500000000000 : ℝ) (50098848083/100000000000 : ℝ) (500988480821/1000000000000 : ℝ) (50098848083/100000000000 : ℝ) (500988480821/1000000000000 : ℝ) (50098848083/100000000000 : ℝ) (500988480821/1000000000000 : ℝ) (50098848083/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66665/524288 : ℝ))) 6 (500988480821/1000000000000 : ℝ) (50098848083/100000000000 : ℝ) (500988480821/1000000000000 : ℝ) (50098848083/100000000000 : ℝ) (500988480821/1000000000000 : ℝ) (50098848083/100000000000 : ℝ) (500988480821/1000000000000 : ℝ) (50098848083/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66665/524288 : ℝ))) 7 (500988480821/1000000000000 : ℝ) (50098848083/100000000000 : ℝ) (500988480821/1000000000000 : ℝ) (50098848083/100000000000 : ℝ) (500988480821/1000000000000 : ℝ) (50098848083/100000000000 : ℝ) (500988480821/1000000000000 : ℝ) (50098848083/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66665/524288 : ℝ)) hmem 8 (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ) (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66665/524288 : ℝ))) hcmem 8 (500988480821/1000000000000 : ℝ) (50098848083/100000000000 : ℝ) (500988480821/1000000000000 : ℝ) (50098848083/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66665/524288 : ℝ)) (992100071413/1000000000000 : ℝ) (124012508927/125000000000 : ℝ) (500988480821/1000000000000 : ℝ) (50098848083/100000000000 : ℝ) (198304306217/250000000000 : ℝ) (158643444977/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0592_exp_lower
  have heNumeric : (410980592029/200000000000 : ℝ)/4 ≤ Real.exp (-2131410354007/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980592029/200000000000 : ℝ)/4 ≤ Real.exp ((8333/65536 : ℝ)-(158643444977/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8333/65536 : ℝ) (66665/524288 : ℝ) (158643444977/200000000000 : ℝ) (410980592029/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0593; no trusted numerical premise.
theorem cover8_leaf0593_exp_radius : (998015170759587649/1000000000000000000 : ℝ) ≤ Real.exp ((-33333/2097152 : ℝ)/8) ∧ Real.exp ((-33333/2097152 : ℝ)/8) ≤ (19960303415191753/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33333/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0593_exp_lower : (230028381758530103/250000000000000000 : ℝ) ≤ Real.exp ((-85256414824391/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256414824391/128000000000000 : ℝ)/8) ≤ (920113527034120413/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256414824391/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0593_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902949483/1000000000000 : ℝ) ≤ 4*Real.exp (66665/524288 : ℝ)*Real.exp (-mu (radius 8 (33333/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902949483/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33333/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0593_exp_radius
  have hrNumeric : (492115618299/500000000000 : ℝ) ≤ Real.exp (-33333/2097152 : ℝ) ∧ Real.exp (-33333/2097152 : ℝ) ≤ (984231236599/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492115618299/500000000000 : ℝ) ≤ (radius 8 (33333/262144 : ℝ)) ∧ (radius 8 (33333/262144 : ℝ)) ≤ (984231236599/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33333/262144 : ℝ)) (492115618299/500000000000 : ℝ) (984231236599/1000000000000 : ℝ) (88443305149/500000000000 : ℝ) (1381926643/7812500000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33333/262144 : ℝ)) (492115618299/500000000000 : ℝ) (984231236599/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33333/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492115618299/500000000000 : ℝ) (984231236599/1000000000000 : ℝ) (992115618299/1000000000000 : ℝ) (9921156183/10000000000 : ℝ) (992084289059/1000000000000 : ℝ) (49604214453/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33333/262144 : ℝ)) 1 (992115618299/1000000000000 : ℝ) (9921156183/10000000000 : ℝ) (992084289059/1000000000000 : ℝ) (49604214453/50000000000 : ℝ) (992099953679/1000000000000 : ℝ) (12401249421/12500000000 : ℝ) (198419990711/200000000000 : ℝ) (992099953557/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33333/262144 : ℝ)) 2 (992099953679/1000000000000 : ℝ) (12401249421/12500000000 : ℝ) (198419990711/200000000000 : ℝ) (992099953557/1000000000000 : ℝ) (992099953617/1000000000000 : ℝ) (992099953619/1000000000000 : ℝ) (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33333/262144 : ℝ)) 3 (992099953617/1000000000000 : ℝ) (992099953619/1000000000000 : ℝ) (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ) (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ) (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33333/262144 : ℝ)) 4 (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ) (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ) (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ) (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33333/262144 : ℝ)) 5 (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ) (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ) (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ) (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33333/262144 : ℝ)) 6 (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ) (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ) (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ) (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33333/262144 : ℝ)) 7 (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ) (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ) (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ) (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33333/262144 : ℝ))) (88443305149/500000000000 : ℝ) (1381926643/7812500000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33333/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88443305149/500000000000 : ℝ) (1381926643/7812500000 : ℝ) (588443305149/1000000000000 : ℝ) (9194426643/15625000000 : ℝ) (52572362377/125000000000 : ℝ) (26286181189/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33333/262144 : ℝ))) 1 (588443305149/1000000000000 : ℝ) (9194426643/15625000000 : ℝ) (52572362377/125000000000 : ℝ) (26286181189/62500000000 : ℝ) (252255551041/500000000000 : ℝ) (63063887761/125000000000 : ℝ) (497480489479/1000000000000 : ℝ) (248740244743/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33333/262144 : ℝ))) 2 (252255551041/500000000000 : ℝ) (63063887761/125000000000 : ℝ) (497480489479/1000000000000 : ℝ) (248740244743/500000000000 : ℝ) (25049789789/50000000000 : ℝ) (500995795787/1000000000000 : ℝ) (125245865703/250000000000 : ℝ) (500983462819/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33333/262144 : ℝ))) 3 (25049789789/50000000000 : ℝ) (500995795787/1000000000000 : ℝ) (125245865703/250000000000 : ℝ) (500983462819/1000000000000 : ℝ) (31311851831/62500000000 : ℝ) (500989629303/1000000000000 : ℝ) (250494814629/500000000000 : ℝ) (250494814633/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33333/262144 : ℝ))) 4 (31311851831/62500000000 : ℝ) (500989629303/1000000000000 : ℝ) (250494814629/500000000000 : ℝ) (250494814633/500000000000 : ℝ) (500989629277/1000000000000 : ℝ) (100197925857/200000000000 : ℝ) (125247407319/250000000000 : ℝ) (100197925857/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33333/262144 : ℝ))) 5 (500989629277/1000000000000 : ℝ) (100197925857/200000000000 : ℝ) (125247407319/250000000000 : ℝ) (100197925857/200000000000 : ℝ) (125247407319/250000000000 : ℝ) (100197925857/200000000000 : ℝ) (125247407319/250000000000 : ℝ) (100197925857/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33333/262144 : ℝ))) 6 (125247407319/250000000000 : ℝ) (100197925857/200000000000 : ℝ) (125247407319/250000000000 : ℝ) (100197925857/200000000000 : ℝ) (125247407319/250000000000 : ℝ) (100197925857/200000000000 : ℝ) (125247407319/250000000000 : ℝ) (100197925857/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33333/262144 : ℝ))) 7 (125247407319/250000000000 : ℝ) (100197925857/200000000000 : ℝ) (125247407319/250000000000 : ℝ) (100197925857/200000000000 : ℝ) (125247407319/250000000000 : ℝ) (100197925857/200000000000 : ℝ) (125247407319/250000000000 : ℝ) (100197925857/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33333/262144 : ℝ)) hmem 8 (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ) (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33333/262144 : ℝ))) hcmem 8 (125247407319/250000000000 : ℝ) (100197925857/200000000000 : ℝ) (125247407319/250000000000 : ℝ) (100197925857/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33333/262144 : ℝ)) (62006247101/62500000000 : ℝ) (992099953619/1000000000000 : ℝ) (125247407319/250000000000 : ℝ) (100197925857/200000000000 : ℝ) (198304784351/250000000000 : ℝ) (396609568711/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0593_exp_lower
  have heNumeric : (2054902949483/1000000000000 : ℝ)/4 ≤ Real.exp (-85256414824391/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902949483/1000000000000 : ℝ)/4 ≤ Real.exp ((66665/524288 : ℝ)-(396609568711/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66665/524288 : ℝ) (33333/262144 : ℝ) (396609568711/500000000000 : ℝ) (2054902949483/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0594; no trusted numerical premise.
theorem cover8_leaf0594_exp_radius : (39920605640656729/40000000000000000 : ℝ) ≤ Real.exp ((-66667/4194304 : ℝ)/8) ∧ Real.exp ((-66667/4194304 : ℝ)/8) ≤ (499007570508209113/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66667/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0594_exp_lower : (460056763219842421/500000000000000000 : ℝ) ≤ Real.exp ((-42628207742971/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628207742971/64000000000000 : ℝ)/8) ≤ (920113526439684843/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628207742971/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0594_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902938863/1000000000000 : ℝ) ≤ 4*Real.exp (33333/262144 : ℝ)*Real.exp (-mu (radius 8 (66667/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902938863/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66667/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0594_exp_radius
  have hrNumeric : (984231001939/1000000000000 : ℝ) ≤ Real.exp (-66667/4194304 : ℝ) ∧ Real.exp (-66667/4194304 : ℝ) ≤ (49211550097/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984231001939/1000000000000 : ℝ) ≤ (radius 8 (66667/524288 : ℝ)) ∧ (radius 8 (66667/524288 : ℝ)) ≤ (49211550097/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66667/524288 : ℝ)) (984231001939/1000000000000 : ℝ) (49211550097/50000000000 : ℝ) (176887915981/1000000000000 : ℝ) (176887915987/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66667/524288 : ℝ)) (984231001939/1000000000000 : ℝ) (49211550097/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66667/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984231001939/1000000000000 : ℝ) (49211550097/50000000000 : ℝ) (992115500969/1000000000000 : ℝ) (99211550097/100000000000 : ℝ) (992084170793/1000000000000 : ℝ) (496042085397/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66667/524288 : ℝ)) 1 (992115500969/1000000000000 : ℝ) (99211550097/100000000000 : ℝ) (992084170793/1000000000000 : ℝ) (496042085397/500000000000 : ℝ) (992099835881/1000000000000 : ℝ) (496049917941/500000000000 : ℝ) (992099835757/1000000000000 : ℝ) (992099835759/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66667/524288 : ℝ)) 2 (992099835881/1000000000000 : ℝ) (496049917941/500000000000 : ℝ) (992099835757/1000000000000 : ℝ) (992099835759/1000000000000 : ℝ) (992099835819/1000000000000 : ℝ) (992099835821/1000000000000 : ℝ) (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66667/524288 : ℝ)) 3 (992099835819/1000000000000 : ℝ) (992099835821/1000000000000 : ℝ) (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ) (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ) (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66667/524288 : ℝ)) 4 (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ) (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ) (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ) (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66667/524288 : ℝ)) 5 (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ) (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ) (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ) (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66667/524288 : ℝ)) 6 (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ) (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ) (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ) (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66667/524288 : ℝ)) 7 (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ) (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ) (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ) (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66667/524288 : ℝ))) (176887915981/1000000000000 : ℝ) (176887915987/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66667/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176887915981/1000000000000 : ℝ) (176887915987/1000000000000 : ℝ) (58844395799/100000000000 : ℝ) (294221978997/500000000000 : ℝ) (210290225629/500000000000 : ℝ) (210290225633/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66667/524288 : ℝ))) 1 (58844395799/100000000000 : ℝ) (294221978997/500000000000 : ℝ) (210290225629/500000000000 : ℝ) (210290225633/500000000000 : ℝ) (31532012789/62500000000 : ℝ) (50451220463/100000000000 : ℝ) (497481683473/1000000000000 : ℝ) (12437042087/25000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66667/524288 : ℝ))) 2 (31532012789/62500000000 : ℝ) (50451220463/100000000000 : ℝ) (497481683473/1000000000000 : ℝ) (12437042087/25000000000 : ℝ) (31312309003/62500000000 : ℝ) (100199388811/200000000000 : ℝ) (500984611429/1000000000000 : ℝ) (125246152859/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66667/524288 : ℝ))) 3 (31312309003/62500000000 : ℝ) (100199388811/200000000000 : ℝ) (500984611429/1000000000000 : ℝ) (125246152859/250000000000 : ℝ) (250495388869/500000000000 : ℝ) (250495388873/500000000000 : ℝ) (5009907777/10000000000 : ℝ) (125247694427/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66667/524288 : ℝ))) 4 (250495388869/500000000000 : ℝ) (250495388873/500000000000 : ℝ) (5009907777/10000000000 : ℝ) (125247694427/250000000000 : ℝ) (500990777719/1000000000000 : ℝ) (500990777727/1000000000000 : ℝ) (250495388859/500000000000 : ℝ) (500990777727/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66667/524288 : ℝ))) 5 (500990777719/1000000000000 : ℝ) (500990777727/1000000000000 : ℝ) (250495388859/500000000000 : ℝ) (500990777727/1000000000000 : ℝ) (250495388859/500000000000 : ℝ) (500990777727/1000000000000 : ℝ) (250495388859/500000000000 : ℝ) (500990777727/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66667/524288 : ℝ))) 6 (250495388859/500000000000 : ℝ) (500990777727/1000000000000 : ℝ) (250495388859/500000000000 : ℝ) (500990777727/1000000000000 : ℝ) (250495388859/500000000000 : ℝ) (500990777727/1000000000000 : ℝ) (250495388859/500000000000 : ℝ) (500990777727/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66667/524288 : ℝ))) 7 (250495388859/500000000000 : ℝ) (500990777727/1000000000000 : ℝ) (250495388859/500000000000 : ℝ) (500990777727/1000000000000 : ℝ) (250495388859/500000000000 : ℝ) (500990777727/1000000000000 : ℝ) (250495388859/500000000000 : ℝ) (500990777727/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66667/524288 : ℝ)) hmem 8 (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ) (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66667/524288 : ℝ))) hcmem 8 (250495388859/500000000000 : ℝ) (500990777727/1000000000000 : ℝ) (250495388859/500000000000 : ℝ) (500990777727/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66667/524288 : ℝ)) (496049917909/500000000000 : ℝ) (992099835821/1000000000000 : ℝ) (250495388859/500000000000 : ℝ) (500990777727/1000000000000 : ℝ) (396610524961/500000000000 : ℝ) (793221049939/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0594_exp_lower
  have heNumeric : (2054902938863/1000000000000 : ℝ)/4 ≤ Real.exp (-42628207742971/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902938863/1000000000000 : ℝ)/4 ≤ Real.exp ((33333/262144 : ℝ)-(793221049939/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33333/262144 : ℝ) (66667/524288 : ℝ) (793221049939/1000000000000 : ℝ) (2054902938863/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0595; no trusted numerical premise.
theorem cover8_leaf0595_exp_radius : (124751888909156211/125000000000000000 : ℝ) ≤ Real.exp ((-16667/1048576 : ℝ)/8) ∧ Real.exp ((-16667/1048576 : ℝ)/8) ≤ (998015111273249689/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16667/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0595_exp_lower : (920113525847089499/1000000000000000000 : ℝ) ≤ Real.exp ((-17051283229089/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051283229089/25600000000000 : ℝ)/8) ≤ (1840227051694179/2000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051283229089/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0595_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (82196117131/40000000000 : ℝ) ≤ 4*Real.exp (66667/524288 : ℝ)*Real.exp (-mu (radius 8 (16667/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (82196117131/40000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16667/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0595_exp_radius
  have hrNumeric : (12302884591/12500000000 : ℝ) ≤ Real.exp (-16667/1048576 : ℝ) ∧ Real.exp (-16667/1048576 : ℝ) ≤ (984230767281/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (12302884591/12500000000 : ℝ) ≤ (radius 8 (16667/131072 : ℝ)) ∧ (radius 8 (16667/131072 : ℝ)) ≤ (984230767281/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16667/131072 : ℝ)) (12302884591/12500000000 : ℝ) (984230767281/1000000000000 : ℝ) (88444610827/500000000000 : ℝ) (8844461083/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16667/131072 : ℝ)) (12302884591/12500000000 : ℝ) (984230767281/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16667/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (12302884591/12500000000 : ℝ) (984230767281/1000000000000 : ℝ) (24802884591/25000000000 : ℝ) (992115383641/1000000000000 : ℝ) (992084052527/1000000000000 : ℝ) (992084052529/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16667/131072 : ℝ)) 1 (24802884591/25000000000 : ℝ) (992115383641/1000000000000 : ℝ) (992084052527/1000000000000 : ℝ) (992084052529/1000000000000 : ℝ) (992099718083/1000000000000 : ℝ) (198419943617/200000000000 : ℝ) (992099717959/1000000000000 : ℝ) (496049858981/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16667/131072 : ℝ)) 2 (992099718083/1000000000000 : ℝ) (198419943617/200000000000 : ℝ) (992099717959/1000000000000 : ℝ) (496049858981/500000000000 : ℝ) (992099718021/1000000000000 : ℝ) (124012464753/125000000000 : ℝ) (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16667/131072 : ℝ)) 3 (992099718021/1000000000000 : ℝ) (124012464753/125000000000 : ℝ) (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ) (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ) (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16667/131072 : ℝ)) 4 (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ) (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ) (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ) (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16667/131072 : ℝ)) 5 (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ) (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ) (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ) (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16667/131072 : ℝ)) 6 (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ) (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ) (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ) (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16667/131072 : ℝ)) 7 (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ) (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ) (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ) (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16667/131072 : ℝ))) (88444610827/500000000000 : ℝ) (8844461083/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16667/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88444610827/500000000000 : ℝ) (8844461083/50000000000 : ℝ) (588444610827/1000000000000 : ℝ) (58844461083/100000000000 : ℝ) (420582003483/1000000000000 : ℝ) (420582003491/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16667/131072 : ℝ))) 1 (588444610827/1000000000000 : ℝ) (58844461083/100000000000 : ℝ) (420582003483/1000000000000 : ℝ) (420582003491/1000000000000 : ℝ) (100902661431/200000000000 : ℝ) (504513307161/1000000000000 : ℝ) (248741438727/500000000000 : ℝ) (497482877461/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16667/131072 : ℝ))) 2 (100902661431/200000000000 : ℝ) (504513307161/1000000000000 : ℝ) (248741438727/500000000000 : ℝ) (497482877461/1000000000000 : ℝ) (31312380769/62500000000 : ℝ) (500998092311/1000000000000 : ℝ) (250492880017/500000000000 : ℝ) (500985760041/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16667/131072 : ℝ))) 3 (31312380769/62500000000 : ℝ) (500998092311/1000000000000 : ℝ) (250492880017/500000000000 : ℝ) (500985760041/1000000000000 : ℝ) (500991926169/1000000000000 : ℝ) (15655997693/31250000000 : ℝ) (500991926131/1000000000000 : ℝ) (500991926139/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16667/131072 : ℝ))) 4 (500991926169/1000000000000 : ℝ) (15655997693/31250000000 : ℝ) (500991926131/1000000000000 : ℝ) (500991926139/1000000000000 : ℝ) (10019838523/20000000000 : ℝ) (250495963079/500000000000 : ℝ) (500991926149/1000000000000 : ℝ) (250495963079/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16667/131072 : ℝ))) 5 (10019838523/20000000000 : ℝ) (250495963079/500000000000 : ℝ) (500991926149/1000000000000 : ℝ) (250495963079/500000000000 : ℝ) (500991926149/1000000000000 : ℝ) (250495963079/500000000000 : ℝ) (500991926149/1000000000000 : ℝ) (250495963079/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16667/131072 : ℝ))) 6 (500991926149/1000000000000 : ℝ) (250495963079/500000000000 : ℝ) (500991926149/1000000000000 : ℝ) (250495963079/500000000000 : ℝ) (500991926149/1000000000000 : ℝ) (250495963079/500000000000 : ℝ) (500991926149/1000000000000 : ℝ) (250495963079/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16667/131072 : ℝ))) 7 (500991926149/1000000000000 : ℝ) (250495963079/500000000000 : ℝ) (500991926149/1000000000000 : ℝ) (250495963079/500000000000 : ℝ) (500991926149/1000000000000 : ℝ) (250495963079/500000000000 : ℝ) (500991926149/1000000000000 : ℝ) (250495963079/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16667/131072 : ℝ)) hmem 8 (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ) (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16667/131072 : ℝ))) hcmem 8 (500991926149/1000000000000 : ℝ) (250495963079/500000000000 : ℝ) (500991926149/1000000000000 : ℝ) (250495963079/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16667/131072 : ℝ)) (49604985901/50000000000 : ℝ) (124012464753/125000000000 : ℝ) (500991926149/1000000000000 : ℝ) (250495963079/500000000000 : ℝ) (793222962421/1000000000000 : ℝ) (19830574061/25000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0595_exp_lower
  have heNumeric : (82196117131/40000000000 : ℝ)/4 ≤ Real.exp (-17051283229089/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (82196117131/40000000000 : ℝ)/4 ≤ Real.exp ((66667/524288 : ℝ)-(19830574061/25000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66667/524288 : ℝ) (16667/131072 : ℝ) (19830574061/25000000000 : ℝ) (82196117131/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0596; no trusted numerical premise.
theorem cover8_leaf0596_exp_radius : (499007540765041019/500000000000000000 : ℝ) ≤ Real.exp ((-66669/4194304 : ℝ)/8) ∧ Real.exp ((-66669/4194304 : ℝ)/8) ≤ (998015081530082039/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66669/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0596_exp_lower : (920113525257024469/1000000000000000000 : ℝ) ≤ Real.exp ((-21314104200533/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314104200533/32000000000000 : ℝ)/8) ≤ (92011352525702447/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314104200533/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0596_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902917733/1000000000000 : ℝ) ≤ 4*Real.exp (16667/131072 : ℝ)*Real.exp (-mu (radius 8 (66669/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902917733/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66669/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0596_exp_radius
  have hrNumeric : (984230532621/1000000000000 : ℝ) ≤ Real.exp (-66669/4194304 : ℝ) ∧ Real.exp (-66669/4194304 : ℝ) ≤ (492115266311/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984230532621/1000000000000 : ℝ) ≤ (radius 8 (66669/524288 : ℝ)) ∧ (radius 8 (66669/524288 : ℝ)) ≤ (492115266311/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66669/524288 : ℝ)) (984230532621/1000000000000 : ℝ) (492115266311/500000000000 : ℝ) (176890527317/1000000000000 : ℝ) (176890527323/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66669/524288 : ℝ)) (984230532621/1000000000000 : ℝ) (492115266311/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66669/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984230532621/1000000000000 : ℝ) (492115266311/500000000000 : ℝ) (99211526631/100000000000 : ℝ) (992115266311/1000000000000 : ℝ) (496041967131/500000000000 : ℝ) (992083934263/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66669/524288 : ℝ)) 1 (99211526631/100000000000 : ℝ) (992115266311/1000000000000 : ℝ) (496041967131/500000000000 : ℝ) (992083934263/1000000000000 : ℝ) (496049800143/500000000000 : ℝ) (992099600287/1000000000000 : ℝ) (496049800081/500000000000 : ℝ) (248024900041/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66669/524288 : ℝ)) 2 (496049800143/500000000000 : ℝ) (992099600287/1000000000000 : ℝ) (496049800081/500000000000 : ℝ) (248024900041/250000000000 : ℝ) (31003112507/31250000000 : ℝ) (496049800113/500000000000 : ℝ) (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66669/524288 : ℝ)) 3 (31003112507/31250000000 : ℝ) (496049800113/500000000000 : ℝ) (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ) (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ) (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66669/524288 : ℝ)) 4 (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ) (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ) (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ) (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66669/524288 : ℝ)) 5 (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ) (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ) (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ) (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66669/524288 : ℝ)) 6 (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ) (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ) (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ) (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66669/524288 : ℝ)) 7 (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ) (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ) (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ) (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66669/524288 : ℝ))) (176890527317/1000000000000 : ℝ) (176890527323/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66669/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176890527317/1000000000000 : ℝ) (176890527323/1000000000000 : ℝ) (294222631829/500000000000 : ℝ) (294222631831/500000000000 : ℝ) (42058355569/100000000000 : ℝ) (210291777849/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66669/524288 : ℝ))) 1 (294222631829/500000000000 : ℝ) (294222631831/500000000000 : ℝ) (42058355569/100000000000 : ℝ) (210291777849/500000000000 : ℝ) (252257204837/500000000000 : ℝ) (6306430121/12500000000 : ℝ) (497484071421/1000000000000 : ℝ) (497484071429/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66669/524288 : ℝ))) 2 (252257204837/500000000000 : ℝ) (6306430121/12500000000 : ℝ) (497484071421/1000000000000 : ℝ) (497484071429/1000000000000 : ℝ) (500999240547/1000000000000 : ℝ) (100199848111/200000000000 : ℝ) (250493454313/500000000000 : ℝ) (250493454317/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66669/524288 : ℝ))) 3 (500999240547/1000000000000 : ℝ) (100199848111/200000000000 : ℝ) (250493454313/500000000000 : ℝ) (250493454317/500000000000 : ℝ) (250496537293/500000000000 : ℝ) (100198614919/200000000000 : ℝ) (125248268637/250000000000 : ℝ) (500993074557/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66669/524288 : ℝ))) 4 (250496537293/500000000000 : ℝ) (100198614919/200000000000 : ℝ) (125248268637/250000000000 : ℝ) (500993074557/1000000000000 : ℝ) (500993074567/1000000000000 : ℝ) (31312067161/62500000000 : ℝ) (250496537283/500000000000 : ℝ) (31312067161/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66669/524288 : ℝ))) 5 (500993074567/1000000000000 : ℝ) (31312067161/62500000000 : ℝ) (250496537283/500000000000 : ℝ) (31312067161/62500000000 : ℝ) (250496537283/500000000000 : ℝ) (31312067161/62500000000 : ℝ) (250496537283/500000000000 : ℝ) (31312067161/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66669/524288 : ℝ))) 6 (250496537283/500000000000 : ℝ) (31312067161/62500000000 : ℝ) (250496537283/500000000000 : ℝ) (31312067161/62500000000 : ℝ) (250496537283/500000000000 : ℝ) (31312067161/62500000000 : ℝ) (250496537283/500000000000 : ℝ) (31312067161/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66669/524288 : ℝ))) 7 (250496537283/500000000000 : ℝ) (31312067161/62500000000 : ℝ) (250496537283/500000000000 : ℝ) (31312067161/62500000000 : ℝ) (250496537283/500000000000 : ℝ) (31312067161/62500000000 : ℝ) (250496537283/500000000000 : ℝ) (31312067161/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66669/524288 : ℝ)) hmem 8 (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ) (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66669/524288 : ℝ))) hcmem 8 (250496537283/500000000000 : ℝ) (31312067161/62500000000 : ℝ) (250496537283/500000000000 : ℝ) (31312067161/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66669/524288 : ℝ)) (992099600223/1000000000000 : ℝ) (496049800113/500000000000 : ℝ) (250496537283/500000000000 : ℝ) (31312067161/62500000000 : ℝ) (7932248749/10000000000 : ℝ) (793224874919/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0596_exp_lower
  have heNumeric : (2054902917733/1000000000000 : ℝ)/4 ≤ Real.exp (-21314104200533/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902917733/1000000000000 : ℝ)/4 ≤ Real.exp ((16667/131072 : ℝ)-(793224874919/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16667/131072 : ℝ) (66669/524288 : ℝ) (793224874919/1000000000000 : ℝ) (2054902917733/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0597; no trusted numerical premise.
theorem cover8_leaf0597_exp_radius : (998015051786915273/1000000000000000000 : ℝ) ≤ Real.exp ((-33335/2097152 : ℝ)/8) ∧ Real.exp ((-33335/2097152 : ℝ)/8) ≤ (499007525893457637/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33335/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0597_exp_lower : (920113524668914681/1000000000000000000 : ℝ) ≤ Real.exp ((-85256417456643/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256417456643/128000000000000 : ℝ)/8) ≤ (460056762334457341/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256417456643/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0597_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (82196116289/40000000000 : ℝ) ≤ 4*Real.exp (66669/524288 : ℝ)*Real.exp (-mu (radius 8 (33335/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (82196116289/40000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33335/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0597_exp_radius
  have hrNumeric : (492115148981/500000000000 : ℝ) ≤ Real.exp (-33335/2097152 : ℝ) ∧ Real.exp (-33335/2097152 : ℝ) ≤ (984230297963/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492115148981/500000000000 : ℝ) ≤ (radius 8 (33335/262144 : ℝ)) ∧ (radius 8 (33335/262144 : ℝ)) ≤ (984230297963/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33335/262144 : ℝ)) (492115148981/500000000000 : ℝ) (984230297963/1000000000000 : ℝ) (17689183297/100000000000 : ℝ) (176891832977/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33335/262144 : ℝ)) (492115148981/500000000000 : ℝ) (984230297963/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33335/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492115148981/500000000000 : ℝ) (984230297963/1000000000000 : ℝ) (992115148981/1000000000000 : ℝ) (496057574491/500000000000 : ℝ) (248020953999/250000000000 : ℝ) (992083815997/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33335/262144 : ℝ)) 1 (992115148981/1000000000000 : ℝ) (496057574491/500000000000 : ℝ) (248020953999/250000000000 : ℝ) (992083815997/1000000000000 : ℝ) (124012435311/125000000000 : ℝ) (99209948249/100000000000 : ℝ) (248024870591/250000000000 : ℝ) (496049741183/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33335/262144 : ℝ)) 2 (124012435311/125000000000 : ℝ) (99209948249/100000000000 : ℝ) (248024870591/250000000000 : ℝ) (496049741183/500000000000 : ℝ) (496049741213/500000000000 : ℝ) (248024870607/250000000000 : ℝ) (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33335/262144 : ℝ)) 3 (496049741213/500000000000 : ℝ) (248024870607/250000000000 : ℝ) (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ) (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ) (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33335/262144 : ℝ)) 4 (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ) (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ) (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ) (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33335/262144 : ℝ)) 5 (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ) (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ) (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ) (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33335/262144 : ℝ)) 6 (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ) (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ) (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ) (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33335/262144 : ℝ)) 7 (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ) (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ) (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ) (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33335/262144 : ℝ))) (17689183297/100000000000 : ℝ) (176891832977/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33335/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17689183297/100000000000 : ℝ) (176891832977/1000000000000 : ℝ) (117689183297/200000000000 : ℝ) (588445916489/1000000000000 : ℝ) (420585107879/1000000000000 : ℝ) (26286569243/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33335/262144 : ℝ))) 1 (117689183297/200000000000 : ℝ) (588445916489/1000000000000 : ℝ) (420585107879/1000000000000 : ℝ) (26286569243/62500000000 : ℝ) (252257756091/500000000000 : ℝ) (504515512189/1000000000000 : ℝ) (3979882123/8000000000 : ℝ) (497485265383/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33335/262144 : ℝ))) 2 (252257756091/500000000000 : ℝ) (504515512189/1000000000000 : ℝ) (3979882123/8000000000 : ℝ) (497485265383/1000000000000 : ℝ) (250500194389/500000000000 : ℝ) (250500194393/500000000000 : ℝ) (250494028603/500000000000 : ℝ) (100197611443/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33335/262144 : ℝ))) 3 (250500194389/500000000000 : ℝ) (250500194393/500000000000 : ℝ) (250494028603/500000000000 : ℝ) (100197611443/200000000000 : ℝ) (31312138937/62500000000 : ℝ) (500994223001/1000000000000 : ℝ) (250497111477/500000000000 : ℝ) (500994222963/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33335/262144 : ℝ))) 4 (31312138937/62500000000 : ℝ) (500994223001/1000000000000 : ℝ) (250497111477/500000000000 : ℝ) (500994222963/1000000000000 : ℝ) (500994222973/1000000000000 : ℝ) (250497111491/500000000000 : ℝ) (125248555743/250000000000 : ℝ) (250497111491/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33335/262144 : ℝ))) 5 (500994222973/1000000000000 : ℝ) (250497111491/500000000000 : ℝ) (125248555743/250000000000 : ℝ) (250497111491/500000000000 : ℝ) (125248555743/250000000000 : ℝ) (250497111491/500000000000 : ℝ) (125248555743/250000000000 : ℝ) (250497111491/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33335/262144 : ℝ))) 6 (125248555743/250000000000 : ℝ) (250497111491/500000000000 : ℝ) (125248555743/250000000000 : ℝ) (250497111491/500000000000 : ℝ) (125248555743/250000000000 : ℝ) (250497111491/500000000000 : ℝ) (125248555743/250000000000 : ℝ) (250497111491/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33335/262144 : ℝ))) 7 (125248555743/250000000000 : ℝ) (250497111491/500000000000 : ℝ) (125248555743/250000000000 : ℝ) (250497111491/500000000000 : ℝ) (125248555743/250000000000 : ℝ) (250497111491/500000000000 : ℝ) (125248555743/250000000000 : ℝ) (250497111491/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33335/262144 : ℝ)) hmem 8 (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ) (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33335/262144 : ℝ))) hcmem 8 (125248555743/250000000000 : ℝ) (250497111491/500000000000 : ℝ) (125248555743/250000000000 : ℝ) (250497111491/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33335/262144 : ℝ)) (39683979297/40000000000 : ℝ) (248024870607/250000000000 : ℝ) (125248555743/250000000000 : ℝ) (250497111491/500000000000 : ℝ) (396613393681/500000000000 : ℝ) (793226787381/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0597_exp_lower
  have heNumeric : (82196116289/40000000000 : ℝ)/4 ≤ Real.exp (-85256417456643/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (82196116289/40000000000 : ℝ)/4 ≤ Real.exp ((66669/524288 : ℝ)-(793226787381/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66669/524288 : ℝ) (33335/262144 : ℝ) (793226787381/1000000000000 : ℝ) (82196116289/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0598; no trusted numerical premise.
theorem cover8_leaf0598_exp_radius : (199603004408749879/200000000000000000 : ℝ) ≤ Real.exp ((-66671/4194304 : ℝ)/8) ∧ Real.exp ((-66671/4194304 : ℝ)/8) ≤ (249503755510937349/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66671/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0598_exp_lower : (920113524083220191/1000000000000000000 : ℝ) ≤ Real.exp ((-42628209054233/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628209054233/64000000000000 : ℝ)/8) ≤ (28753547627600631/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628209054233/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0598_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902896761/1000000000000 : ℝ) ≤ 4*Real.exp (33335/262144 : ℝ)*Real.exp (-mu (radius 8 (66671/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902896761/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66671/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0598_exp_radius
  have hrNumeric : (984230063303/1000000000000 : ℝ) ≤ Real.exp (-66671/4194304 : ℝ) ∧ Real.exp (-66671/4194304 : ℝ) ≤ (123028757913/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984230063303/1000000000000 : ℝ) ≤ (radius 8 (66671/524288 : ℝ)) ∧ (radius 8 (66671/524288 : ℝ)) ≤ (123028757913/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66671/524288 : ℝ)) (984230063303/1000000000000 : ℝ) (123028757913/125000000000 : ℝ) (176893138613/1000000000000 : ℝ) (8844656931/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66671/524288 : ℝ)) (984230063303/1000000000000 : ℝ) (123028757913/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66671/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984230063303/1000000000000 : ℝ) (123028757913/125000000000 : ℝ) (992115031651/1000000000000 : ℝ) (248028757913/250000000000 : ℝ) (99208369773/100000000000 : ℝ) (248020924433/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66671/524288 : ℝ)) 1 (992115031651/1000000000000 : ℝ) (248028757913/250000000000 : ℝ) (99208369773/100000000000 : ℝ) (248020924433/250000000000 : ℝ) (99209936469/100000000000 : ℝ) (248024841173/250000000000 : ℝ) (496049682283/500000000000 : ℝ) (992099364569/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66671/524288 : ℝ)) 2 (99209936469/100000000000 : ℝ) (248024841173/250000000000 : ℝ) (496049682283/500000000000 : ℝ) (992099364569/1000000000000 : ℝ) (248024841157/250000000000 : ℝ) (992099364631/1000000000000 : ℝ) (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66671/524288 : ℝ)) 3 (248024841157/250000000000 : ℝ) (992099364631/1000000000000 : ℝ) (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ) (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ) (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66671/524288 : ℝ)) 4 (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ) (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ) (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ) (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66671/524288 : ℝ)) 5 (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ) (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ) (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ) (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66671/524288 : ℝ)) 6 (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ) (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ) (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ) (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66671/524288 : ℝ)) 7 (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ) (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ) (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ) (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66671/524288 : ℝ))) (176893138613/1000000000000 : ℝ) (8844656931/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66671/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176893138613/1000000000000 : ℝ) (8844656931/50000000000 : ℝ) (294223284653/500000000000 : ℝ) (58844656931/100000000000 : ℝ) (420586660051/1000000000000 : ℝ) (21029333003/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66671/524288 : ℝ))) 1 (294223284653/500000000000 : ℝ) (58844656931/100000000000 : ℝ) (420586660051/1000000000000 : ℝ) (21029333003/50000000000 : ℝ) (252258307339/500000000000 : ℝ) (100903322937/200000000000 : ℝ) (124371614829/250000000000 : ℝ) (124371614831/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66671/524288 : ℝ))) 2 (252258307339/500000000000 : ℝ) (100903322937/200000000000 : ℝ) (124371614829/250000000000 : ℝ) (124371614831/250000000000 : ℝ) (501001536997/1000000000000 : ℝ) (100200307401/200000000000 : ℝ) (250494602887/500000000000 : ℝ) (250494602891/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66671/524288 : ℝ))) 3 (501001536997/1000000000000 : ℝ) (100200307401/200000000000 : ℝ) (250494602887/500000000000 : ℝ) (250494602891/500000000000 : ℝ) (100199074277/200000000000 : ℝ) (250497685697/500000000000 : ℝ) (500995371347/1000000000000 : ℝ) (125248842839/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66671/524288 : ℝ))) 4 (100199074277/200000000000 : ℝ) (250497685697/500000000000 : ℝ) (500995371347/1000000000000 : ℝ) (125248842839/250000000000 : ℝ) (250497685683/500000000000 : ℝ) (4007962971/8000000000 : ℝ) (100199074273/200000000000 : ℝ) (4007962971/8000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66671/524288 : ℝ))) 5 (250497685683/500000000000 : ℝ) (4007962971/8000000000 : ℝ) (100199074273/200000000000 : ℝ) (4007962971/8000000000 : ℝ) (100199074273/200000000000 : ℝ) (4007962971/8000000000 : ℝ) (100199074273/200000000000 : ℝ) (4007962971/8000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66671/524288 : ℝ))) 6 (100199074273/200000000000 : ℝ) (4007962971/8000000000 : ℝ) (100199074273/200000000000 : ℝ) (4007962971/8000000000 : ℝ) (100199074273/200000000000 : ℝ) (4007962971/8000000000 : ℝ) (100199074273/200000000000 : ℝ) (4007962971/8000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66671/524288 : ℝ))) 7 (100199074273/200000000000 : ℝ) (4007962971/8000000000 : ℝ) (100199074273/200000000000 : ℝ) (4007962971/8000000000 : ℝ) (100199074273/200000000000 : ℝ) (4007962971/8000000000 : ℝ) (100199074273/200000000000 : ℝ) (4007962971/8000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66671/524288 : ℝ)) hmem 8 (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ) (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66671/524288 : ℝ))) hcmem 8 (100199074273/200000000000 : ℝ) (4007962971/8000000000 : ℝ) (100199074273/200000000000 : ℝ) (4007962971/8000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66671/524288 : ℝ)) (992099364627/1000000000000 : ℝ) (992099364631/1000000000000 : ℝ) (100199074273/200000000000 : ℝ) (4007962971/8000000000 : ℝ) (396614349901/500000000000 : ℝ) (396614349911/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0598_exp_lower
  have heNumeric : (2054902896761/1000000000000 : ℝ)/4 ≤ Real.exp (-42628209054233/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902896761/1000000000000 : ℝ)/4 ≤ Real.exp ((33335/262144 : ℝ)-(396614349911/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33335/262144 : ℝ) (66671/524288 : ℝ) (396614349911/500000000000 : ℝ) (2054902896761/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0599; no trusted numerical premise.
theorem cover8_leaf0599_exp_radius : (249503748075146101/250000000000000000 : ℝ) ≤ Real.exp ((-4167/262144 : ℝ)/8) ∧ Real.exp ((-4167/262144 : ℝ)/8) ≤ (199602998460116881/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4167/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0599_exp_lower : (92011352350051607/100000000000000000 : ℝ) ≤ Real.exp ((-85256418756961/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256418756961/128000000000000 : ℝ)/8) ≤ (920113523500516071/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256418756961/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0599_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (41098057727/20000000000 : ℝ) ≤ 4*Real.exp (66671/524288 : ℝ)*Real.exp (-mu (radius 8 (4167/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (41098057727/20000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4167/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0599_exp_radius
  have hrNumeric : (196845965729/200000000000 : ℝ) ≤ Real.exp (-4167/262144 : ℝ) ∧ Real.exp (-4167/262144 : ℝ) ≤ (492114914323/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196845965729/200000000000 : ℝ) ≤ (radius 8 (4167/32768 : ℝ)) ∧ (radius 8 (4167/32768 : ℝ)) ≤ (492114914323/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4167/32768 : ℝ)) (196845965729/200000000000 : ℝ) (492114914323/500000000000 : ℝ) (176894444241/1000000000000 : ℝ) (176894444247/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4167/32768 : ℝ)) (196845965729/200000000000 : ℝ) (492114914323/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4167/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196845965729/200000000000 : ℝ) (492114914323/500000000000 : ℝ) (496057457161/500000000000 : ℝ) (992114914323/1000000000000 : ℝ) (198416715893/200000000000 : ℝ) (496041789733/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4167/32768 : ℝ)) 1 (496057457161/500000000000 : ℝ) (992114914323/1000000000000 : ℝ) (198416715893/200000000000 : ℝ) (496041789733/500000000000 : ℝ) (992099246893/1000000000000 : ℝ) (198419849379/200000000000 : ℝ) (992099246769/1000000000000 : ℝ) (992099246771/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4167/32768 : ℝ)) 2 (992099246893/1000000000000 : ℝ) (198419849379/200000000000 : ℝ) (992099246769/1000000000000 : ℝ) (992099246771/1000000000000 : ℝ) (992099246831/1000000000000 : ℝ) (992099246833/1000000000000 : ℝ) (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4167/32768 : ℝ)) 3 (992099246831/1000000000000 : ℝ) (992099246833/1000000000000 : ℝ) (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ) (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ) (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4167/32768 : ℝ)) 4 (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ) (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ) (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ) (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4167/32768 : ℝ)) 5 (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ) (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ) (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ) (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4167/32768 : ℝ)) 6 (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ) (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ) (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ) (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4167/32768 : ℝ)) 7 (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ) (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ) (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ) (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4167/32768 : ℝ))) (176894444241/1000000000000 : ℝ) (176894444247/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4167/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176894444241/1000000000000 : ℝ) (176894444247/1000000000000 : ℝ) (14711180553/25000000000 : ℝ) (147111805531/250000000000 : ℝ) (420588212199/1000000000000 : ℝ) (420588212207/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4167/32768 : ℝ))) 1 (14711180553/25000000000 : ℝ) (147111805531/250000000000 : ℝ) (420588212199/1000000000000 : ℝ) (420588212207/1000000000000 : ℝ) (504517717159/1000000000000 : ℝ) (252258858583/500000000000 : ℝ) (248743826619/500000000000 : ℝ) (248743826623/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4167/32768 : ℝ))) 2 (504517717159/1000000000000 : ℝ) (252258858583/500000000000 : ℝ) (248743826619/500000000000 : ℝ) (248743826623/500000000000 : ℝ) (250501342599/500000000000 : ℝ) (250501342603/500000000000 : ℝ) (125247588581/250000000000 : ℝ) (500990354333/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4167/32768 : ℝ))) 3 (250501342599/500000000000 : ℝ) (250501342603/500000000000 : ℝ) (125247588581/250000000000 : ℝ) (500990354333/1000000000000 : ℝ) (500996519761/1000000000000 : ℝ) (50099651977/100000000000 : ℝ) (500996519723/1000000000000 : ℝ) (125249129933/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4167/32768 : ℝ))) 4 (500996519761/1000000000000 : ℝ) (50099651977/100000000000 : ℝ) (500996519723/1000000000000 : ℝ) (125249129933/250000000000 : ℝ) (250498259871/500000000000 : ℝ) (500996519751/1000000000000 : ℝ) (500996519741/1000000000000 : ℝ) (500996519751/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4167/32768 : ℝ))) 5 (250498259871/500000000000 : ℝ) (500996519751/1000000000000 : ℝ) (500996519741/1000000000000 : ℝ) (500996519751/1000000000000 : ℝ) (500996519741/1000000000000 : ℝ) (500996519751/1000000000000 : ℝ) (500996519741/1000000000000 : ℝ) (500996519751/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4167/32768 : ℝ))) 6 (500996519741/1000000000000 : ℝ) (500996519751/1000000000000 : ℝ) (500996519741/1000000000000 : ℝ) (500996519751/1000000000000 : ℝ) (500996519741/1000000000000 : ℝ) (500996519751/1000000000000 : ℝ) (500996519741/1000000000000 : ℝ) (500996519751/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4167/32768 : ℝ))) 7 (500996519741/1000000000000 : ℝ) (500996519751/1000000000000 : ℝ) (500996519741/1000000000000 : ℝ) (500996519751/1000000000000 : ℝ) (500996519741/1000000000000 : ℝ) (500996519751/1000000000000 : ℝ) (500996519741/1000000000000 : ℝ) (500996519751/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4167/32768 : ℝ)) hmem 8 (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ) (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4167/32768 : ℝ))) hcmem 8 (500996519741/1000000000000 : ℝ) (500996519751/1000000000000 : ℝ) (500996519741/1000000000000 : ℝ) (500996519751/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4167/32768 : ℝ)) (99209924683/100000000000 : ℝ) (992099246833/1000000000000 : ℝ) (500996519741/1000000000000 : ℝ) (500996519751/1000000000000 : ℝ) (793230612217/1000000000000 : ℝ) (793230612237/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0599_exp_lower
  have heNumeric : (41098057727/20000000000 : ℝ)/4 ≤ Real.exp (-85256418756961/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (41098057727/20000000000 : ℝ)/4 ≤ Real.exp ((66671/524288 : ℝ)-(793230612237/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66671/524288 : ℝ) (4167/32768 : ℝ) (793230612237/1000000000000 : ℝ) (41098057727/20000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0575_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0575_certificate
#check SmaleRate.Proofs.cover8_leaf0576_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0576_certificate
#check SmaleRate.Proofs.cover8_leaf0577_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0577_certificate
#check SmaleRate.Proofs.cover8_leaf0578_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0578_certificate
#check SmaleRate.Proofs.cover8_leaf0579_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0579_certificate
#check SmaleRate.Proofs.cover8_leaf0580_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0580_certificate
#check SmaleRate.Proofs.cover8_leaf0581_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0581_certificate
#check SmaleRate.Proofs.cover8_leaf0582_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0582_certificate
#check SmaleRate.Proofs.cover8_leaf0583_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0583_certificate
#check SmaleRate.Proofs.cover8_leaf0584_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0584_certificate
#check SmaleRate.Proofs.cover8_leaf0585_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0585_certificate
#check SmaleRate.Proofs.cover8_leaf0586_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0586_certificate
#check SmaleRate.Proofs.cover8_leaf0587_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0587_certificate
#check SmaleRate.Proofs.cover8_leaf0588_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0588_certificate
#check SmaleRate.Proofs.cover8_leaf0589_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0589_certificate
#check SmaleRate.Proofs.cover8_leaf0590_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0590_certificate
#check SmaleRate.Proofs.cover8_leaf0591_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0591_certificate
#check SmaleRate.Proofs.cover8_leaf0592_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0592_certificate
#check SmaleRate.Proofs.cover8_leaf0593_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0593_certificate
#check SmaleRate.Proofs.cover8_leaf0594_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0594_certificate
#check SmaleRate.Proofs.cover8_leaf0595_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0595_certificate
#check SmaleRate.Proofs.cover8_leaf0596_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0596_certificate
#check SmaleRate.Proofs.cover8_leaf0597_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0597_certificate
#check SmaleRate.Proofs.cover8_leaf0598_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0598_certificate
#check SmaleRate.Proofs.cover8_leaf0599_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0599_certificate
