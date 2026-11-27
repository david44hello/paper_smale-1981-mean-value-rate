/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0250; no trusted numerical premise.
theorem cover8_leaf0250_exp_radius : (49901885816849991/50000000000000000 : ℝ) ≤ Real.exp ((-16477/1048576 : ℝ)/8) ∧ Real.exp ((-16477/1048576 : ℝ)/8) ≤ (998037716336999821/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16477/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0250_exp_lower : (920113967904141619/1000000000000000000 : ℝ) ≤ Real.exp ((-5328495261097/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328495261097/8000000000000 : ℝ)/8) ≤ (46005698395207081/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328495261097/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0250_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513727706577/250000000000 : ℝ) ≤ 4*Real.exp (4119/32768 : ℝ)*Real.exp (-mu (radius 8 (16477/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513727706577/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16477/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0250_exp_radius
  have hrNumeric : (984409124203/1000000000000 : ℝ) ≤ Real.exp (-16477/1048576 : ℝ) ∧ Real.exp (-16477/1048576 : ℝ) ≤ (246102281051/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984409124203/1000000000000 : ℝ) ≤ (radius 8 (16477/131072 : ℝ)) ∧ (radius 8 (16477/131072 : ℝ)) ≤ (246102281051/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16477/131072 : ℝ)) (984409124203/1000000000000 : ℝ) (246102281051/250000000000 : ℝ) (175893934471/1000000000000 : ℝ) (87946967239/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16477/131072 : ℝ)) (984409124203/1000000000000 : ℝ) (246102281051/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16477/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984409124203/1000000000000 : ℝ) (246102281051/250000000000 : ℝ) (992204562101/1000000000000 : ℝ) (496102281051/500000000000 : ℝ) (496086969241/500000000000 : ℝ) (992173938483/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16477/131072 : ℝ)) 1 (992204562101/1000000000000 : ℝ) (496102281051/500000000000 : ℝ) (496086969241/500000000000 : ℝ) (992173938483/1000000000000 : ℝ) (992189250291/1000000000000 : ℝ) (992189250293/1000000000000 : ℝ) (992189250173/1000000000000 : ℝ) (39687570007/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16477/131072 : ℝ)) 2 (992189250291/1000000000000 : ℝ) (992189250293/1000000000000 : ℝ) (992189250173/1000000000000 : ℝ) (39687570007/40000000000 : ℝ) (124023656279/125000000000 : ℝ) (496094625117/500000000000 : ℝ) (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16477/131072 : ℝ)) 3 (124023656279/125000000000 : ℝ) (496094625117/500000000000 : ℝ) (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ) (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ) (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16477/131072 : ℝ)) 4 (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ) (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ) (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ) (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16477/131072 : ℝ)) 5 (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ) (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ) (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ) (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16477/131072 : ℝ)) 6 (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ) (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ) (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ) (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16477/131072 : ℝ)) 7 (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ) (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ) (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ) (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16477/131072 : ℝ))) (175893934471/1000000000000 : ℝ) (87946967239/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16477/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175893934471/1000000000000 : ℝ) (87946967239/500000000000 : ℝ) (117589393447/200000000000 : ℝ) (587946967239/1000000000000 : ℝ) (104849277081/250000000000 : ℝ) (419397108333/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16477/131072 : ℝ))) 1 (117589393447/200000000000 : ℝ) (587946967239/1000000000000 : ℝ) (104849277081/250000000000 : ℝ) (419397108333/1000000000000 : ℝ) (503672037779/1000000000000 : ℝ) (251836018893/500000000000 : ℝ) (124142875829/250000000000 : ℝ) (124142875831/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16477/131072 : ℝ))) 2 (503672037779/1000000000000 : ℝ) (251836018893/500000000000 : ℝ) (124142875829/250000000000 : ℝ) (124142875831/250000000000 : ℝ) (500121770547/1000000000000 : ℝ) (100024354111/200000000000 : ℝ) (25005458453/50000000000 : ℝ) (125027292267/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16477/131072 : ℝ))) 3 (500121770547/1000000000000 : ℝ) (100024354111/200000000000 : ℝ) (25005458453/50000000000 : ℝ) (125027292267/250000000000 : ℝ) (500115469803/1000000000000 : ℝ) (125028867453/250000000000 : ℝ) (500115469763/1000000000000 : ℝ) (125028867443/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16477/131072 : ℝ))) 4 (500115469803/1000000000000 : ℝ) (125028867453/250000000000 : ℝ) (500115469763/1000000000000 : ℝ) (125028867443/250000000000 : ℝ) (500115469783/1000000000000 : ℝ) (15628608431/31250000000 : ℝ) (250057734891/500000000000 : ℝ) (15628608431/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16477/131072 : ℝ))) 5 (500115469783/1000000000000 : ℝ) (15628608431/31250000000 : ℝ) (250057734891/500000000000 : ℝ) (15628608431/31250000000 : ℝ) (250057734891/500000000000 : ℝ) (15628608431/31250000000 : ℝ) (250057734891/500000000000 : ℝ) (15628608431/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16477/131072 : ℝ))) 6 (250057734891/500000000000 : ℝ) (15628608431/31250000000 : ℝ) (250057734891/500000000000 : ℝ) (15628608431/31250000000 : ℝ) (250057734891/500000000000 : ℝ) (15628608431/31250000000 : ℝ) (250057734891/500000000000 : ℝ) (15628608431/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16477/131072 : ℝ))) 7 (250057734891/500000000000 : ℝ) (15628608431/31250000000 : ℝ) (250057734891/500000000000 : ℝ) (15628608431/31250000000 : ℝ) (250057734891/500000000000 : ℝ) (15628608431/31250000000 : ℝ) (250057734891/500000000000 : ℝ) (15628608431/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16477/131072 : ℝ)) hmem 8 (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ) (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16477/131072 : ℝ))) hcmem 8 (250057734891/500000000000 : ℝ) (15628608431/31250000000 : ℝ) (250057734891/500000000000 : ℝ) (15628608431/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16477/131072 : ℝ)) (992189250231/1000000000000 : ℝ) (496094625117/500000000000 : ℝ) (250057734891/500000000000 : ℝ) (15628608431/31250000000 : ℝ) (158352762383/200000000000 : ℝ) (395881905967/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0250_exp_lower
  have heNumeric : (513727706577/250000000000 : ℝ)/4 ≤ Real.exp (-5328495261097/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513727706577/250000000000 : ℝ)/4 ≤ Real.exp ((4119/32768 : ℝ)-(395881905967/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4119/32768 : ℝ) (16477/131072 : ℝ) (395881905967/500000000000 : ℝ) (513727706577/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0251; no trusted numerical premise.
theorem cover8_leaf0251_exp_radius : (499018798680819901/500000000000000000 : ℝ) ≤ Real.exp ((-8239/524288 : ℝ)/8) ∧ Real.exp ((-8239/524288 : ℝ)/8) ≤ (998037597361639803/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8239/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0251_exp_lower : (920113958683165623/1000000000000000000 : ℝ) ≤ Real.exp ((-21313983609907/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313983609907/32000000000000 : ℝ)/8) ≤ (115014244835395703/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313983609907/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0251_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054910661561/1000000000000 : ℝ) ≤ 4*Real.exp (16477/131072 : ℝ)*Real.exp (-mu (radius 8 (8239/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054910661561/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8239/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0251_exp_radius
  have hrNumeric : (492204092699/500000000000 : ℝ) ≤ Real.exp (-8239/524288 : ℝ) ∧ Real.exp (-8239/524288 : ℝ) ≤ (984408185399/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492204092699/500000000000 : ℝ) ≤ (radius 8 (8239/65536 : ℝ)) ∧ (radius 8 (8239/65536 : ℝ)) ≤ (984408185399/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8239/65536 : ℝ)) (492204092699/500000000000 : ℝ) (984408185399/1000000000000 : ℝ) (5496849641/31250000000 : ℝ) (175899188519/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8239/65536 : ℝ)) (492204092699/500000000000 : ℝ) (984408185399/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8239/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492204092699/500000000000 : ℝ) (984408185399/1000000000000 : ℝ) (992204092699/1000000000000 : ℝ) (9922040927/10000000000 : ℝ) (31005420793/31250000000 : ℝ) (496086732689/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8239/65536 : ℝ)) 1 (992204092699/1000000000000 : ℝ) (9922040927/10000000000 : ℝ) (31005420793/31250000000 : ℝ) (496086732689/500000000000 : ℝ) (992188779037/1000000000000 : ℝ) (992188779039/1000000000000 : ℝ) (992188778919/1000000000000 : ℝ) (992188778921/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8239/65536 : ℝ)) 2 (992188779037/1000000000000 : ℝ) (992188779039/1000000000000 : ℝ) (992188778919/1000000000000 : ℝ) (992188778921/1000000000000 : ℝ) (496094389489/500000000000 : ℝ) (49609438949/50000000000 : ℝ) (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8239/65536 : ℝ)) 3 (496094389489/500000000000 : ℝ) (49609438949/50000000000 : ℝ) (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ) (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ) (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8239/65536 : ℝ)) 4 (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ) (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ) (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ) (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8239/65536 : ℝ)) 5 (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ) (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ) (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ) (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8239/65536 : ℝ)) 6 (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ) (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ) (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ) (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8239/65536 : ℝ)) 7 (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ) (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ) (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ) (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8239/65536 : ℝ))) (5496849641/31250000000 : ℝ) (175899188519/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8239/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5496849641/31250000000 : ℝ) (175899188519/1000000000000 : ℝ) (36746849641/62500000000 : ℝ) (29397479713/50000000000 : ℝ) (419403372079/1000000000000 : ℝ) (419403372089/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8239/65536 : ℝ))) 1 (36746849641/62500000000 : ℝ) (29397479713/50000000000 : ℝ) (419403372079/1000000000000 : ℝ) (419403372089/1000000000000 : ℝ) (503676483167/1000000000000 : ℝ) (20147059327/40000000000 : ℝ) (15518010027/31250000000 : ℝ) (496576320873/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8239/65536 : ℝ))) 2 (503676483167/1000000000000 : ℝ) (20147059327/40000000000 : ℝ) (15518010027/31250000000 : ℝ) (496576320873/1000000000000 : ℝ) (100025280403/200000000000 : ℝ) (62515800253/125000000000 : ℝ) (100022760393/200000000000 : ℝ) (20004552079/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8239/65536 : ℝ))) 3 (100025280403/200000000000 : ℝ) (62515800253/125000000000 : ℝ) (100022760393/200000000000 : ℝ) (20004552079/40000000000 : ℝ) (50012010199/100000000000 : ℝ) (250060051/500000000 : ℝ) (10002402039/20000000000 : ℝ) (12503002549/25000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8239/65536 : ℝ))) 4 (50012010199/100000000000 : ℝ) (250060051/500000000 : ℝ) (10002402039/20000000000 : ℝ) (12503002549/25000000000 : ℝ) (50012010197/100000000000 : ℝ) (25006005099/50000000000 : ℝ) (500120101969/1000000000000 : ℝ) (25006005099/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8239/65536 : ℝ))) 5 (50012010197/100000000000 : ℝ) (25006005099/50000000000 : ℝ) (500120101969/1000000000000 : ℝ) (25006005099/50000000000 : ℝ) (500120101969/1000000000000 : ℝ) (25006005099/50000000000 : ℝ) (500120101969/1000000000000 : ℝ) (25006005099/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8239/65536 : ℝ))) 6 (500120101969/1000000000000 : ℝ) (25006005099/50000000000 : ℝ) (500120101969/1000000000000 : ℝ) (25006005099/50000000000 : ℝ) (500120101969/1000000000000 : ℝ) (25006005099/50000000000 : ℝ) (500120101969/1000000000000 : ℝ) (25006005099/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8239/65536 : ℝ))) 7 (500120101969/1000000000000 : ℝ) (25006005099/50000000000 : ℝ) (500120101969/1000000000000 : ℝ) (25006005099/50000000000 : ℝ) (500120101969/1000000000000 : ℝ) (25006005099/50000000000 : ℝ) (500120101969/1000000000000 : ℝ) (25006005099/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8239/65536 : ℝ)) hmem 8 (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ) (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8239/65536 : ℝ))) hcmem 8 (500120101969/1000000000000 : ℝ) (25006005099/50000000000 : ℝ) (500120101969/1000000000000 : ℝ) (25006005099/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8239/65536 : ℝ)) (992188778977/1000000000000 : ℝ) (49609438949/50000000000 : ℝ) (500120101969/1000000000000 : ℝ) (25006005099/50000000000 : ℝ) (19794288037/25000000000 : ℝ) (791771521501/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0251_exp_lower
  have heNumeric : (2054910661561/1000000000000 : ℝ)/4 ≤ Real.exp (-21313983609907/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054910661561/1000000000000 : ℝ)/4 ≤ Real.exp ((16477/131072 : ℝ)-(791771521501/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16477/131072 : ℝ) (8239/65536 : ℝ) (791771521501/1000000000000 : ℝ) (2054910661561/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0252; no trusted numerical premise.
theorem cover8_leaf0252_exp_radius : (998037478386293967/1000000000000000000 : ℝ) ≤ Real.exp ((-16479/1048576 : ℝ)/8) ∧ Real.exp ((-16479/1048576 : ℝ)/8) ≤ (62377342399143373/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16479/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0252_exp_lower : (920113949498074163/1000000000000000000 : ℝ) ≤ Real.exp ((-10656993082721/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656993082721/16000000000000 : ℝ)/8) ≤ (230028487374518541/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656993082721/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0252_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027455248727/500000000000 : ℝ) ≤ 4*Real.exp (8239/65536 : ℝ)*Real.exp (-mu (radius 8 (16479/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027455248727/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16479/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0252_exp_radius
  have hrNumeric : (984407246593/1000000000000 : ℝ) ≤ Real.exp (-16479/1048576 : ℝ) ∧ Real.exp (-16479/1048576 : ℝ) ≤ (492203623297/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984407246593/1000000000000 : ℝ) ≤ (radius 8 (16479/131072 : ℝ)) ∧ (radius 8 (16479/131072 : ℝ)) ≤ (492203623297/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16479/131072 : ℝ)) (984407246593/1000000000000 : ℝ) (492203623297/500000000000 : ℝ) (175904442391/1000000000000 : ℝ) (87952221199/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16479/131072 : ℝ)) (984407246593/1000000000000 : ℝ) (492203623297/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16479/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984407246593/1000000000000 : ℝ) (492203623297/500000000000 : ℝ) (7751590807/7812500000 : ℝ) (992203623297/1000000000000 : ℝ) (992172992271/1000000000000 : ℝ) (992172992273/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16479/131072 : ℝ)) 1 (7751590807/7812500000 : ℝ) (992203623297/1000000000000 : ℝ) (992172992271/1000000000000 : ℝ) (992172992273/1000000000000 : ℝ) (992188307783/1000000000000 : ℝ) (198437661557/200000000000 : ℝ) (198437661533/200000000000 : ℝ) (992188307667/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16479/131072 : ℝ)) 2 (992188307783/1000000000000 : ℝ) (198437661557/200000000000 : ℝ) (198437661533/200000000000 : ℝ) (992188307667/1000000000000 : ℝ) (248047076931/250000000000 : ℝ) (496094153863/500000000000 : ℝ) (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16479/131072 : ℝ)) 3 (248047076931/250000000000 : ℝ) (496094153863/500000000000 : ℝ) (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ) (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ) (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16479/131072 : ℝ)) 4 (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ) (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ) (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ) (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16479/131072 : ℝ)) 5 (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ) (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ) (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ) (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16479/131072 : ℝ)) 6 (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ) (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ) (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ) (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16479/131072 : ℝ)) 7 (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ) (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ) (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ) (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16479/131072 : ℝ))) (175904442391/1000000000000 : ℝ) (87952221199/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16479/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175904442391/1000000000000 : ℝ) (87952221199/500000000000 : ℝ) (117590444239/200000000000 : ℝ) (587952221199/1000000000000 : ℝ) (104852408887/250000000000 : ℝ) (419409635557/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16479/131072 : ℝ))) 1 (117590444239/200000000000 : ℝ) (587952221199/1000000000000 : ℝ) (104852408887/250000000000 : ℝ) (419409635557/1000000000000 : ℝ) (503680928371/1000000000000 : ℝ) (251840464189/500000000000 : ℝ) (248290569097/500000000000 : ℝ) (496581138203/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16479/131072 : ℝ))) 2 (503680928371/1000000000000 : ℝ) (251840464189/500000000000 : ℝ) (248290569097/500000000000 : ℝ) (496581138203/1000000000000 : ℝ) (250065516641/500000000000 : ℝ) (500131033291/1000000000000 : ℝ) (50011843467/100000000000 : ℝ) (500118434679/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16479/131072 : ℝ))) 3 (250065516641/500000000000 : ℝ) (500131033291/1000000000000 : ℝ) (50011843467/100000000000 : ℝ) (500118434679/1000000000000 : ℝ) (62515591747/125000000000 : ℝ) (100024946797/200000000000 : ℝ) (31257795871/62500000000 : ℝ) (250062366973/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16479/131072 : ℝ))) 4 (62515591747/125000000000 : ℝ) (100024946797/200000000000 : ℝ) (31257795871/62500000000 : ℝ) (250062366973/500000000000 : ℝ) (125031183489/250000000000 : ℝ) (250062366983/500000000000 : ℝ) (100024946791/200000000000 : ℝ) (250062366983/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16479/131072 : ℝ))) 5 (125031183489/250000000000 : ℝ) (250062366983/500000000000 : ℝ) (100024946791/200000000000 : ℝ) (250062366983/500000000000 : ℝ) (100024946791/200000000000 : ℝ) (250062366983/500000000000 : ℝ) (100024946791/200000000000 : ℝ) (250062366983/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16479/131072 : ℝ))) 6 (100024946791/200000000000 : ℝ) (250062366983/500000000000 : ℝ) (100024946791/200000000000 : ℝ) (250062366983/500000000000 : ℝ) (100024946791/200000000000 : ℝ) (250062366983/500000000000 : ℝ) (100024946791/200000000000 : ℝ) (250062366983/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16479/131072 : ℝ))) 7 (100024946791/200000000000 : ℝ) (250062366983/500000000000 : ℝ) (100024946791/200000000000 : ℝ) (250062366983/500000000000 : ℝ) (100024946791/200000000000 : ℝ) (250062366983/500000000000 : ℝ) (100024946791/200000000000 : ℝ) (250062366983/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16479/131072 : ℝ)) hmem 8 (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ) (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16479/131072 : ℝ))) hcmem 8 (100024946791/200000000000 : ℝ) (250062366983/500000000000 : ℝ) (100024946791/200000000000 : ℝ) (250062366983/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16479/131072 : ℝ)) (992188307723/1000000000000 : ℝ) (496094153863/500000000000 : ℝ) (100024946791/200000000000 : ℝ) (250062366983/500000000000 : ℝ) (158355846147/200000000000 : ℝ) (197944807689/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0252_exp_lower
  have heNumeric : (1027455248727/500000000000 : ℝ)/4 ≤ Real.exp (-10656993082721/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027455248727/500000000000 : ℝ)/4 ≤ Real.exp ((8239/65536 : ℝ)-(197944807689/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8239/65536 : ℝ) (16479/131072 : ℝ) (197944807689/250000000000 : ℝ) (1027455248727/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0253; no trusted numerical premise.
theorem cover8_leaf0253_exp_radius : (199607471882192463/200000000000000000 : ℝ) ≤ Real.exp ((-515/32768 : ℝ)/8) ∧ Real.exp ((-515/32768 : ℝ)/8) ≤ (249509339852740579/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-515/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0253_exp_lower : (920113940350822481/1000000000000000000 : ℝ) ≤ Real.exp ((-21313988710449/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313988710449/32000000000000 : ℝ)/8) ≤ (460056970175411241/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313988710449/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0253_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256863791753/125000000000 : ℝ) ≤ 4*Real.exp (16479/131072 : ℝ)*Real.exp (-mu (radius 8 (515/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (256863791753/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (515/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0253_exp_radius
  have hrNumeric : (98440630779/100000000000 : ℝ) ≤ Real.exp (-515/32768 : ℝ) ∧ Real.exp (-515/32768 : ℝ) ≤ (984406307791/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98440630779/100000000000 : ℝ) ≤ (radius 8 (515/4096 : ℝ)) ∧ (radius 8 (515/4096 : ℝ)) ≤ (984406307791/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (515/4096 : ℝ)) (98440630779/100000000000 : ℝ) (984406307791/1000000000000 : ℝ) (87954848049/500000000000 : ℝ) (21988712013/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (515/4096 : ℝ)) (98440630779/100000000000 : ℝ) (984406307791/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (515/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98440630779/100000000000 : ℝ) (984406307791/1000000000000 : ℝ) (198440630779/200000000000 : ℝ) (124025394237/125000000000 : ℝ) (496086259583/500000000000 : ℝ) (3875673903/3906250000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (515/4096 : ℝ)) 1 (198440630779/200000000000 : ℝ) (124025394237/125000000000 : ℝ) (496086259583/500000000000 : ℝ) (3875673903/3906250000 : ℝ) (99218783653/100000000000 : ℝ) (248046959133/250000000000 : ℝ) (248046959103/250000000000 : ℝ) (496093918207/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (515/4096 : ℝ)) 2 (99218783653/100000000000 : ℝ) (248046959133/250000000000 : ℝ) (248046959103/250000000000 : ℝ) (496093918207/500000000000 : ℝ) (992187836471/1000000000000 : ℝ) (992187836473/1000000000000 : ℝ) (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (515/4096 : ℝ)) 3 (992187836471/1000000000000 : ℝ) (992187836473/1000000000000 : ℝ) (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ) (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ) (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (515/4096 : ℝ)) 4 (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ) (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ) (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ) (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (515/4096 : ℝ)) 5 (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ) (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ) (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ) (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (515/4096 : ℝ)) 6 (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ) (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ) (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ) (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (515/4096 : ℝ)) 7 (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ) (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ) (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ) (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (515/4096 : ℝ))) (87954848049/500000000000 : ℝ) (21988712013/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (515/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87954848049/500000000000 : ℝ) (21988712013/125000000000 : ℝ) (587954848049/1000000000000 : ℝ) (146988712013/250000000000 : ℝ) (209707949359/500000000000 : ℝ) (209707949363/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (515/4096 : ℝ))) 1 (587954848049/1000000000000 : ℝ) (146988712013/250000000000 : ℝ) (209707949359/500000000000 : ℝ) (209707949363/500000000000 : ℝ) (503685373383/1000000000000 : ℝ) (503685373389/1000000000000 : ℝ) (248292977649/500000000000 : ℝ) (99317191061/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (515/4096 : ℝ))) 2 (503685373383/1000000000000 : ℝ) (503685373389/1000000000000 : ℝ) (248292977649/500000000000 : ℝ) (99317191061/200000000000 : ℝ) (25006783217/50000000000 : ℝ) (500135664347/1000000000000 : ℝ) (100024613433/200000000000 : ℝ) (500123067173/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (515/4096 : ℝ))) 3 (25006783217/50000000000 : ℝ) (500135664347/1000000000000 : ℝ) (100024613433/200000000000 : ℝ) (500123067173/1000000000000 : ℝ) (62516170719/125000000000 : ℝ) (390726067/781250000 : ℝ) (31258085357/62500000000 : ℝ) (500129365721/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (515/4096 : ℝ))) 4 (62516170719/125000000000 : ℝ) (390726067/781250000 : ℝ) (31258085357/62500000000 : ℝ) (500129365721/1000000000000 : ℝ) (125032341433/250000000000 : ℝ) (500129365741/1000000000000 : ℝ) (500129365731/1000000000000 : ℝ) (500129365741/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (515/4096 : ℝ))) 5 (125032341433/250000000000 : ℝ) (500129365741/1000000000000 : ℝ) (500129365731/1000000000000 : ℝ) (500129365741/1000000000000 : ℝ) (500129365731/1000000000000 : ℝ) (500129365741/1000000000000 : ℝ) (500129365731/1000000000000 : ℝ) (500129365741/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (515/4096 : ℝ))) 6 (500129365731/1000000000000 : ℝ) (500129365741/1000000000000 : ℝ) (500129365731/1000000000000 : ℝ) (500129365741/1000000000000 : ℝ) (500129365731/1000000000000 : ℝ) (500129365741/1000000000000 : ℝ) (500129365731/1000000000000 : ℝ) (500129365741/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (515/4096 : ℝ))) 7 (500129365731/1000000000000 : ℝ) (500129365741/1000000000000 : ℝ) (500129365731/1000000000000 : ℝ) (500129365741/1000000000000 : ℝ) (500129365731/1000000000000 : ℝ) (500129365741/1000000000000 : ℝ) (500129365731/1000000000000 : ℝ) (500129365741/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (515/4096 : ℝ)) hmem 8 (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ) (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (515/4096 : ℝ))) hcmem 8 (500129365731/1000000000000 : ℝ) (500129365741/1000000000000 : ℝ) (500129365731/1000000000000 : ℝ) (500129365741/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (515/4096 : ℝ)) (99218783647/100000000000 : ℝ) (992187836473/1000000000000 : ℝ) (500129365731/1000000000000 : ℝ) (500129365741/1000000000000 : ℝ) (791786939663/1000000000000 : ℝ) (395893469841/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0253_exp_lower
  have heNumeric : (256863791753/125000000000 : ℝ)/4 ≤ Real.exp (-21313988710449/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256863791753/125000000000 : ℝ)/4 ≤ Real.exp ((16479/131072 : ℝ)-(395893469841/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16479/131072 : ℝ) (515/4096 : ℝ) (395893469841/500000000000 : ℝ) (256863791753/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0254; no trusted numerical premise.
theorem cover8_leaf0254_exp_radius : (499018620217822423/500000000000000000 : ℝ) ≤ Real.exp ((-16481/1048576 : ℝ)/8) ∧ Real.exp ((-16481/1048576 : ℝ)/8) ≤ (998037240435644847/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16481/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0254_exp_lower : (230028482809748819/250000000000000000 : ℝ) ≤ Real.exp ((-26642489057/40000000000 : ℝ)/8) ∧ Real.exp ((-26642489057/40000000000 : ℝ)/8) ≤ (920113931238995277/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-26642489057/40000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0254_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054910171227/1000000000000 : ℝ) ≤ 4*Real.exp (515/4096 : ℝ)*Real.exp (-mu (radius 8 (16481/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054910171227/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16481/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0254_exp_radius
  have hrNumeric : (984405368987/1000000000000 : ℝ) ≤ Real.exp (-16481/1048576 : ℝ) ∧ Real.exp (-16481/1048576 : ℝ) ≤ (246101342247/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984405368987/1000000000000 : ℝ) ≤ (radius 8 (16481/131072 : ℝ)) ∧ (radius 8 (16481/131072 : ℝ)) ≤ (246101342247/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16481/131072 : ℝ)) (984405368987/1000000000000 : ℝ) (246101342247/250000000000 : ℝ) (87957474821/500000000000 : ℝ) (10994684353/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16481/131072 : ℝ)) (984405368987/1000000000000 : ℝ) (246101342247/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16481/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984405368987/1000000000000 : ℝ) (246101342247/250000000000 : ℝ) (992202684493/1000000000000 : ℝ) (496101342247/500000000000 : ℝ) (496086023031/500000000000 : ℝ) (992172046063/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16481/131072 : ℝ)) 1 (992202684493/1000000000000 : ℝ) (496101342247/500000000000 : ℝ) (496086023031/500000000000 : ℝ) (992172046063/1000000000000 : ℝ) (992187365277/1000000000000 : ℝ) (992187365279/1000000000000 : ℝ) (992187365159/1000000000000 : ℝ) (992187365161/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16481/131072 : ℝ)) 2 (992187365277/1000000000000 : ℝ) (992187365279/1000000000000 : ℝ) (992187365159/1000000000000 : ℝ) (992187365161/1000000000000 : ℝ) (496093682609/500000000000 : ℝ) (49609368261/50000000000 : ℝ) (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16481/131072 : ℝ)) 3 (496093682609/500000000000 : ℝ) (49609368261/50000000000 : ℝ) (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ) (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ) (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16481/131072 : ℝ)) 4 (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ) (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ) (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ) (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16481/131072 : ℝ)) 5 (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ) (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ) (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ) (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16481/131072 : ℝ)) 6 (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ) (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ) (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ) (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16481/131072 : ℝ)) 7 (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ) (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ) (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ) (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16481/131072 : ℝ))) (87957474821/500000000000 : ℝ) (10994684353/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16481/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87957474821/500000000000 : ℝ) (10994684353/62500000000 : ℝ) (587957474821/1000000000000 : ℝ) (73494684353/125000000000 : ℝ) (262138851/625000000 : ℝ) (419422161609/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16481/131072 : ℝ))) 1 (587957474821/1000000000000 : ℝ) (73494684353/125000000000 : ℝ) (262138851/625000000 : ℝ) (419422161609/1000000000000 : ℝ) (50368981821/100000000000 : ℝ) (503689818217/1000000000000 : ℝ) (62073846523/125000000000 : ℝ) (496590772191/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16481/131072 : ℝ))) 2 (50368981821/100000000000 : ℝ) (503689818217/1000000000000 : ℝ) (62073846523/125000000000 : ℝ) (496590772191/1000000000000 : ℝ) (500140295197/1000000000000 : ℝ) (125035073801/250000000000 : ℝ) (250063849729/500000000000 : ℝ) (250063849733/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16481/131072 : ℝ))) 3 (500140295197/1000000000000 : ℝ) (125035073801/250000000000 : ℝ) (250063849729/500000000000 : ℝ) (250063849733/500000000000 : ℝ) (500133997327/1000000000000 : ℝ) (100026799467/200000000000 : ℝ) (500133997287/1000000000000 : ℝ) (31258374831/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16481/131072 : ℝ))) 4 (500133997327/1000000000000 : ℝ) (100026799467/200000000000 : ℝ) (500133997287/1000000000000 : ℝ) (31258374831/62500000000 : ℝ) (500133997307/1000000000000 : ℝ) (125033499329/250000000000 : ℝ) (250066998653/500000000000 : ℝ) (125033499329/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16481/131072 : ℝ))) 5 (500133997307/1000000000000 : ℝ) (125033499329/250000000000 : ℝ) (250066998653/500000000000 : ℝ) (125033499329/250000000000 : ℝ) (250066998653/500000000000 : ℝ) (125033499329/250000000000 : ℝ) (250066998653/500000000000 : ℝ) (125033499329/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16481/131072 : ℝ))) 6 (250066998653/500000000000 : ℝ) (125033499329/250000000000 : ℝ) (250066998653/500000000000 : ℝ) (125033499329/250000000000 : ℝ) (250066998653/500000000000 : ℝ) (125033499329/250000000000 : ℝ) (250066998653/500000000000 : ℝ) (125033499329/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16481/131072 : ℝ))) 7 (250066998653/500000000000 : ℝ) (125033499329/250000000000 : ℝ) (250066998653/500000000000 : ℝ) (125033499329/250000000000 : ℝ) (250066998653/500000000000 : ℝ) (125033499329/250000000000 : ℝ) (250066998653/500000000000 : ℝ) (125033499329/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16481/131072 : ℝ)) hmem 8 (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ) (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16481/131072 : ℝ))) hcmem 8 (250066998653/500000000000 : ℝ) (125033499329/250000000000 : ℝ) (250066998653/500000000000 : ℝ) (125033499329/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16481/131072 : ℝ)) (992187365217/1000000000000 : ℝ) (49609368261/50000000000 : ℝ) (250066998653/500000000000 : ℝ) (125033499329/250000000000 : ℝ) (791794648281/1000000000000 : ℝ) (7917946483/10000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0254_exp_lower
  have heNumeric : (2054910171227/1000000000000 : ℝ)/4 ≤ Real.exp (-26642489057/40000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054910171227/1000000000000 : ℝ)/4 ≤ Real.exp ((515/4096 : ℝ)-(7917946483/10000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (515/4096 : ℝ) (16481/131072 : ℝ) (7917946483/10000000000 : ℝ) (2054910171227/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0255; no trusted numerical premise.
theorem cover8_leaf0255_exp_radius : (24950928036508539/25000000000000000 : ℝ) ≤ Real.exp ((-8241/524288 : ℝ)/8) ∧ Real.exp ((-8241/524288 : ℝ)/8) ≤ (998037121460341561/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8241/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0255_exp_lower : (28753560067652901/31250000000000000 : ℝ) ≤ Real.exp ((-4262798754051/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262798754051/6400000000000 : ℝ)/8) ≤ (920113922164892833/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262798754051/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0255_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431875569/62500000000 : ℝ) ≤ 4*Real.exp (16481/131072 : ℝ)*Real.exp (-mu (radius 8 (8241/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (128431875569/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8241/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0255_exp_radius
  have hrNumeric : (492202215093/500000000000 : ℝ) ≤ Real.exp (-8241/524288 : ℝ) ∧ Real.exp (-8241/524288 : ℝ) ≤ (984404430187/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492202215093/500000000000 : ℝ) ≤ (radius 8 (8241/65536 : ℝ)) ∧ (radius 8 (8241/65536 : ℝ)) ≤ (984404430187/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8241/65536 : ℝ)) (492202215093/500000000000 : ℝ) (984404430187/1000000000000 : ℝ) (175920203013/1000000000000 : ℝ) (175920203019/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8241/65536 : ℝ)) (492202215093/500000000000 : ℝ) (984404430187/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8241/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492202215093/500000000000 : ℝ) (984404430187/1000000000000 : ℝ) (992202215093/1000000000000 : ℝ) (496101107547/500000000000 : ℝ) (496085786479/500000000000 : ℝ) (992171572959/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8241/65536 : ℝ)) 1 (992202215093/1000000000000 : ℝ) (496101107547/500000000000 : ℝ) (496085786479/500000000000 : ℝ) (992171572959/1000000000000 : ℝ) (39687475761/40000000000 : ℝ) (992186894027/1000000000000 : ℝ) (992186893907/1000000000000 : ℝ) (992186893909/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8241/65536 : ℝ)) 2 (39687475761/40000000000 : ℝ) (992186894027/1000000000000 : ℝ) (992186893907/1000000000000 : ℝ) (992186893909/1000000000000 : ℝ) (496093446983/500000000000 : ℝ) (62011680873/62500000000 : ℝ) (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8241/65536 : ℝ)) 3 (496093446983/500000000000 : ℝ) (62011680873/62500000000 : ℝ) (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ) (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ) (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8241/65536 : ℝ)) 4 (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ) (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ) (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ) (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8241/65536 : ℝ)) 5 (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ) (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ) (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ) (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8241/65536 : ℝ)) 6 (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ) (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ) (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ) (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8241/65536 : ℝ)) 7 (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ) (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ) (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ) (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8241/65536 : ℝ))) (175920203013/1000000000000 : ℝ) (175920203019/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8241/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175920203013/1000000000000 : ℝ) (175920203019/1000000000000 : ℝ) (293980050753/500000000000 : ℝ) (58796010151/100000000000 : ℝ) (419428424183/1000000000000 : ℝ) (419428424191/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8241/65536 : ℝ))) 1 (293980050753/500000000000 : ℝ) (58796010151/100000000000 : ℝ) (419428424183/1000000000000 : ℝ) (419428424191/1000000000000 : ℝ) (125923565711/250000000000 : ℝ) (503694262851/1000000000000 : ℝ) (496595588841/1000000000000 : ℝ) (496595588849/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8241/65536 : ℝ))) 2 (125923565711/250000000000 : ℝ) (503694262851/1000000000000 : ℝ) (496595588841/1000000000000 : ℝ) (496595588849/1000000000000 : ℝ) (250072462921/500000000000 : ℝ) (10002898517/20000000000 : ℝ) (500132331541/1000000000000 : ℝ) (500132331549/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8241/65536 : ℝ))) 3 (250072462921/500000000000 : ℝ) (10002898517/20000000000 : ℝ) (500132331541/1000000000000 : ℝ) (500132331549/1000000000000 : ℝ) (500138628691/1000000000000 : ℝ) (5001386287/10000000000 : ℝ) (500138628651/1000000000000 : ℝ) (25006931433/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8241/65536 : ℝ))) 4 (500138628691/1000000000000 : ℝ) (5001386287/10000000000 : ℝ) (500138628651/1000000000000 : ℝ) (25006931433/50000000000 : ℝ) (500138628671/1000000000000 : ℝ) (12503465717/25000000000 : ℝ) (50013862867/100000000000 : ℝ) (12503465717/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8241/65536 : ℝ))) 5 (500138628671/1000000000000 : ℝ) (12503465717/25000000000 : ℝ) (50013862867/100000000000 : ℝ) (12503465717/25000000000 : ℝ) (50013862867/100000000000 : ℝ) (12503465717/25000000000 : ℝ) (50013862867/100000000000 : ℝ) (12503465717/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8241/65536 : ℝ))) 6 (50013862867/100000000000 : ℝ) (12503465717/25000000000 : ℝ) (50013862867/100000000000 : ℝ) (12503465717/25000000000 : ℝ) (50013862867/100000000000 : ℝ) (12503465717/25000000000 : ℝ) (50013862867/100000000000 : ℝ) (12503465717/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8241/65536 : ℝ))) 7 (50013862867/100000000000 : ℝ) (12503465717/25000000000 : ℝ) (50013862867/100000000000 : ℝ) (12503465717/25000000000 : ℝ) (50013862867/100000000000 : ℝ) (12503465717/25000000000 : ℝ) (50013862867/100000000000 : ℝ) (12503465717/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8241/65536 : ℝ)) hmem 8 (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ) (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8241/65536 : ℝ))) hcmem 8 (50013862867/100000000000 : ℝ) (12503465717/25000000000 : ℝ) (50013862867/100000000000 : ℝ) (12503465717/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8241/65536 : ℝ)) (198437378793/200000000000 : ℝ) (62011680873/62500000000 : ℝ) (50013862867/100000000000 : ℝ) (12503465717/25000000000 : ℝ) (791802356571/1000000000000 : ℝ) (79180235659/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0255_exp_lower
  have heNumeric : (128431875569/62500000000 : ℝ)/4 ≤ Real.exp (-4262798754051/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431875569/62500000000 : ℝ)/4 ≤ Real.exp ((16481/131072 : ℝ)-(79180235659/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16481/131072 : ℝ) (8241/65536 : ℝ) (79180235659/100000000000 : ℝ) (128431875569/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0256; no trusted numerical premise.
theorem cover8_leaf0256_exp_radius : (998037002485052457/1000000000000000000 : ℝ) ≤ Real.exp ((-16483/1048576 : ℝ)/8) ∧ Real.exp ((-16483/1048576 : ℝ)/8) ≤ (499018501242526229/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16483/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0256_exp_lower : (57507119570388429/62500000000000000 : ℝ) ≤ Real.exp ((-10656998142527/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656998142527/16000000000000 : ℝ)/8) ≤ (184022782625242973/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656998142527/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0256_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027454923807/500000000000 : ℝ) ≤ 4*Real.exp (8241/65536 : ℝ)*Real.exp (-mu (radius 8 (16483/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027454923807/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16483/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0256_exp_radius
  have hrNumeric : (196880698277/200000000000 : ℝ) ≤ Real.exp (-16483/1048576 : ℝ) ∧ Real.exp (-16483/1048576 : ℝ) ≤ (492201745693/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196880698277/200000000000 : ℝ) ≤ (radius 8 (16483/131072 : ℝ)) ∧ (radius 8 (16483/131072 : ℝ)) ≤ (492201745693/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16483/131072 : ℝ)) (196880698277/200000000000 : ℝ) (492201745693/500000000000 : ℝ) (87962728111/500000000000 : ℝ) (43981364057/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16483/131072 : ℝ)) (196880698277/200000000000 : ℝ) (492201745693/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16483/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196880698277/200000000000 : ℝ) (492201745693/500000000000 : ℝ) (248050436423/250000000000 : ℝ) (992201745693/1000000000000 : ℝ) (992171099853/1000000000000 : ℝ) (198434219971/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16483/131072 : ℝ)) 1 (248050436423/250000000000 : ℝ) (992201745693/1000000000000 : ℝ) (992171099853/1000000000000 : ℝ) (198434219971/200000000000 : ℝ) (248046605693/250000000000 : ℝ) (496093211387/500000000000 : ℝ) (496093211327/500000000000 : ℝ) (7751456427/7812500000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16483/131072 : ℝ)) 2 (248046605693/250000000000 : ℝ) (496093211387/500000000000 : ℝ) (496093211327/500000000000 : ℝ) (7751456427/7812500000 : ℝ) (992186422713/1000000000000 : ℝ) (198437284543/200000000000 : ℝ) (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16483/131072 : ℝ)) 3 (992186422713/1000000000000 : ℝ) (198437284543/200000000000 : ℝ) (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ) (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ) (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16483/131072 : ℝ)) 4 (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ) (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ) (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ) (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16483/131072 : ℝ)) 5 (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ) (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ) (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ) (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16483/131072 : ℝ)) 6 (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ) (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ) (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ) (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16483/131072 : ℝ)) 7 (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ) (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ) (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ) (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16483/131072 : ℝ))) (87962728111/500000000000 : ℝ) (43981364057/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16483/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87962728111/500000000000 : ℝ) (43981364057/250000000000 : ℝ) (587962728111/1000000000000 : ℝ) (293981364057/500000000000 : ℝ) (419434686479/1000000000000 : ℝ) (419434686487/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16483/131072 : ℝ))) 1 (587962728111/1000000000000 : ℝ) (293981364057/500000000000 : ℝ) (419434686479/1000000000000 : ℝ) (419434686487/1000000000000 : ℝ) (100739741459/200000000000 : ℝ) (503698707301/1000000000000 : ℝ) (248300202641/500000000000 : ℝ) (496600405289/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16483/131072 : ℝ))) 2 (100739741459/200000000000 : ℝ) (503698707301/1000000000000 : ℝ) (248300202641/500000000000 : ℝ) (496600405289/1000000000000 : ℝ) (7814836817/15625000000 : ℝ) (100029911259/200000000000 : ℝ) (500136963423/1000000000000 : ℝ) (500136963431/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16483/131072 : ℝ))) 3 (7814836817/15625000000 : ℝ) (100029911259/200000000000 : ℝ) (500136963423/1000000000000 : ℝ) (500136963431/1000000000000 : ℝ) (100028651971/200000000000 : ℝ) (500143259863/1000000000000 : ℝ) (100028651963/200000000000 : ℝ) (31258953739/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16483/131072 : ℝ))) 4 (100028651971/200000000000 : ℝ) (500143259863/1000000000000 : ℝ) (100028651963/200000000000 : ℝ) (31258953739/62500000000 : ℝ) (100028651967/200000000000 : ℝ) (125035814961/250000000000 : ℝ) (250071629917/500000000000 : ℝ) (125035814961/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16483/131072 : ℝ))) 5 (100028651967/200000000000 : ℝ) (125035814961/250000000000 : ℝ) (250071629917/500000000000 : ℝ) (125035814961/250000000000 : ℝ) (250071629917/500000000000 : ℝ) (125035814961/250000000000 : ℝ) (250071629917/500000000000 : ℝ) (125035814961/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16483/131072 : ℝ))) 6 (250071629917/500000000000 : ℝ) (125035814961/250000000000 : ℝ) (250071629917/500000000000 : ℝ) (125035814961/250000000000 : ℝ) (250071629917/500000000000 : ℝ) (125035814961/250000000000 : ℝ) (250071629917/500000000000 : ℝ) (125035814961/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16483/131072 : ℝ))) 7 (250071629917/500000000000 : ℝ) (125035814961/250000000000 : ℝ) (250071629917/500000000000 : ℝ) (125035814961/250000000000 : ℝ) (250071629917/500000000000 : ℝ) (125035814961/250000000000 : ℝ) (250071629917/500000000000 : ℝ) (125035814961/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16483/131072 : ℝ)) hmem 8 (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ) (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16483/131072 : ℝ))) hcmem 8 (250071629917/500000000000 : ℝ) (125035814961/250000000000 : ℝ) (250071629917/500000000000 : ℝ) (125035814961/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16483/131072 : ℝ)) (124023302839/125000000000 : ℝ) (198437284543/200000000000 : ℝ) (250071629917/500000000000 : ℝ) (125035814961/250000000000 : ℝ) (98976258069/125000000000 : ℝ) (197952516143/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0256_exp_lower
  have heNumeric : (1027454923807/500000000000 : ℝ)/4 ≤ Real.exp (-10656998142527/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027454923807/500000000000 : ℝ)/4 ≤ Real.exp ((8241/65536 : ℝ)-(197952516143/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8241/65536 : ℝ) (16483/131072 : ℝ) (197952516143/250000000000 : ℝ) (1027454923807/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0257; no trusted numerical premise.
theorem cover8_leaf0257_exp_radius : (998036883509777537/1000000000000000000 : ℝ) ≤ Real.exp ((-4121/262144 : ℝ)/8) ∧ Real.exp ((-4121/262144 : ℝ)/8) ≤ (499018441754888769/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4121/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0257_exp_lower : (46005695206217077/50000000000000000 : ℝ) ≤ Real.exp ((-21313998789613/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313998789613/32000000000000 : ℝ)/8) ≤ (920113904124341541/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313998789613/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0257_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054909686781/1000000000000 : ℝ) ≤ 4*Real.exp (16483/131072 : ℝ)*Real.exp (-mu (radius 8 (4121/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054909686781/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4121/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0257_exp_radius
  have hrNumeric : (196880510517/200000000000 : ℝ) ≤ Real.exp (-4121/262144 : ℝ) ∧ Real.exp (-4121/262144 : ℝ) ≤ (492201276293/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196880510517/200000000000 : ℝ) ≤ (radius 8 (4121/32768 : ℝ)) ∧ (radius 8 (4121/32768 : ℝ)) ≤ (492201276293/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4121/32768 : ℝ)) (196880510517/200000000000 : ℝ) (492201276293/500000000000 : ℝ) (10995669329/62500000000 : ℝ) (17593070927/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4121/32768 : ℝ)) (196880510517/200000000000 : ℝ) (492201276293/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4121/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196880510517/200000000000 : ℝ) (492201276293/500000000000 : ℝ) (248050319073/250000000000 : ℝ) (992201276293/1000000000000 : ℝ) (992170626749/1000000000000 : ℝ) (992170626751/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4121/32768 : ℝ)) 1 (248050319073/250000000000 : ℝ) (992201276293/1000000000000 : ℝ) (992170626749/1000000000000 : ℝ) (992170626751/1000000000000 : ℝ) (6201162197/6250000000 : ℝ) (496092975761/500000000000 : ℝ) (496092975701/500000000000 : ℝ) (248046487851/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4121/32768 : ℝ)) 2 (6201162197/6250000000 : ℝ) (496092975761/500000000000 : ℝ) (496092975701/500000000000 : ℝ) (248046487851/250000000000 : ℝ) (992185951461/1000000000000 : ℝ) (992185951463/1000000000000 : ℝ) (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4121/32768 : ℝ)) 3 (992185951461/1000000000000 : ℝ) (992185951463/1000000000000 : ℝ) (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ) (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ) (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4121/32768 : ℝ)) 4 (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ) (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ) (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ) (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4121/32768 : ℝ)) 5 (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ) (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ) (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ) (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4121/32768 : ℝ)) 6 (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ) (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ) (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ) (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4121/32768 : ℝ)) 7 (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ) (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ) (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ) (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4121/32768 : ℝ))) (10995669329/62500000000 : ℝ) (17593070927/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4121/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (10995669329/62500000000 : ℝ) (17593070927/100000000000 : ℝ) (73495669329/125000000000 : ℝ) (117593070927/200000000000 : ℝ) (209720474241/500000000000 : ℝ) (41944094849/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4121/32768 : ℝ))) 1 (73495669329/125000000000 : ℝ) (117593070927/200000000000 : ℝ) (209720474241/500000000000 : ℝ) (41944094849/100000000000 : ℝ) (503703151557/1000000000000 : ℝ) (503703151563/1000000000000 : ℝ) (993210443/2000000000 : ℝ) (496605221507/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4121/32768 : ℝ))) 2 (503703151557/1000000000000 : ℝ) (503703151563/1000000000000 : ℝ) (993210443/2000000000 : ℝ) (496605221507/1000000000000 : ℝ) (15629818329/31250000000 : ℝ) (100030837307/200000000000 : ℝ) (5001415951/10000000000 : ℝ) (500141595107/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4121/32768 : ℝ))) 3 (15629818329/31250000000 : ℝ) (100030837307/200000000000 : ℝ) (5001415951/10000000000 : ℝ) (500141595107/1000000000000 : ℝ) (250073945407/500000000000 : ℝ) (500147890821/1000000000000 : ℝ) (250073945387/500000000000 : ℝ) (250073945391/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4121/32768 : ℝ))) 4 (250073945407/500000000000 : ℝ) (500147890821/1000000000000 : ℝ) (250073945387/500000000000 : ℝ) (250073945391/500000000000 : ℝ) (250073945397/500000000000 : ℝ) (250073945401/500000000000 : ℝ) (500147890793/1000000000000 : ℝ) (250073945401/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4121/32768 : ℝ))) 5 (250073945397/500000000000 : ℝ) (250073945401/500000000000 : ℝ) (500147890793/1000000000000 : ℝ) (250073945401/500000000000 : ℝ) (500147890793/1000000000000 : ℝ) (250073945401/500000000000 : ℝ) (500147890793/1000000000000 : ℝ) (250073945401/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4121/32768 : ℝ))) 6 (500147890793/1000000000000 : ℝ) (250073945401/500000000000 : ℝ) (500147890793/1000000000000 : ℝ) (250073945401/500000000000 : ℝ) (500147890793/1000000000000 : ℝ) (250073945401/500000000000 : ℝ) (500147890793/1000000000000 : ℝ) (250073945401/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4121/32768 : ℝ))) 7 (500147890793/1000000000000 : ℝ) (250073945401/500000000000 : ℝ) (500147890793/1000000000000 : ℝ) (250073945401/500000000000 : ℝ) (500147890793/1000000000000 : ℝ) (250073945401/500000000000 : ℝ) (500147890793/1000000000000 : ℝ) (250073945401/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4121/32768 : ℝ)) hmem 8 (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ) (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4121/32768 : ℝ))) hcmem 8 (500147890793/1000000000000 : ℝ) (250073945401/500000000000 : ℝ) (500147890793/1000000000000 : ℝ) (250073945401/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4121/32768 : ℝ)) (49609297573/50000000000 : ℝ) (992185951463/1000000000000 : ℝ) (500147890793/1000000000000 : ℝ) (250073945401/500000000000 : ℝ) (98977221527/125000000000 : ℝ) (395908886117/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0257_exp_lower
  have heNumeric : (2054909686781/1000000000000 : ℝ)/4 ≤ Real.exp (-21313998789613/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054909686781/1000000000000 : ℝ)/4 ≤ Real.exp ((16483/131072 : ℝ)-(395908886117/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16483/131072 : ℝ) (4121/32768 : ℝ) (395908886117/500000000000 : ℝ) (2054909686781/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0258; no trusted numerical premise.
theorem cover8_leaf0258_exp_radius : (623772977834073/625000000000000 : ℝ) ≤ Real.exp ((-16485/1048576 : ℝ)/8) ∧ Real.exp ((-16485/1048576 : ℝ)/8) ≤ (998036764534516801/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16485/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0258_exp_lower : (46005694757963643/50000000000000000 : ℝ) ≤ Real.exp ((-5328500320983/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328500320983/8000000000000 : ℝ)/8) ≤ (920113895159272861/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328500320983/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0258_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027454763303/500000000000 : ℝ) ≤ 4*Real.exp (4121/32768 : ℝ)*Real.exp (-mu (radius 8 (16485/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027454763303/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16485/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0258_exp_radius
  have hrNumeric : (492200806893/500000000000 : ℝ) ≤ Real.exp (-16485/1048576 : ℝ) ∧ Real.exp (-16485/1048576 : ℝ) ≤ (984401613787/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492200806893/500000000000 : ℝ) ≤ (radius 8 (16485/131072 : ℝ)) ∧ (radius 8 (16485/131072 : ℝ)) ≤ (984401613787/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16485/131072 : ℝ)) (492200806893/500000000000 : ℝ) (984401613787/1000000000000 : ℝ) (87967981069/500000000000 : ℝ) (5497998817/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16485/131072 : ℝ)) (492200806893/500000000000 : ℝ) (984401613787/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16485/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492200806893/500000000000 : ℝ) (984401613787/1000000000000 : ℝ) (992200806893/1000000000000 : ℝ) (496100403447/500000000000 : ℝ) (496085076823/500000000000 : ℝ) (992170153647/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16485/131072 : ℝ)) 1 (992200806893/1000000000000 : ℝ) (496100403447/500000000000 : ℝ) (496085076823/500000000000 : ℝ) (992170153647/1000000000000 : ℝ) (992185480269/1000000000000 : ℝ) (992185480271/1000000000000 : ℝ) (992185480151/1000000000000 : ℝ) (992185480153/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16485/131072 : ℝ)) 2 (992185480269/1000000000000 : ℝ) (992185480271/1000000000000 : ℝ) (992185480151/1000000000000 : ℝ) (992185480153/1000000000000 : ℝ) (99218548021/100000000000 : ℝ) (248046370053/250000000000 : ℝ) (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16485/131072 : ℝ)) 3 (99218548021/100000000000 : ℝ) (248046370053/250000000000 : ℝ) (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ) (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ) (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16485/131072 : ℝ)) 4 (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ) (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ) (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ) (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16485/131072 : ℝ)) 5 (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ) (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ) (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ) (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16485/131072 : ℝ)) 6 (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ) (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ) (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ) (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16485/131072 : ℝ)) 7 (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ) (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ) (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ) (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16485/131072 : ℝ))) (87967981069/500000000000 : ℝ) (5497998817/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16485/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87967981069/500000000000 : ℝ) (5497998817/31250000000 : ℝ) (587967981069/1000000000000 : ℝ) (36747998817/62500000000 : ℝ) (26215450637/62500000000 : ℝ) (2097236051/5000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16485/131072 : ℝ))) 1 (587967981069/1000000000000 : ℝ) (36747998817/62500000000 : ℝ) (26215450637/62500000000 : ℝ) (2097236051/5000000000 : ℝ) (50370759563/100000000000 : ℝ) (125926898909/250000000000 : ℝ) (99322007499/200000000000 : ℝ) (248305018751/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16485/131072 : ℝ))) 2 (50370759563/100000000000 : ℝ) (125926898909/250000000000 : ℝ) (99322007499/200000000000 : ℝ) (248305018751/500000000000 : ℝ) (250079408281/500000000000 : ℝ) (500158816569/1000000000000 : ℝ) (50014622657/100000000000 : ℝ) (500146226577/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16485/131072 : ℝ))) 3 (250079408281/500000000000 : ℝ) (500158816569/1000000000000 : ℝ) (50014622657/100000000000 : ℝ) (500146226577/1000000000000 : ℝ) (250076260783/500000000000 : ℝ) (500152521573/1000000000000 : ℝ) (250076260763/500000000000 : ℝ) (250076260767/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16485/131072 : ℝ))) 4 (250076260783/500000000000 : ℝ) (500152521573/1000000000000 : ℝ) (250076260763/500000000000 : ℝ) (250076260767/500000000000 : ℝ) (250076260773/500000000000 : ℝ) (250076260777/500000000000 : ℝ) (100030504309/200000000000 : ℝ) (250076260777/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16485/131072 : ℝ))) 5 (250076260773/500000000000 : ℝ) (250076260777/500000000000 : ℝ) (100030504309/200000000000 : ℝ) (250076260777/500000000000 : ℝ) (100030504309/200000000000 : ℝ) (250076260777/500000000000 : ℝ) (100030504309/200000000000 : ℝ) (250076260777/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16485/131072 : ℝ))) 6 (100030504309/200000000000 : ℝ) (250076260777/500000000000 : ℝ) (100030504309/200000000000 : ℝ) (250076260777/500000000000 : ℝ) (100030504309/200000000000 : ℝ) (250076260777/500000000000 : ℝ) (100030504309/200000000000 : ℝ) (250076260777/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16485/131072 : ℝ))) 7 (100030504309/200000000000 : ℝ) (250076260777/500000000000 : ℝ) (100030504309/200000000000 : ℝ) (250076260777/500000000000 : ℝ) (100030504309/200000000000 : ℝ) (250076260777/500000000000 : ℝ) (100030504309/200000000000 : ℝ) (250076260777/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16485/131072 : ℝ)) hmem 8 (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ) (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16485/131072 : ℝ))) hcmem 8 (100030504309/200000000000 : ℝ) (250076260777/500000000000 : ℝ) (100030504309/200000000000 : ℝ) (250076260777/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16485/131072 : ℝ)) (992185480209/1000000000000 : ℝ) (248046370053/250000000000 : ℝ) (100030504309/200000000000 : ℝ) (250076260777/500000000000 : ℝ) (395912739779/500000000000 : ℝ) (98978184947/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0258_exp_lower
  have heNumeric : (1027454763303/500000000000 : ℝ)/4 ≤ Real.exp (-5328500320983/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027454763303/500000000000 : ℝ)/4 ≤ Real.exp ((4121/32768 : ℝ)-(98978184947/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4121/32768 : ℝ) (16485/131072 : ℝ) (98978184947/125000000000 : ℝ) (1027454763303/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0259; no trusted numerical premise.
theorem cover8_leaf0259_exp_radius : (499018322779635123/500000000000000000 : ℝ) ≤ Real.exp ((-8243/524288 : ℝ)/8) ∧ Real.exp ((-8243/524288 : ℝ)/8) ≤ (998036645559270247/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8243/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0259_exp_lower : (115014235778804219/125000000000000000 : ℝ) ≤ Real.exp ((-21314003768171/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314003768171/32000000000000 : ℝ)/8) ≤ (920113886230433753/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314003768171/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0259_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054909367079/1000000000000 : ℝ) ≤ 4*Real.exp (16485/131072 : ℝ)*Real.exp (-mu (radius 8 (8243/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054909367079/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8243/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0259_exp_radius
  have hrNumeric : (246100168747/250000000000 : ℝ) ≤ Real.exp (-8243/524288 : ℝ) ∧ Real.exp (-8243/524288 : ℝ) ≤ (984400674989/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246100168747/250000000000 : ℝ) ≤ (radius 8 (8243/65536 : ℝ)) ∧ (radius 8 (8243/65536 : ℝ)) ≤ (984400674989/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8243/65536 : ℝ)) (246100168747/250000000000 : ℝ) (984400674989/1000000000000 : ℝ) (35188242969/200000000000 : ℝ) (175941214851/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8243/65536 : ℝ)) (246100168747/250000000000 : ℝ) (984400674989/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8243/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246100168747/250000000000 : ℝ) (984400674989/1000000000000 : ℝ) (496100168747/500000000000 : ℝ) (198440067499/200000000000 : ℝ) (496084840271/500000000000 : ℝ) (31005302517/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8243/65536 : ℝ)) 1 (496100168747/500000000000 : ℝ) (198440067499/200000000000 : ℝ) (496084840271/500000000000 : ℝ) (31005302517/31250000000 : ℝ) (496092504509/500000000000 : ℝ) (49609250451/50000000000 : ℝ) (992185008899/1000000000000 : ℝ) (496092504451/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8243/65536 : ℝ)) 2 (496092504509/500000000000 : ℝ) (49609250451/50000000000 : ℝ) (992185008899/1000000000000 : ℝ) (496092504451/500000000000 : ℝ) (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ) (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8243/65536 : ℝ)) 3 (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ) (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ) (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ) (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8243/65536 : ℝ)) 4 (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ) (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ) (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ) (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8243/65536 : ℝ)) 5 (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ) (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ) (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ) (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8243/65536 : ℝ)) 6 (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ) (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ) (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ) (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8243/65536 : ℝ)) 7 (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ) (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ) (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ) (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8243/65536 : ℝ))) (35188242969/200000000000 : ℝ) (175941214851/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8243/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35188242969/200000000000 : ℝ) (175941214851/1000000000000 : ℝ) (293985303711/500000000000 : ℝ) (293985303713/500000000000 : ℝ) (419453471609/1000000000000 : ℝ) (419453471617/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8243/65536 : ℝ))) 1 (293985303711/500000000000 : ℝ) (293985303713/500000000000 : ℝ) (419453471609/1000000000000 : ℝ) (419453471617/1000000000000 : ℝ) (100742407903/200000000000 : ℝ) (251856019761/500000000000 : ℝ) (124153713317/250000000000 : ℝ) (124153713319/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8243/65536 : ℝ))) 2 (100742407903/200000000000 : ℝ) (251856019761/500000000000 : ℝ) (124153713317/250000000000 : ℝ) (124153713319/250000000000 : ℝ) (500163446391/1000000000000 : ℝ) (500163446399/1000000000000 : ℝ) (250075428917/500000000000 : ℝ) (500150857843/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8243/65536 : ℝ))) 3 (500163446391/1000000000000 : ℝ) (500163446399/1000000000000 : ℝ) (250075428917/500000000000 : ℝ) (500150857843/1000000000000 : ℝ) (31259822007/62500000000 : ℝ) (500157152121/1000000000000 : ℝ) (62519644009/125000000000 : ℝ) (250078576041/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8243/65536 : ℝ))) 4 (31259822007/62500000000 : ℝ) (500157152121/1000000000000 : ℝ) (62519644009/125000000000 : ℝ) (250078576041/500000000000 : ℝ) (125039288023/250000000000 : ℝ) (250078576051/500000000000 : ℝ) (500157152091/1000000000000 : ℝ) (250078576051/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8243/65536 : ℝ))) 5 (125039288023/250000000000 : ℝ) (250078576051/500000000000 : ℝ) (500157152091/1000000000000 : ℝ) (250078576051/500000000000 : ℝ) (500157152091/1000000000000 : ℝ) (250078576051/500000000000 : ℝ) (500157152091/1000000000000 : ℝ) (250078576051/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8243/65536 : ℝ))) 6 (500157152091/1000000000000 : ℝ) (250078576051/500000000000 : ℝ) (500157152091/1000000000000 : ℝ) (250078576051/500000000000 : ℝ) (500157152091/1000000000000 : ℝ) (250078576051/500000000000 : ℝ) (500157152091/1000000000000 : ℝ) (250078576051/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8243/65536 : ℝ))) 7 (500157152091/1000000000000 : ℝ) (250078576051/500000000000 : ℝ) (500157152091/1000000000000 : ℝ) (250078576051/500000000000 : ℝ) (500157152091/1000000000000 : ℝ) (250078576051/500000000000 : ℝ) (500157152091/1000000000000 : ℝ) (250078576051/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8243/65536 : ℝ)) hmem 8 (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ) (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8243/65536 : ℝ))) hcmem 8 (500157152091/1000000000000 : ℝ) (250078576051/500000000000 : ℝ) (500157152091/1000000000000 : ℝ) (250078576051/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8243/65536 : ℝ)) (496092504479/500000000000 : ℝ) (992185008961/1000000000000 : ℝ) (500157152091/1000000000000 : ℝ) (250078576051/500000000000 : ℝ) (395916593291/500000000000 : ℝ) (791833186603/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0259_exp_lower
  have heNumeric : (2054909367079/1000000000000 : ℝ)/4 ≤ Real.exp (-21314003768171/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054909367079/1000000000000 : ℝ)/4 ≤ Real.exp ((16485/131072 : ℝ)-(791833186603/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16485/131072 : ℝ) (8243/65536 : ℝ) (791833186603/1000000000000 : ℝ) (2054909367079/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0260; no trusted numerical premise.
theorem cover8_leaf0260_exp_radius : (499018263292018937/500000000000000000 : ℝ) ≤ Real.exp ((-16487/1048576 : ℝ)/8) ∧ Real.exp ((-16487/1048576 : ℝ)/8) ≤ (7984292212672303/8000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16487/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0260_exp_lower : (184022775467679857/200000000000000000 : ℝ) ≤ Real.exp ((-2131400624217/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131400624217/3200000000000 : ℝ)/8) ≤ (460056938669199643/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131400624217/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0260_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054909208209/1000000000000 : ℝ) ≤ 4*Real.exp (8243/65536 : ℝ)*Real.exp (-mu (radius 8 (16487/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054909208209/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16487/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0260_exp_radius
  have hrNumeric : (984399736191/1000000000000 : ℝ) ≤ Real.exp (-16487/1048576 : ℝ) ∧ Real.exp (-16487/1048576 : ℝ) ≤ (7690622939/7812500000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984399736191/1000000000000 : ℝ) ≤ (radius 8 (16487/131072 : ℝ)) ∧ (radius 8 (16487/131072 : ℝ)) ≤ (7690622939/7812500000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16487/131072 : ℝ)) (984399736191/1000000000000 : ℝ) (7690622939/7812500000 : ℝ) (21993308423/125000000000 : ℝ) (175946467391/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16487/131072 : ℝ)) (984399736191/1000000000000 : ℝ) (7690622939/7812500000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16487/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984399736191/1000000000000 : ℝ) (7690622939/7812500000 : ℝ) (198439973619/200000000000 : ℝ) (15503122939/15625000000 : ℝ) (992169207439/1000000000000 : ℝ) (12402115093/12500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16487/131072 : ℝ)) 1 (198439973619/200000000000 : ℝ) (15503122939/15625000000 : ℝ) (992169207439/1000000000000 : ℝ) (12402115093/12500000000 : ℝ) (992184537767/1000000000000 : ℝ) (124023067221/125000000000 : ℝ) (62011533603/62500000000 : ℝ) (19843690753/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16487/131072 : ℝ)) 2 (992184537767/1000000000000 : ℝ) (124023067221/125000000000 : ℝ) (62011533603/62500000000 : ℝ) (19843690753/20000000000 : ℝ) (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ) (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16487/131072 : ℝ)) 3 (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ) (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ) (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ) (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16487/131072 : ℝ)) 4 (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ) (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ) (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ) (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16487/131072 : ℝ)) 5 (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ) (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ) (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ) (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16487/131072 : ℝ)) 6 (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ) (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ) (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ) (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16487/131072 : ℝ)) 7 (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ) (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ) (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ) (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16487/131072 : ℝ))) (21993308423/125000000000 : ℝ) (175946467391/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16487/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (21993308423/125000000000 : ℝ) (175946467391/1000000000000 : ℝ) (146993308423/250000000000 : ℝ) (18374163553/31250000000 : ℝ) (104864933183/250000000000 : ℝ) (419459732741/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16487/131072 : ℝ))) 1 (146993308423/250000000000 : ℝ) (18374163553/31250000000 : ℝ) (104864933183/250000000000 : ℝ) (419459732741/1000000000000 : ℝ) (125929120803/250000000000 : ℝ) (503716483219/1000000000000 : ℝ) (496619668819/1000000000000 : ℝ) (496619668827/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16487/131072 : ℝ))) 2 (125929120803/250000000000 : ℝ) (503716483219/1000000000000 : ℝ) (496619668819/1000000000000 : ℝ) (496619668827/1000000000000 : ℝ) (100033615203/200000000000 : ℝ) (500168076023/1000000000000 : ℝ) (250077744447/500000000000 : ℝ) (500155488903/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16487/131072 : ℝ))) 3 (100033615203/200000000000 : ℝ) (500168076023/1000000000000 : ℝ) (250077744447/500000000000 : ℝ) (500155488903/1000000000000 : ℝ) (250080891227/500000000000 : ℝ) (500161782463/1000000000000 : ℝ) (250080891207/500000000000 : ℝ) (62520222803/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16487/131072 : ℝ))) 4 (250080891227/500000000000 : ℝ) (500161782463/1000000000000 : ℝ) (250080891207/500000000000 : ℝ) (62520222803/125000000000 : ℝ) (250080891217/500000000000 : ℝ) (125040445611/250000000000 : ℝ) (500161782433/1000000000000 : ℝ) (125040445611/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16487/131072 : ℝ))) 5 (250080891217/500000000000 : ℝ) (125040445611/250000000000 : ℝ) (500161782433/1000000000000 : ℝ) (125040445611/250000000000 : ℝ) (500161782433/1000000000000 : ℝ) (125040445611/250000000000 : ℝ) (500161782433/1000000000000 : ℝ) (125040445611/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16487/131072 : ℝ))) 6 (500161782433/1000000000000 : ℝ) (125040445611/250000000000 : ℝ) (500161782433/1000000000000 : ℝ) (125040445611/250000000000 : ℝ) (500161782433/1000000000000 : ℝ) (125040445611/250000000000 : ℝ) (500161782433/1000000000000 : ℝ) (125040445611/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16487/131072 : ℝ))) 7 (500161782433/1000000000000 : ℝ) (125040445611/250000000000 : ℝ) (500161782433/1000000000000 : ℝ) (125040445611/250000000000 : ℝ) (500161782433/1000000000000 : ℝ) (125040445611/250000000000 : ℝ) (500161782433/1000000000000 : ℝ) (125040445611/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16487/131072 : ℝ)) hmem 8 (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ) (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16487/131072 : ℝ))) hcmem 8 (500161782433/1000000000000 : ℝ) (125040445611/250000000000 : ℝ) (500161782433/1000000000000 : ℝ) (125040445611/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16487/131072 : ℝ)) (992184537707/1000000000000 : ℝ) (992184537709/1000000000000 : ℝ) (500161782433/1000000000000 : ℝ) (125040445611/250000000000 : ℝ) (79184089329/100000000000 : ℝ) (79184089331/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0260_exp_lower
  have heNumeric : (2054909208209/1000000000000 : ℝ)/4 ≤ Real.exp (-2131400624217/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054909208209/1000000000000 : ℝ)/4 ≤ Real.exp ((8243/65536 : ℝ)-(79184089331/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8243/65536 : ℝ) (16487/131072 : ℝ) (79184089331/100000000000 : ℝ) (2054909208209/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0261; no trusted numerical premise.
theorem cover8_leaf0261_exp_radius : (499018203804409843/500000000000000000 : ℝ) ≤ Real.exp ((-2061/131072 : ℝ)/8) ∧ Real.exp ((-2061/131072 : ℝ)/8) ≤ (998036407608819687/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2061/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0261_exp_lower : (184022773696610889/200000000000000000 : ℝ) ≤ Real.exp ((-21314008705961/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314008705961/32000000000000 : ℝ)/8) ≤ (460056934241527223/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314008705961/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0261_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027454524997/500000000000 : ℝ) ≤ 4*Real.exp (16487/131072 : ℝ)*Real.exp (-mu (radius 8 (2061/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027454524997/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2061/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0261_exp_radius
  have hrNumeric : (196879759479/200000000000 : ℝ) ≤ Real.exp (-2061/131072 : ℝ) ∧ Real.exp (-2061/131072 : ℝ) ≤ (246099699349/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196879759479/200000000000 : ℝ) ≤ (radius 8 (2061/16384 : ℝ)) ∧ (radius 8 (2061/16384 : ℝ)) ≤ (246099699349/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2061/16384 : ℝ)) (196879759479/200000000000 : ℝ) (246099699349/250000000000 : ℝ) (43987929939/250000000000 : ℝ) (175951719763/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2061/16384 : ℝ)) (196879759479/200000000000 : ℝ) (246099699349/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2061/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196879759479/200000000000 : ℝ) (246099699349/250000000000 : ℝ) (992199398697/1000000000000 : ℝ) (496099699349/500000000000 : ℝ) (7751318237/7812500000 : ℝ) (496084367169/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2061/16384 : ℝ)) 1 (992199398697/1000000000000 : ℝ) (496099699349/500000000000 : ℝ) (7751318237/7812500000 : ℝ) (496084367169/500000000000 : ℝ) (248046016629/250000000000 : ℝ) (496092033259/500000000000 : ℝ) (496092033199/500000000000 : ℝ) (1240230083/1250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2061/16384 : ℝ)) 2 (248046016629/250000000000 : ℝ) (496092033259/500000000000 : ℝ) (496092033199/500000000000 : ℝ) (1240230083/1250000000 : ℝ) (992184066457/1000000000000 : ℝ) (992184066459/1000000000000 : ℝ) (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2061/16384 : ℝ)) 3 (992184066457/1000000000000 : ℝ) (992184066459/1000000000000 : ℝ) (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ) (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ) (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2061/16384 : ℝ)) 4 (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ) (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ) (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ) (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2061/16384 : ℝ)) 5 (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ) (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ) (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ) (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2061/16384 : ℝ)) 6 (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ) (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ) (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ) (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2061/16384 : ℝ)) 7 (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ) (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ) (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ) (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2061/16384 : ℝ))) (43987929939/250000000000 : ℝ) (175951719763/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2061/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (43987929939/250000000000 : ℝ) (175951719763/1000000000000 : ℝ) (293987929939/500000000000 : ℝ) (293987929941/500000000000 : ℝ) (419465993563/1000000000000 : ℝ) (104866498393/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2061/16384 : ℝ))) 1 (293987929939/500000000000 : ℝ) (293987929941/500000000000 : ℝ) (419465993563/1000000000000 : ℝ) (104866498393/250000000000 : ℝ) (196765987/390625000 : ℝ) (503720926727/1000000000000 : ℝ) (496624484147/1000000000000 : ℝ) (99324896831/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2061/16384 : ℝ))) 2 (196765987/390625000 : ℝ) (503720926727/1000000000000 : ℝ) (496624484147/1000000000000 : ℝ) (99324896831/200000000000 : ℝ) (500172705433/1000000000000 : ℝ) (500172705441/1000000000000 : ℝ) (125040029937/250000000000 : ℝ) (125040029939/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2061/16384 : ℝ))) 3 (500172705433/1000000000000 : ℝ) (500172705441/1000000000000 : ℝ) (125040029937/250000000000 : ℝ) (125040029939/250000000000 : ℝ) (50016641259/100000000000 : ℝ) (500166412599/1000000000000 : ℝ) (10003328251/20000000000 : ℝ) (500166412559/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2061/16384 : ℝ))) 4 (50016641259/100000000000 : ℝ) (500166412599/1000000000000 : ℝ) (10003328251/20000000000 : ℝ) (500166412559/1000000000000 : ℝ) (50016641257/100000000000 : ℝ) (500166412579/1000000000000 : ℝ) (500166412569/1000000000000 : ℝ) (500166412579/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2061/16384 : ℝ))) 5 (50016641257/100000000000 : ℝ) (500166412579/1000000000000 : ℝ) (500166412569/1000000000000 : ℝ) (500166412579/1000000000000 : ℝ) (500166412569/1000000000000 : ℝ) (500166412579/1000000000000 : ℝ) (500166412569/1000000000000 : ℝ) (500166412579/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2061/16384 : ℝ))) 6 (500166412569/1000000000000 : ℝ) (500166412579/1000000000000 : ℝ) (500166412569/1000000000000 : ℝ) (500166412579/1000000000000 : ℝ) (500166412569/1000000000000 : ℝ) (500166412579/1000000000000 : ℝ) (500166412569/1000000000000 : ℝ) (500166412579/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2061/16384 : ℝ))) 7 (500166412569/1000000000000 : ℝ) (500166412579/1000000000000 : ℝ) (500166412569/1000000000000 : ℝ) (500166412579/1000000000000 : ℝ) (500166412569/1000000000000 : ℝ) (500166412579/1000000000000 : ℝ) (500166412569/1000000000000 : ℝ) (500166412579/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2061/16384 : ℝ)) hmem 8 (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ) (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2061/16384 : ℝ))) hcmem 8 (500166412569/1000000000000 : ℝ) (500166412579/1000000000000 : ℝ) (500166412569/1000000000000 : ℝ) (500166412579/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2061/16384 : ℝ)) (124023008307/125000000000 : ℝ) (992184066459/1000000000000 : ℝ) (500166412569/1000000000000 : ℝ) (500166412579/1000000000000 : ℝ) (791848599679/1000000000000 : ℝ) (395924299849/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0261_exp_lower
  have heNumeric : (1027454524997/500000000000 : ℝ)/4 ≤ Real.exp (-21314008705961/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027454524997/500000000000 : ℝ)/4 ≤ Real.exp ((16487/131072 : ℝ)-(395924299849/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16487/131072 : ℝ) (2061/16384 : ℝ) (395924299849/500000000000 : ℝ) (1027454524997/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0262; no trusted numerical premise.
theorem cover8_leaf0262_exp_radius : (998036288633615681/1000000000000000000 : ℝ) ≤ Real.exp ((-16489/1048576 : ℝ)/8) ∧ Real.exp ((-16489/1048576 : ℝ)/8) ≤ (499018144316807841/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16489/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0262_exp_lower : (14376779057238267/15625000000000000 : ℝ) ≤ Real.exp ((-2664251394983/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664251394983/4000000000000 : ℝ)/8) ≤ (920113859663249089/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664251394983/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0262_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027454446207/500000000000 : ℝ) ≤ 4*Real.exp (2061/16384 : ℝ)*Real.exp (-mu (radius 8 (16489/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027454446207/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16489/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0262_exp_radius
  have hrNumeric : (984397858599/1000000000000 : ℝ) ≤ Real.exp (-16489/1048576 : ℝ) ∧ Real.exp (-16489/1048576 : ℝ) ≤ (4921989293/5000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984397858599/1000000000000 : ℝ) ≤ (radius 8 (16489/131072 : ℝ)) ∧ (radius 8 (16489/131072 : ℝ)) ≤ (4921989293/5000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16489/131072 : ℝ)) (984397858599/1000000000000 : ℝ) (4921989293/5000000000 : ℝ) (87978485983/500000000000 : ℝ) (175956971973/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16489/131072 : ℝ)) (984397858599/1000000000000 : ℝ) (4921989293/5000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16489/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984397858599/1000000000000 : ℝ) (4921989293/5000000000 : ℝ) (992198929299/1000000000000 : ℝ) (9921989293/10000000000 : ℝ) (992168261233/1000000000000 : ℝ) (496084130617/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16489/131072 : ℝ)) 1 (992198929299/1000000000000 : ℝ) (9921989293/10000000000 : ℝ) (992168261233/1000000000000 : ℝ) (496084130617/500000000000 : ℝ) (496091797633/500000000000 : ℝ) (992183595267/1000000000000 : ℝ) (992183595147/1000000000000 : ℝ) (992183595149/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16489/131072 : ℝ)) 2 (496091797633/500000000000 : ℝ) (992183595267/1000000000000 : ℝ) (992183595147/1000000000000 : ℝ) (992183595149/1000000000000 : ℝ) (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ) (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16489/131072 : ℝ)) 3 (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ) (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ) (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ) (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16489/131072 : ℝ)) 4 (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ) (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ) (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ) (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16489/131072 : ℝ)) 5 (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ) (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ) (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ) (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16489/131072 : ℝ)) 6 (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ) (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ) (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ) (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16489/131072 : ℝ)) 7 (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ) (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ) (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ) (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16489/131072 : ℝ))) (87978485983/500000000000 : ℝ) (175956971973/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16489/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87978485983/500000000000 : ℝ) (175956971973/1000000000000 : ℝ) (587978485983/1000000000000 : ℝ) (587978485987/1000000000000 : ℝ) (419472254107/1000000000000 : ℝ) (104868063529/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16489/131072 : ℝ))) 1 (587978485983/1000000000000 : ℝ) (587978485987/1000000000000 : ℝ) (419472254107/1000000000000 : ℝ) (104868063529/250000000000 : ℝ) (100745074009/200000000000 : ℝ) (125931342513/250000000000 : ℝ) (248314649629/500000000000 : ℝ) (248314649633/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16489/131072 : ℝ))) 2 (100745074009/200000000000 : ℝ) (125931342513/250000000000 : ℝ) (248314649629/500000000000 : ℝ) (248314649633/500000000000 : ℝ) (500177334651/1000000000000 : ℝ) (500177334659/1000000000000 : ℝ) (500164750401/1000000000000 : ℝ) (500164750409/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16489/131072 : ℝ))) 3 (500177334651/1000000000000 : ℝ) (500177334659/1000000000000 : ℝ) (500164750401/1000000000000 : ℝ) (500164750409/1000000000000 : ℝ) (250085521263/500000000000 : ℝ) (250085521267/500000000000 : ℝ) (250085521243/500000000000 : ℝ) (100034208499/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16489/131072 : ℝ))) 4 (250085521263/500000000000 : ℝ) (250085521267/500000000000 : ℝ) (250085521243/500000000000 : ℝ) (100034208499/200000000000 : ℝ) (250085521253/500000000000 : ℝ) (100034208503/200000000000 : ℝ) (100034208501/200000000000 : ℝ) (100034208503/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16489/131072 : ℝ))) 5 (250085521253/500000000000 : ℝ) (100034208503/200000000000 : ℝ) (100034208501/200000000000 : ℝ) (100034208503/200000000000 : ℝ) (100034208501/200000000000 : ℝ) (100034208503/200000000000 : ℝ) (100034208501/200000000000 : ℝ) (100034208503/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16489/131072 : ℝ))) 6 (100034208501/200000000000 : ℝ) (100034208503/200000000000 : ℝ) (100034208501/200000000000 : ℝ) (100034208503/200000000000 : ℝ) (100034208501/200000000000 : ℝ) (100034208503/200000000000 : ℝ) (100034208501/200000000000 : ℝ) (100034208503/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16489/131072 : ℝ))) 7 (100034208501/200000000000 : ℝ) (100034208503/200000000000 : ℝ) (100034208501/200000000000 : ℝ) (100034208503/200000000000 : ℝ) (100034208501/200000000000 : ℝ) (100034208503/200000000000 : ℝ) (100034208501/200000000000 : ℝ) (100034208503/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16489/131072 : ℝ)) hmem 8 (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ) (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16489/131072 : ℝ))) hcmem 8 (100034208501/200000000000 : ℝ) (100034208503/200000000000 : ℝ) (100034208501/200000000000 : ℝ) (100034208503/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16489/131072 : ℝ)) (496091797603/500000000000 : ℝ) (124022949401/125000000000 : ℝ) (100034208501/200000000000 : ℝ) (100034208503/200000000000 : ℝ) (395928152879/500000000000 : ℝ) (791856305777/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0262_exp_lower
  have heNumeric : (1027454446207/500000000000 : ℝ)/4 ≤ Real.exp (-2664251394983/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027454446207/500000000000 : ℝ)/4 ≤ Real.exp ((2061/16384 : ℝ)-(791856305777/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2061/16384 : ℝ) (16489/131072 : ℝ) (791856305777/1000000000000 : ℝ) (1027454446207/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0263; no trusted numerical premise.
theorem cover8_leaf0263_exp_radius : (499018084829212929/500000000000000000 : ℝ) ≤ Real.exp ((-8245/524288 : ℝ)/8) ∧ Real.exp ((-8245/524288 : ℝ)/8) ≤ (998036169658425859/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8245/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0263_exp_lower : (230028462720292121/250000000000000000 : ℝ) ≤ Real.exp ((-21314013603271/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314013603271/32000000000000 : ℝ)/8) ≤ (184022770176233697/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314013603271/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0263_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054908735509/1000000000000 : ℝ) ≤ 4*Real.exp (16489/131072 : ℝ)*Real.exp (-mu (radius 8 (8245/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054908735509/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8245/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0263_exp_radius
  have hrNumeric : (196879383961/200000000000 : ℝ) ≤ Real.exp (-8245/524288 : ℝ) ∧ Real.exp (-8245/524288 : ℝ) ≤ (492198459903/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196879383961/200000000000 : ℝ) ≤ (radius 8 (8245/65536 : ℝ)) ∧ (radius 8 (8245/65536 : ℝ)) ≤ (492198459903/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8245/65536 : ℝ)) (196879383961/200000000000 : ℝ) (492198459903/500000000000 : ℝ) (43990556001/250000000000 : ℝ) (17596222401/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8245/65536 : ℝ)) (196879383961/200000000000 : ℝ) (492198459903/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8245/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196879383961/200000000000 : ℝ) (492198459903/500000000000 : ℝ) (496099229951/500000000000 : ℝ) (992198459903/1000000000000 : ℝ) (992167788131/1000000000000 : ℝ) (248041947033/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8245/65536 : ℝ)) 1 (496099229951/500000000000 : ℝ) (992198459903/1000000000000 : ℝ) (992167788131/1000000000000 : ℝ) (248041947033/250000000000 : ℝ) (62011445251/62500000000 : ℝ) (496091562009/500000000000 : ℝ) (992183123897/1000000000000 : ℝ) (992183123899/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8245/65536 : ℝ)) 2 (62011445251/62500000000 : ℝ) (496091562009/500000000000 : ℝ) (992183123897/1000000000000 : ℝ) (992183123899/1000000000000 : ℝ) (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ) (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8245/65536 : ℝ)) 3 (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ) (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ) (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ) (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8245/65536 : ℝ)) 4 (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ) (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ) (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ) (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8245/65536 : ℝ)) 5 (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ) (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ) (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ) (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8245/65536 : ℝ)) 6 (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ) (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ) (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ) (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8245/65536 : ℝ)) 7 (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ) (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ) (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ) (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8245/65536 : ℝ))) (43990556001/250000000000 : ℝ) (17596222401/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8245/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (43990556001/250000000000 : ℝ) (17596222401/100000000000 : ℝ) (293990556001/500000000000 : ℝ) (117596222401/200000000000 : ℝ) (419478514353/1000000000000 : ℝ) (419478514361/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8245/65536 : ℝ))) 1 (293990556001/500000000000 : ℝ) (117596222401/200000000000 : ℝ) (419478514353/1000000000000 : ℝ) (419478514361/1000000000000 : ℝ) (503729813177/1000000000000 : ℝ) (503729813183/1000000000000 : ℝ) (248317057071/500000000000 : ℝ) (496634114149/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8245/65536 : ℝ))) 2 (503729813177/1000000000000 : ℝ) (503729813183/1000000000000 : ℝ) (248317057071/500000000000 : ℝ) (496634114149/1000000000000 : ℝ) (500181963659/1000000000000 : ℝ) (250090981833/500000000000 : ℝ) (125042345211/250000000000 : ℝ) (500169380851/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8245/65536 : ℝ))) 3 (500181963659/1000000000000 : ℝ) (250090981833/500000000000 : ℝ) (125042345211/250000000000 : ℝ) (500169380851/1000000000000 : ℝ) (500175672251/1000000000000 : ℝ) (500175672259/1000000000000 : ℝ) (500175672211/1000000000000 : ℝ) (500175672219/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8245/65536 : ℝ))) 4 (500175672251/1000000000000 : ℝ) (500175672259/1000000000000 : ℝ) (500175672211/1000000000000 : ℝ) (500175672219/1000000000000 : ℝ) (500175672231/1000000000000 : ℝ) (500175672239/1000000000000 : ℝ) (50017567223/100000000000 : ℝ) (500175672239/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8245/65536 : ℝ))) 5 (500175672231/1000000000000 : ℝ) (500175672239/1000000000000 : ℝ) (50017567223/100000000000 : ℝ) (500175672239/1000000000000 : ℝ) (50017567223/100000000000 : ℝ) (500175672239/1000000000000 : ℝ) (50017567223/100000000000 : ℝ) (500175672239/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8245/65536 : ℝ))) 6 (50017567223/100000000000 : ℝ) (500175672239/1000000000000 : ℝ) (50017567223/100000000000 : ℝ) (500175672239/1000000000000 : ℝ) (50017567223/100000000000 : ℝ) (500175672239/1000000000000 : ℝ) (50017567223/100000000000 : ℝ) (500175672239/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8245/65536 : ℝ))) 7 (50017567223/100000000000 : ℝ) (500175672239/1000000000000 : ℝ) (50017567223/100000000000 : ℝ) (500175672239/1000000000000 : ℝ) (50017567223/100000000000 : ℝ) (500175672239/1000000000000 : ℝ) (50017567223/100000000000 : ℝ) (500175672239/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8245/65536 : ℝ)) hmem 8 (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ) (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8245/65536 : ℝ))) hcmem 8 (50017567223/100000000000 : ℝ) (500175672239/1000000000000 : ℝ) (50017567223/100000000000 : ℝ) (500175672239/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8245/65536 : ℝ)) (248045780989/250000000000 : ℝ) (992183123959/1000000000000 : ℝ) (50017567223/100000000000 : ℝ) (500175672239/1000000000000 : ℝ) (79186401151/100000000000 : ℝ) (98983001441/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0263_exp_lower
  have heNumeric : (2054908735509/1000000000000 : ℝ)/4 ≤ Real.exp (-21314013603271/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054908735509/1000000000000 : ℝ)/4 ≤ Real.exp ((16489/131072 : ℝ)-(98983001441/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16489/131072 : ℝ) (8245/65536 : ℝ) (98983001441/125000000000 : ℝ) (2054908735509/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0264; no trusted numerical premise.
theorem cover8_leaf0264_exp_radius : (998036050683250219/1000000000000000000 : ℝ) ≤ Real.exp ((-16491/1048576 : ℝ)/8) ∧ Real.exp ((-16491/1048576 : ℝ)/8) ≤ (49901802534162511/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16491/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0264_exp_lower : (230028460533599333/250000000000000000 : ℝ) ≤ Real.exp ((-10657008018427/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657008018427/16000000000000 : ℝ)/8) ≤ (920113842134397333/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657008018427/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0264_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027454289617/500000000000 : ℝ) ≤ 4*Real.exp (8245/65536 : ℝ)*Real.exp (-mu (radius 8 (16491/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027454289617/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16491/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0264_exp_radius
  have hrNumeric : (984395981011/1000000000000 : ℝ) ≤ Real.exp (-16491/1048576 : ℝ) ∧ Real.exp (-16491/1048576 : ℝ) ≤ (246098995253/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984395981011/1000000000000 : ℝ) ≤ (radius 8 (16491/131072 : ℝ)) ∧ (radius 8 (16491/131072 : ℝ)) ≤ (246098995253/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16491/131072 : ℝ)) (984395981011/1000000000000 : ℝ) (246098995253/250000000000 : ℝ) (175967475879/1000000000000 : ℝ) (87983737943/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16491/131072 : ℝ)) (984395981011/1000000000000 : ℝ) (246098995253/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16491/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984395981011/1000000000000 : ℝ) (246098995253/250000000000 : ℝ) (198439598101/200000000000 : ℝ) (496098995253/500000000000 : ℝ) (248041828757/250000000000 : ℝ) (99216731503/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16491/131072 : ℝ)) 1 (198439598101/200000000000 : ℝ) (496098995253/500000000000 : ℝ) (248041828757/250000000000 : ℝ) (99216731503/100000000000 : ℝ) (496091326383/500000000000 : ℝ) (31005707899/31250000000 : ℝ) (992182652647/1000000000000 : ℝ) (19843653053/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16491/131072 : ℝ)) 2 (496091326383/500000000000 : ℝ) (31005707899/31250000000 : ℝ) (992182652647/1000000000000 : ℝ) (19843653053/20000000000 : ℝ) (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ) (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16491/131072 : ℝ)) 3 (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ) (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ) (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ) (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16491/131072 : ℝ)) 4 (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ) (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ) (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ) (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16491/131072 : ℝ)) 5 (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ) (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ) (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ) (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16491/131072 : ℝ)) 6 (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ) (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ) (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ) (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16491/131072 : ℝ)) 7 (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ) (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ) (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ) (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16491/131072 : ℝ))) (175967475879/1000000000000 : ℝ) (87983737943/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16491/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175967475879/1000000000000 : ℝ) (87983737943/500000000000 : ℝ) (587983737939/1000000000000 : ℝ) (587983737943/1000000000000 : ℝ) (419484774311/1000000000000 : ℝ) (5243559679/12500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16491/131072 : ℝ))) 1 (587983737939/1000000000000 : ℝ) (587983737943/1000000000000 : ℝ) (419484774311/1000000000000 : ℝ) (5243559679/12500000000 : ℝ) (4029874049/8000000000 : ℝ) (125933564033/250000000000 : ℝ) (62079866101/125000000000 : ℝ) (31039933051/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16491/131072 : ℝ))) 2 (4029874049/8000000000 : ℝ) (125933564033/250000000000 : ℝ) (62079866101/125000000000 : ℝ) (31039933051/62500000000 : ℝ) (250093296233/500000000000 : ℝ) (250093296237/500000000000 : ℝ) (100034802217/200000000000 : ℝ) (250087005547/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16491/131072 : ℝ))) 3 (250093296233/500000000000 : ℝ) (250093296237/500000000000 : ℝ) (100034802217/200000000000 : ℝ) (250087005547/500000000000 : ℝ) (20007212071/40000000000 : ℝ) (62522537723/125000000000 : ℝ) (100036060347/200000000000 : ℝ) (100036060349/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16491/131072 : ℝ))) 4 (20007212071/40000000000 : ℝ) (62522537723/125000000000 : ℝ) (100036060347/200000000000 : ℝ) (100036060349/200000000000 : ℝ) (100036060351/200000000000 : ℝ) (100036060353/200000000000 : ℝ) (250090150877/500000000000 : ℝ) (100036060353/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16491/131072 : ℝ))) 5 (100036060351/200000000000 : ℝ) (100036060353/200000000000 : ℝ) (250090150877/500000000000 : ℝ) (100036060353/200000000000 : ℝ) (250090150877/500000000000 : ℝ) (100036060353/200000000000 : ℝ) (250090150877/500000000000 : ℝ) (100036060353/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16491/131072 : ℝ))) 6 (250090150877/500000000000 : ℝ) (100036060353/200000000000 : ℝ) (250090150877/500000000000 : ℝ) (100036060353/200000000000 : ℝ) (250090150877/500000000000 : ℝ) (100036060353/200000000000 : ℝ) (250090150877/500000000000 : ℝ) (100036060353/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16491/131072 : ℝ))) 7 (250090150877/500000000000 : ℝ) (100036060353/200000000000 : ℝ) (250090150877/500000000000 : ℝ) (100036060353/200000000000 : ℝ) (250090150877/500000000000 : ℝ) (100036060353/200000000000 : ℝ) (250090150877/500000000000 : ℝ) (100036060353/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16491/131072 : ℝ)) hmem 8 (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ) (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16491/131072 : ℝ))) hcmem 8 (250090150877/500000000000 : ℝ) (100036060353/200000000000 : ℝ) (250090150877/500000000000 : ℝ) (100036060353/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16491/131072 : ℝ)) (496091326353/500000000000 : ℝ) (992182652709/1000000000000 : ℝ) (250090150877/500000000000 : ℝ) (100036060353/200000000000 : ℝ) (791871716951/1000000000000 : ℝ) (197967929243/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0264_exp_lower
  have heNumeric : (1027454289617/500000000000 : ℝ)/4 ≤ Real.exp (-10657008018427/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027454289617/500000000000 : ℝ)/4 ≤ Real.exp ((8245/65536 : ℝ)-(197967929243/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8245/65536 : ℝ) (16491/131072 : ℝ) (197967929243/250000000000 : ℝ) (1027454289617/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0265; no trusted numerical premise.
theorem cover8_leaf0265_exp_radius : (499017965854044381/500000000000000000 : ℝ) ≤ Real.exp ((-4123/262144 : ℝ)/8) ∧ Real.exp ((-4123/262144 : ℝ)/8) ≤ (998035931708088763/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4123/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0265_exp_lower : (92011383342454583/100000000000000000 : ℝ) ≤ Real.exp ((-4262803692033/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262803692033/6400000000000 : ℝ)/8) ≤ (920113833424545831/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262803692033/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0265_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054908423619/1000000000000 : ℝ) ≤ 4*Real.exp (16491/131072 : ℝ)*Real.exp (-mu (radius 8 (4123/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054908423619/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4123/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0265_exp_radius
  have hrNumeric : (492197521109/500000000000 : ℝ) ≤ Real.exp (-4123/262144 : ℝ) ∧ Real.exp (-4123/262144 : ℝ) ≤ (984395042219/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492197521109/500000000000 : ℝ) ≤ (radius 8 (4123/32768 : ℝ)) ∧ (radius 8 (4123/32768 : ℝ)) ≤ (984395042219/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4123/32768 : ℝ)) (492197521109/500000000000 : ℝ) (984395042219/1000000000000 : ℝ) (175972727587/1000000000000 : ℝ) (87986363797/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4123/32768 : ℝ)) (492197521109/500000000000 : ℝ) (984395042219/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4123/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492197521109/500000000000 : ℝ) (984395042219/1000000000000 : ℝ) (992197521109/1000000000000 : ℝ) (99219752111/100000000000 : ℝ) (496083420963/500000000000 : ℝ) (992166841927/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4123/32768 : ℝ)) 1 (992197521109/1000000000000 : ℝ) (99219752111/100000000000 : ℝ) (496083420963/500000000000 : ℝ) (992166841927/1000000000000 : ℝ) (992182181517/1000000000000 : ℝ) (992182181519/1000000000000 : ℝ) (496091090699/500000000000 : ℝ) (4960910907/5000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4123/32768 : ℝ)) 2 (992182181517/1000000000000 : ℝ) (992182181519/1000000000000 : ℝ) (496091090699/500000000000 : ℝ) (4960910907/5000000000 : ℝ) (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ) (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4123/32768 : ℝ)) 3 (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ) (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ) (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ) (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4123/32768 : ℝ)) 4 (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ) (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ) (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ) (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4123/32768 : ℝ)) 5 (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ) (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ) (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ) (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4123/32768 : ℝ)) 6 (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ) (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ) (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ) (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4123/32768 : ℝ)) 7 (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ) (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ) (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ) (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4123/32768 : ℝ))) (175972727587/1000000000000 : ℝ) (87986363797/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4123/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175972727587/1000000000000 : ℝ) (87986363797/500000000000 : ℝ) (587986363793/1000000000000 : ℝ) (587986363797/1000000000000 : ℝ) (52436379247/125000000000 : ℝ) (209745516993/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4123/32768 : ℝ))) 1 (587986363793/1000000000000 : ℝ) (587986363797/1000000000000 : ℝ) (52436379247/125000000000 : ℝ) (209745516993/500000000000 : ℝ) (125934674721/250000000000 : ℝ) (125934674723/250000000000 : ℝ) (496643743251/1000000000000 : ℝ) (24832187163/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4123/32768 : ℝ))) 2 (125934674721/250000000000 : ℝ) (125934674723/250000000000 : ℝ) (496643743251/1000000000000 : ℝ) (24832187163/50000000000 : ℝ) (500191221067/1000000000000 : ℝ) (125047805269/250000000000 : ℝ) (500178641121/1000000000000 : ℝ) (50017864113/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4123/32768 : ℝ))) 3 (500191221067/1000000000000 : ℝ) (125047805269/250000000000 : ℝ) (500178641121/1000000000000 : ℝ) (50017864113/100000000000 : ℝ) (250092465547/500000000000 : ℝ) (500184931103/1000000000000 : ℝ) (250092465527/500000000000 : ℝ) (62523116383/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4123/32768 : ℝ))) 4 (250092465547/500000000000 : ℝ) (500184931103/1000000000000 : ℝ) (250092465527/500000000000 : ℝ) (62523116383/125000000000 : ℝ) (250092465537/500000000000 : ℝ) (125046232771/250000000000 : ℝ) (500184931073/1000000000000 : ℝ) (125046232771/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4123/32768 : ℝ))) 5 (250092465537/500000000000 : ℝ) (125046232771/250000000000 : ℝ) (500184931073/1000000000000 : ℝ) (125046232771/250000000000 : ℝ) (500184931073/1000000000000 : ℝ) (125046232771/250000000000 : ℝ) (500184931073/1000000000000 : ℝ) (125046232771/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4123/32768 : ℝ))) 6 (500184931073/1000000000000 : ℝ) (125046232771/250000000000 : ℝ) (500184931073/1000000000000 : ℝ) (125046232771/250000000000 : ℝ) (500184931073/1000000000000 : ℝ) (125046232771/250000000000 : ℝ) (500184931073/1000000000000 : ℝ) (125046232771/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4123/32768 : ℝ))) 7 (500184931073/1000000000000 : ℝ) (125046232771/250000000000 : ℝ) (500184931073/1000000000000 : ℝ) (125046232771/250000000000 : ℝ) (500184931073/1000000000000 : ℝ) (125046232771/250000000000 : ℝ) (500184931073/1000000000000 : ℝ) (125046232771/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4123/32768 : ℝ)) hmem 8 (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ) (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4123/32768 : ℝ))) hcmem 8 (500184931073/1000000000000 : ℝ) (125046232771/250000000000 : ℝ) (500184931073/1000000000000 : ℝ) (125046232771/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4123/32768 : ℝ)) (992182181457/1000000000000 : ℝ) (49609109073/50000000000 : ℝ) (500184931073/1000000000000 : ℝ) (125046232771/250000000000 : ℝ) (395939711037/500000000000 : ℝ) (158375884419/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0265_exp_lower
  have heNumeric : (2054908423619/1000000000000 : ℝ)/4 ≤ Real.exp (-4262803692033/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054908423619/1000000000000 : ℝ)/4 ≤ Real.exp ((16491/131072 : ℝ)-(158375884419/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16491/131072 : ℝ) (4123/32768 : ℝ) (158375884419/200000000000 : ℝ) (2054908423619/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0266; no trusted numerical premise.
theorem cover8_leaf0266_exp_radius : (62377238295808843/62500000000000000 : ℝ) ≤ Real.exp ((-16493/1048576 : ℝ)/8) ∧ Real.exp ((-16493/1048576 : ℝ)/8) ≤ (998035812732941489/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16493/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0266_exp_lower : (460056912375576961/500000000000000000 : ℝ) ≤ Real.exp ((-5328505218333/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328505218333/8000000000000 : ℝ)/8) ≤ (920113824751153923/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328505218333/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0266_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410981653731/200000000000 : ℝ) ≤ 4*Real.exp (4123/32768 : ℝ)*Real.exp (-mu (radius 8 (16493/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (410981653731/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16493/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0266_exp_radius
  have hrNumeric : (492197051713/500000000000 : ℝ) ≤ Real.exp (-16493/1048576 : ℝ) ∧ Real.exp (-16493/1048576 : ℝ) ≤ (984394103427/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492197051713/500000000000 : ℝ) ≤ (radius 8 (16493/131072 : ℝ)) ∧ (radius 8 (16493/131072 : ℝ)) ≤ (984394103427/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16493/131072 : ℝ)) (492197051713/500000000000 : ℝ) (984394103427/1000000000000 : ℝ) (21997247391/125000000000 : ℝ) (35195595827/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16493/131072 : ℝ)) (492197051713/500000000000 : ℝ) (984394103427/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16493/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492197051713/500000000000 : ℝ) (984394103427/1000000000000 : ℝ) (992197051713/1000000000000 : ℝ) (496098525857/500000000000 : ℝ) (124020796103/125000000000 : ℝ) (39686654753/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16493/131072 : ℝ)) 1 (992197051713/1000000000000 : ℝ) (496098525857/500000000000 : ℝ) (124020796103/125000000000 : ℝ) (39686654753/40000000000 : ℝ) (248045427567/250000000000 : ℝ) (99218171027/100000000000 : ℝ) (992181710149/1000000000000 : ℝ) (992181710151/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16493/131072 : ℝ)) 2 (248045427567/250000000000 : ℝ) (99218171027/100000000000 : ℝ) (992181710149/1000000000000 : ℝ) (992181710151/1000000000000 : ℝ) (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ) (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16493/131072 : ℝ)) 3 (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ) (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ) (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ) (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16493/131072 : ℝ)) 4 (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ) (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ) (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ) (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16493/131072 : ℝ)) 5 (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ) (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ) (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ) (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16493/131072 : ℝ)) 6 (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ) (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ) (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ) (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16493/131072 : ℝ)) 7 (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ) (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ) (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ) (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16493/131072 : ℝ))) (21997247391/125000000000 : ℝ) (35195595827/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16493/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (21997247391/125000000000 : ℝ) (35195595827/200000000000 : ℝ) (146997247391/250000000000 : ℝ) (4593663981/7812500000 : ℝ) (8389945867/20000000000 : ℝ) (419497293359/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16493/131072 : ℝ))) 1 (146997247391/250000000000 : ℝ) (4593663981/7812500000 : ℝ) (8389945867/20000000000 : ℝ) (419497293359/1000000000000 : ℝ) (503743141457/1000000000000 : ℝ) (62967892683/125000000000 : ℝ) (248324278737/500000000000 : ℝ) (248324278741/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16493/131072 : ℝ))) 2 (503743141457/1000000000000 : ℝ) (62967892683/125000000000 : ℝ) (248324278737/500000000000 : ℝ) (248324278741/500000000000 : ℝ) (100039169893/200000000000 : ℝ) (500195849473/1000000000000 : ℝ) (500183270953/1000000000000 : ℝ) (250091635481/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16493/131072 : ℝ))) 3 (100039169893/200000000000 : ℝ) (500195849473/1000000000000 : ℝ) (500183270953/1000000000000 : ℝ) (250091635481/500000000000 : ℝ) (500189560209/1000000000000 : ℝ) (250094780109/500000000000 : ℝ) (500189560169/1000000000000 : ℝ) (250094780089/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16493/131072 : ℝ))) 4 (500189560209/1000000000000 : ℝ) (250094780109/500000000000 : ℝ) (500189560169/1000000000000 : ℝ) (250094780089/500000000000 : ℝ) (500189560189/1000000000000 : ℝ) (250094780099/500000000000 : ℝ) (125047390047/250000000000 : ℝ) (250094780099/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16493/131072 : ℝ))) 5 (500189560189/1000000000000 : ℝ) (250094780099/500000000000 : ℝ) (125047390047/250000000000 : ℝ) (250094780099/500000000000 : ℝ) (125047390047/250000000000 : ℝ) (250094780099/500000000000 : ℝ) (125047390047/250000000000 : ℝ) (250094780099/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16493/131072 : ℝ))) 6 (125047390047/250000000000 : ℝ) (250094780099/500000000000 : ℝ) (125047390047/250000000000 : ℝ) (250094780099/500000000000 : ℝ) (125047390047/250000000000 : ℝ) (250094780099/500000000000 : ℝ) (125047390047/250000000000 : ℝ) (250094780099/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16493/131072 : ℝ))) 7 (125047390047/250000000000 : ℝ) (250094780099/500000000000 : ℝ) (125047390047/250000000000 : ℝ) (250094780099/500000000000 : ℝ) (125047390047/250000000000 : ℝ) (250094780099/500000000000 : ℝ) (125047390047/250000000000 : ℝ) (250094780099/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16493/131072 : ℝ)) hmem 8 (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ) (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16493/131072 : ℝ))) hcmem 8 (125047390047/250000000000 : ℝ) (250094780099/500000000000 : ℝ) (125047390047/250000000000 : ℝ) (250094780099/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16493/131072 : ℝ)) (7751419611/7812500000 : ℝ) (992181710211/1000000000000 : ℝ) (125047390047/250000000000 : ℝ) (250094780099/500000000000 : ℝ) (395943563441/500000000000 : ℝ) (791887126901/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0266_exp_lower
  have heNumeric : (410981653731/200000000000 : ℝ)/4 ≤ Real.exp (-5328505218333/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410981653731/200000000000 : ℝ)/4 ≤ Real.exp ((4123/32768 : ℝ)-(791887126901/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4123/32768 : ℝ) (16493/131072 : ℝ) (791887126901/1000000000000 : ℝ) (410981653731/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0267; no trusted numerical premise.
theorem cover8_leaf0267_exp_radius : (499017846878904199/500000000000000000 : ℝ) ≤ Real.exp ((-8247/524288 : ℝ)/8) ∧ Real.exp ((-8247/524288 : ℝ)/8) ≤ (998035693757808399/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8247/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0267_exp_lower : (920113816115371747/1000000000000000000 : ℝ) ≤ Real.exp ((-4262804655207/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262804655207/6400000000000 : ℝ)/8) ≤ (230028454028842937/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262804655207/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0267_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513727028591/250000000000 : ℝ) ≤ 4*Real.exp (16493/131072 : ℝ)*Real.exp (-mu (radius 8 (8247/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513727028591/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8247/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0267_exp_radius
  have hrNumeric : (246098291159/250000000000 : ℝ) ≤ Real.exp (-8247/524288 : ℝ) ∧ Real.exp (-8247/524288 : ℝ) ≤ (984393164637/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246098291159/250000000000 : ℝ) ≤ (radius 8 (8247/65536 : ℝ)) ∧ (radius 8 (8247/65536 : ℝ)) ≤ (984393164637/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8247/65536 : ℝ)) (246098291159/250000000000 : ℝ) (984393164637/1000000000000 : ℝ) (5499475953/31250000000 : ℝ) (175983230503/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8247/65536 : ℝ)) (246098291159/250000000000 : ℝ) (984393164637/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8247/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246098291159/250000000000 : ℝ) (984393164637/1000000000000 : ℝ) (496098291159/500000000000 : ℝ) (992196582319/1000000000000 : ℝ) (992165895723/1000000000000 : ℝ) (248041473931/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8247/65536 : ℝ)) 1 (496098291159/500000000000 : ℝ) (992196582319/1000000000000 : ℝ) (992165895723/1000000000000 : ℝ) (248041473931/250000000000 : ℝ) (49609061951/50000000000 : ℝ) (496090619511/500000000000 : ℝ) (992181238901/1000000000000 : ℝ) (992181238903/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8247/65536 : ℝ)) 2 (49609061951/50000000000 : ℝ) (496090619511/500000000000 : ℝ) (992181238901/1000000000000 : ℝ) (992181238903/1000000000000 : ℝ) (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ) (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8247/65536 : ℝ)) 3 (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ) (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ) (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ) (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8247/65536 : ℝ)) 4 (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ) (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ) (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ) (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8247/65536 : ℝ)) 5 (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ) (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ) (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ) (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8247/65536 : ℝ)) 6 (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ) (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ) (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ) (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8247/65536 : ℝ)) 7 (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ) (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ) (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ) (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8247/65536 : ℝ))) (5499475953/31250000000 : ℝ) (175983230503/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8247/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5499475953/31250000000 : ℝ) (175983230503/1000000000000 : ℝ) (36749475953/62500000000 : ℝ) (146997903813/250000000000 : ℝ) (419503552423/1000000000000 : ℝ) (26218972027/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8247/65536 : ℝ))) 1 (36749475953/62500000000 : ℝ) (146997903813/250000000000 : ℝ) (419503552423/1000000000000 : ℝ) (26218972027/62500000000 : ℝ) (100749516767/200000000000 : ℝ) (251873791921/500000000000 : ℝ) (124163342867/250000000000 : ℝ) (124163342869/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8247/65536 : ℝ))) 2 (100749516767/200000000000 : ℝ) (251873791921/500000000000 : ℝ) (124163342867/250000000000 : ℝ) (124163342869/250000000000 : ℝ) (500200477651/1000000000000 : ℝ) (500200477659/1000000000000 : ℝ) (500187900573/1000000000000 : ℝ) (250093950291/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8247/65536 : ℝ))) 3 (500200477651/1000000000000 : ℝ) (500200477659/1000000000000 : ℝ) (500187900573/1000000000000 : ℝ) (250093950291/500000000000 : ℝ) (62524273639/125000000000 : ℝ) (500194189121/1000000000000 : ℝ) (31262136817/62500000000 : ℝ) (500194189081/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8247/65536 : ℝ))) 4 (62524273639/125000000000 : ℝ) (500194189121/1000000000000 : ℝ) (31262136817/62500000000 : ℝ) (500194189081/1000000000000 : ℝ) (125048547273/250000000000 : ℝ) (500194189101/1000000000000 : ℝ) (500194189091/1000000000000 : ℝ) (500194189101/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8247/65536 : ℝ))) 5 (125048547273/250000000000 : ℝ) (500194189101/1000000000000 : ℝ) (500194189091/1000000000000 : ℝ) (500194189101/1000000000000 : ℝ) (500194189091/1000000000000 : ℝ) (500194189101/1000000000000 : ℝ) (500194189091/1000000000000 : ℝ) (500194189101/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8247/65536 : ℝ))) 6 (500194189091/1000000000000 : ℝ) (500194189101/1000000000000 : ℝ) (500194189091/1000000000000 : ℝ) (500194189101/1000000000000 : ℝ) (500194189091/1000000000000 : ℝ) (500194189101/1000000000000 : ℝ) (500194189091/1000000000000 : ℝ) (500194189101/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8247/65536 : ℝ))) 7 (500194189091/1000000000000 : ℝ) (500194189101/1000000000000 : ℝ) (500194189091/1000000000000 : ℝ) (500194189101/1000000000000 : ℝ) (500194189091/1000000000000 : ℝ) (500194189101/1000000000000 : ℝ) (500194189091/1000000000000 : ℝ) (500194189101/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8247/65536 : ℝ)) hmem 8 (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ) (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8247/65536 : ℝ))) hcmem 8 (500194189091/1000000000000 : ℝ) (500194189101/1000000000000 : ℝ) (500194189091/1000000000000 : ℝ) (500194189101/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8247/65536 : ℝ)) (12402265487/12500000000 : ℝ) (992181238963/1000000000000 : ℝ) (500194189091/1000000000000 : ℝ) (500194189101/1000000000000 : ℝ) (791894831361/1000000000000 : ℝ) (39594741569/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0267_exp_lower
  have heNumeric : (513727028591/250000000000 : ℝ)/4 ≤ Real.exp (-4262804655207/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513727028591/250000000000 : ℝ)/4 ≤ Real.exp ((16493/131072 : ℝ)-(39594741569/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16493/131072 : ℝ) (8247/65536 : ℝ) (39594741569/50000000000 : ℝ) (513727028591/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0268; no trusted numerical premise.
theorem cover8_leaf0268_exp_radius : (99803557478268949/100000000000000000 : ℝ) ≤ Real.exp ((-16495/1048576 : ℝ)/8) ∧ Real.exp ((-16495/1048576 : ℝ)/8) ≤ (998035574782689491/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16495/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0268_exp_lower : (184022761503002807/200000000000000000 : ℝ) ≤ Real.exp ((-10657012834441/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657012834441/16000000000000 : ℝ)/8) ≤ (230028451878753509/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657012834441/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0268_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410981592141/200000000000 : ℝ) ≤ 4*Real.exp (8247/65536 : ℝ)*Real.exp (-mu (radius 8 (16495/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (410981592141/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16495/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0268_exp_radius
  have hrNumeric : (492196112923/500000000000 : ℝ) ≤ Real.exp (-16495/1048576 : ℝ) ∧ Real.exp (-16495/1048576 : ℝ) ≤ (984392225847/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492196112923/500000000000 : ℝ) ≤ (radius 8 (16495/131072 : ℝ)) ∧ (radius 8 (16495/131072 : ℝ)) ≤ (984392225847/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16495/131072 : ℝ)) (492196112923/500000000000 : ℝ) (984392225847/1000000000000 : ℝ) (87994240851/500000000000 : ℝ) (175988481709/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16495/131072 : ℝ)) (492196112923/500000000000 : ℝ) (984392225847/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16495/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492196112923/500000000000 : ℝ) (984392225847/1000000000000 : ℝ) (992196112923/1000000000000 : ℝ) (248049028231/250000000000 : ℝ) (992165422621/1000000000000 : ℝ) (992165422623/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16495/131072 : ℝ)) 1 (992196112923/1000000000000 : ℝ) (248049028231/250000000000 : ℝ) (992165422621/1000000000000 : ℝ) (992165422623/1000000000000 : ℝ) (248045191943/250000000000 : ℝ) (496090383887/500000000000 : ℝ) (992180767653/1000000000000 : ℝ) (198436153531/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16495/131072 : ℝ)) 2 (248045191943/250000000000 : ℝ) (496090383887/500000000000 : ℝ) (992180767653/1000000000000 : ℝ) (198436153531/200000000000 : ℝ) (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ) (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16495/131072 : ℝ)) 3 (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ) (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ) (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ) (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16495/131072 : ℝ)) 4 (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ) (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ) (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ) (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16495/131072 : ℝ)) 5 (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ) (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ) (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ) (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16495/131072 : ℝ)) 6 (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ) (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ) (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ) (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16495/131072 : ℝ)) 7 (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ) (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ) (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ) (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16495/131072 : ℝ))) (87994240851/500000000000 : ℝ) (175988481709/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16495/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87994240851/500000000000 : ℝ) (175988481709/1000000000000 : ℝ) (587994240851/1000000000000 : ℝ) (117598848171/200000000000 : ℝ) (41950981121/100000000000 : ℝ) (419509811219/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16495/131072 : ℝ))) 1 (587994240851/1000000000000 : ℝ) (117598848171/200000000000 : ℝ) (41950981121/100000000000 : ℝ) (419509811219/1000000000000 : ℝ) (50375202603/100000000000 : ℝ) (503752026037/1000000000000 : ℝ) (248329092623/500000000000 : ℝ) (248329092627/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16495/131072 : ℝ))) 2 (50375202603/100000000000 : ℝ) (503752026037/1000000000000 : ℝ) (248329092623/500000000000 : ℝ) (248329092627/500000000000 : ℝ) (250102552819/500000000000 : ℝ) (250102552823/500000000000 : ℝ) (250096264997/500000000000 : ℝ) (250096265001/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16495/131072 : ℝ))) 3 (250102552819/500000000000 : ℝ) (250102552823/500000000000 : ℝ) (250096264997/500000000000 : ℝ) (250096265001/500000000000 : ℝ) (62524852227/125000000000 : ℝ) (15631213057/31250000000 : ℝ) (31262426111/62500000000 : ℝ) (100039763557/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16495/131072 : ℝ))) 4 (62524852227/125000000000 : ℝ) (15631213057/31250000000 : ℝ) (31262426111/62500000000 : ℝ) (100039763557/200000000000 : ℝ) (125049704449/250000000000 : ℝ) (100039763561/200000000000 : ℝ) (100039763559/200000000000 : ℝ) (100039763561/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16495/131072 : ℝ))) 5 (125049704449/250000000000 : ℝ) (100039763561/200000000000 : ℝ) (100039763559/200000000000 : ℝ) (100039763561/200000000000 : ℝ) (100039763559/200000000000 : ℝ) (100039763561/200000000000 : ℝ) (100039763559/200000000000 : ℝ) (100039763561/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16495/131072 : ℝ))) 6 (100039763559/200000000000 : ℝ) (100039763561/200000000000 : ℝ) (100039763559/200000000000 : ℝ) (100039763561/200000000000 : ℝ) (100039763559/200000000000 : ℝ) (100039763561/200000000000 : ℝ) (100039763559/200000000000 : ℝ) (100039763561/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16495/131072 : ℝ))) 7 (100039763559/200000000000 : ℝ) (100039763561/200000000000 : ℝ) (100039763559/200000000000 : ℝ) (100039763561/200000000000 : ℝ) (100039763559/200000000000 : ℝ) (100039763561/200000000000 : ℝ) (100039763559/200000000000 : ℝ) (100039763561/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16495/131072 : ℝ)) hmem 8 (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ) (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16495/131072 : ℝ))) hcmem 8 (100039763559/200000000000 : ℝ) (100039763561/200000000000 : ℝ) (100039763559/200000000000 : ℝ) (100039763561/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16495/131072 : ℝ)) (31005648991/31250000000 : ℝ) (198436153543/200000000000 : ℝ) (100039763559/200000000000 : ℝ) (100039763561/200000000000 : ℝ) (791902535531/1000000000000 : ℝ) (791902535551/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0268_exp_lower
  have heNumeric : (410981592141/200000000000 : ℝ)/4 ≤ Real.exp (-10657012834441/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410981592141/200000000000 : ℝ)/4 ≤ Real.exp ((8247/65536 : ℝ)-(791902535551/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8247/65536 : ℝ) (16495/131072 : ℝ) (791902535551/1000000000000 : ℝ) (410981592141/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0269; no trusted numerical premise.
theorem cover8_leaf0269_exp_radius : (199607091161516953/200000000000000000 : ℝ) ≤ Real.exp ((-1031/65536 : ℝ)/8) ∧ Real.exp ((-1031/65536 : ℝ)/8) ≤ (499017727903792383/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1031/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0269_exp_lower : (230028449737606457/250000000000000000 : ℝ) ≤ Real.exp ((-21314028051777/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314028051777/32000000000000 : ℝ)/8) ≤ (920113798950425829/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314028051777/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0269_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410981561537/200000000000 : ℝ) ≤ 4*Real.exp (16495/131072 : ℝ)*Real.exp (-mu (radius 8 (1031/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (410981561537/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1031/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0269_exp_radius
  have hrNumeric : (61524455441/62500000000 : ℝ) ≤ Real.exp (-1031/65536 : ℝ) ∧ Real.exp (-1031/65536 : ℝ) ≤ (984391287057/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61524455441/62500000000 : ℝ) ≤ (radius 8 (1031/8192 : ℝ)) ∧ (radius 8 (1031/8192 : ℝ)) ≤ (984391287057/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1031/8192 : ℝ)) (61524455441/62500000000 : ℝ) (984391287057/1000000000000 : ℝ) (175993732747/1000000000000 : ℝ) (175993732753/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1031/8192 : ℝ)) (61524455441/62500000000 : ℝ) (984391287057/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1031/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61524455441/62500000000 : ℝ) (984391287057/1000000000000 : ℝ) (124024455441/125000000000 : ℝ) (992195643529/1000000000000 : ℝ) (992164949519/1000000000000 : ℝ) (992164949521/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1031/8192 : ℝ)) 1 (124024455441/125000000000 : ℝ) (992195643529/1000000000000 : ℝ) (992164949519/1000000000000 : ℝ) (992164949521/1000000000000 : ℝ) (992180296523/1000000000000 : ℝ) (39687211861/40000000000 : ℝ) (248045074101/250000000000 : ℝ) (992180296407/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1031/8192 : ℝ)) 2 (992180296523/1000000000000 : ℝ) (39687211861/40000000000 : ℝ) (248045074101/250000000000 : ℝ) (992180296407/1000000000000 : ℝ) (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ) (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1031/8192 : ℝ)) 3 (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ) (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ) (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ) (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1031/8192 : ℝ)) 4 (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ) (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ) (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ) (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1031/8192 : ℝ)) 5 (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ) (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ) (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ) (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1031/8192 : ℝ)) 6 (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ) (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ) (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ) (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1031/8192 : ℝ)) 7 (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ) (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ) (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ) (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1031/8192 : ℝ))) (175993732747/1000000000000 : ℝ) (175993732753/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1031/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175993732747/1000000000000 : ℝ) (175993732753/1000000000000 : ℝ) (587996866373/1000000000000 : ℝ) (587996866377/1000000000000 : ℝ) (26219754357/62500000000 : ℝ) (10487901743/25000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1031/8192 : ℝ))) 1 (587996866373/1000000000000 : ℝ) (587996866377/1000000000000 : ℝ) (26219754357/62500000000 : ℝ) (10487901743/25000000000 : ℝ) (251878234021/500000000000 : ℝ) (503756468049/1000000000000 : ℝ) (248331499403/500000000000 : ℝ) (248331499407/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1031/8192 : ℝ))) 2 (251878234021/500000000000 : ℝ) (503756468049/1000000000000 : ℝ) (248331499403/500000000000 : ℝ) (248331499407/500000000000 : ℝ) (31263108339/62500000000 : ℝ) (62526216679/125000000000 : ℝ) (500197159213/1000000000000 : ℝ) (250098579611/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1031/8192 : ℝ))) 3 (31263108339/62500000000 : ℝ) (62526216679/125000000000 : ℝ) (500197159213/1000000000000 : ℝ) (250098579611/500000000000 : ℝ) (250101723159/500000000000 : ℝ) (500203446327/1000000000000 : ℝ) (250101723139/500000000000 : ℝ) (31262715393/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1031/8192 : ℝ))) 4 (250101723159/500000000000 : ℝ) (500203446327/1000000000000 : ℝ) (250101723139/500000000000 : ℝ) (31262715393/62500000000 : ℝ) (250101723149/500000000000 : ℝ) (125050861577/250000000000 : ℝ) (500203446297/1000000000000 : ℝ) (125050861577/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1031/8192 : ℝ))) 5 (250101723149/500000000000 : ℝ) (125050861577/250000000000 : ℝ) (500203446297/1000000000000 : ℝ) (125050861577/250000000000 : ℝ) (500203446297/1000000000000 : ℝ) (125050861577/250000000000 : ℝ) (500203446297/1000000000000 : ℝ) (125050861577/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1031/8192 : ℝ))) 6 (500203446297/1000000000000 : ℝ) (125050861577/250000000000 : ℝ) (500203446297/1000000000000 : ℝ) (125050861577/250000000000 : ℝ) (500203446297/1000000000000 : ℝ) (125050861577/250000000000 : ℝ) (500203446297/1000000000000 : ℝ) (125050861577/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1031/8192 : ℝ))) 7 (500203446297/1000000000000 : ℝ) (125050861577/250000000000 : ℝ) (500203446297/1000000000000 : ℝ) (125050861577/250000000000 : ℝ) (500203446297/1000000000000 : ℝ) (125050861577/250000000000 : ℝ) (500203446297/1000000000000 : ℝ) (125050861577/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1031/8192 : ℝ)) hmem 8 (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ) (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1031/8192 : ℝ))) hcmem 8 (500203446297/1000000000000 : ℝ) (125050861577/250000000000 : ℝ) (500203446297/1000000000000 : ℝ) (125050861577/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1031/8192 : ℝ)) (992180296463/1000000000000 : ℝ) (496090148233/500000000000 : ℝ) (500203446297/1000000000000 : ℝ) (125050861577/250000000000 : ℝ) (791910239391/1000000000000 : ℝ) (791910239411/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0269_exp_lower
  have heNumeric : (410981561537/200000000000 : ℝ)/4 ≤ Real.exp (-21314028051777/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410981561537/200000000000 : ℝ)/4 ≤ Real.exp ((16495/131072 : ℝ)-(791910239411/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16495/131072 : ℝ) (1031/8192 : ℝ) (791910239411/1000000000000 : ℝ) (410981561537/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0270; no trusted numerical premise.
theorem cover8_leaf0270_exp_radius : (998035336832494223/1000000000000000000 : ℝ) ≤ Real.exp ((-16497/1048576 : ℝ)/8) ∧ Real.exp ((-16497/1048576 : ℝ)/8) ≤ (62377208552030889/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16497/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0270_exp_lower : (920113790423447351/1000000000000000000 : ℝ) ≤ Real.exp ((-1332126901513/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332126901513/2000000000000 : ℝ)/8) ≤ (115014223802930919/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332126901513/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0270_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453827669/500000000000 : ℝ) ≤ 4*Real.exp (1031/8192 : ℝ)*Real.exp (-mu (radius 8 (16497/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453827669/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16497/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0270_exp_radius
  have hrNumeric : (246097587067/250000000000 : ℝ) ≤ Real.exp (-16497/1048576 : ℝ) ∧ Real.exp (-16497/1048576 : ℝ) ≤ (984390348269/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246097587067/250000000000 : ℝ) ≤ (radius 8 (16497/131072 : ℝ)) ∧ (radius 8 (16497/131072 : ℝ)) ≤ (984390348269/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16497/131072 : ℝ)) (246097587067/250000000000 : ℝ) (984390348269/1000000000000 : ℝ) (87999491809/500000000000 : ℝ) (1407991869/8000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16497/131072 : ℝ)) (246097587067/250000000000 : ℝ) (984390348269/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16497/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246097587067/250000000000 : ℝ) (984390348269/1000000000000 : ℝ) (496097587067/500000000000 : ℝ) (198439034827/200000000000 : ℝ) (992164476419/1000000000000 : ℝ) (49608223821/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16497/131072 : ℝ)) 1 (496097587067/500000000000 : ℝ) (198439034827/200000000000 : ℝ) (992164476419/1000000000000 : ℝ) (49608223821/50000000000 : ℝ) (248044956319/250000000000 : ℝ) (496089912639/500000000000 : ℝ) (992179825157/1000000000000 : ℝ) (992179825159/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16497/131072 : ℝ)) 2 (248044956319/250000000000 : ℝ) (496089912639/500000000000 : ℝ) (992179825157/1000000000000 : ℝ) (992179825159/1000000000000 : ℝ) (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ) (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16497/131072 : ℝ)) 3 (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ) (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ) (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ) (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16497/131072 : ℝ)) 4 (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ) (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ) (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ) (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16497/131072 : ℝ)) 5 (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ) (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ) (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ) (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16497/131072 : ℝ)) 6 (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ) (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ) (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ) (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16497/131072 : ℝ)) 7 (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ) (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ) (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ) (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16497/131072 : ℝ))) (87999491809/500000000000 : ℝ) (1407991869/8000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16497/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87999491809/500000000000 : ℝ) (1407991869/8000000000 : ℝ) (587999491809/1000000000000 : ℝ) (587999491813/1000000000000 : ℝ) (419522327913/1000000000000 : ℝ) (209761163961/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16497/131072 : ℝ))) 1 (587999491809/1000000000000 : ℝ) (587999491813/1000000000000 : ℝ) (419522327913/1000000000000 : ℝ) (209761163961/500000000000 : ℝ) (503760909861/1000000000000 : ℝ) (125940227467/250000000000 : ℝ) (496667812139/1000000000000 : ℝ) (496667812147/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16497/131072 : ℝ))) 2 (503760909861/1000000000000 : ℝ) (125940227467/250000000000 : ℝ) (496667812139/1000000000000 : ℝ) (496667812147/1000000000000 : ℝ) (500214361/1000000000 : ℝ) (31263397563/62500000000 : ℝ) (500201788223/1000000000000 : ℝ) (500201788231/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16497/131072 : ℝ))) 3 (500214361/1000000000 : ℝ) (31263397563/62500000000 : ℝ) (500201788223/1000000000000 : ℝ) (500201788231/1000000000000 : ℝ) (500208074611/1000000000000 : ℝ) (25010403731/50000000000 : ℝ) (500208074571/1000000000000 : ℝ) (25010403729/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16497/131072 : ℝ))) 4 (500208074611/1000000000000 : ℝ) (25010403731/50000000000 : ℝ) (500208074571/1000000000000 : ℝ) (25010403729/50000000000 : ℝ) (500208074591/1000000000000 : ℝ) (2501040373/5000000000 : ℝ) (50020807459/100000000000 : ℝ) (2501040373/5000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16497/131072 : ℝ))) 5 (500208074591/1000000000000 : ℝ) (2501040373/5000000000 : ℝ) (50020807459/100000000000 : ℝ) (2501040373/5000000000 : ℝ) (50020807459/100000000000 : ℝ) (2501040373/5000000000 : ℝ) (50020807459/100000000000 : ℝ) (2501040373/5000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16497/131072 : ℝ))) 6 (50020807459/100000000000 : ℝ) (2501040373/5000000000 : ℝ) (50020807459/100000000000 : ℝ) (2501040373/5000000000 : ℝ) (50020807459/100000000000 : ℝ) (2501040373/5000000000 : ℝ) (50020807459/100000000000 : ℝ) (2501040373/5000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16497/131072 : ℝ))) 7 (50020807459/100000000000 : ℝ) (2501040373/5000000000 : ℝ) (50020807459/100000000000 : ℝ) (2501040373/5000000000 : ℝ) (50020807459/100000000000 : ℝ) (2501040373/5000000000 : ℝ) (50020807459/100000000000 : ℝ) (2501040373/5000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16497/131072 : ℝ)) hmem 8 (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ) (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16497/131072 : ℝ))) hcmem 8 (50020807459/100000000000 : ℝ) (2501040373/5000000000 : ℝ) (50020807459/100000000000 : ℝ) (2501040373/5000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16497/131072 : ℝ)) (15502809769/15625000000 : ℝ) (992179825219/1000000000000 : ℝ) (50020807459/100000000000 : ℝ) (2501040373/5000000000 : ℝ) (31676717717/40000000000 : ℝ) (24747435717/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0270_exp_lower
  have heNumeric : (1027453827669/500000000000 : ℝ)/4 ≤ Real.exp (-1332126901513/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453827669/500000000000 : ℝ)/4 ≤ Real.exp ((1031/8192 : ℝ)-(24747435717/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1031/8192 : ℝ) (16497/131072 : ℝ) (24747435717/31250000000 : ℝ) (1027453827669/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0271; no trusted numerical premise.
theorem cover8_leaf0271_exp_radius : (199607043571483573/200000000000000000 : ℝ) ≤ Real.exp ((-8249/524288 : ℝ)/8) ∧ Real.exp ((-8249/524288 : ℝ)/8) ≤ (499017608928708933/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8249/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0271_exp_lower : (460056890966464231/500000000000000000 : ℝ) ≤ Real.exp ((-4262806557299/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262806557299/6400000000000 : ℝ)/8) ≤ (920113781932928463/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262806557299/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0271_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907503641/1000000000000 : ℝ) ≤ 4*Real.exp (16497/131072 : ℝ)*Real.exp (-mu (radius 8 (8249/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907503641/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8249/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0271_exp_radius
  have hrNumeric : (984389409481/1000000000000 : ℝ) ≤ Real.exp (-8249/524288 : ℝ) ∧ Real.exp (-8249/524288 : ℝ) ≤ (492194704741/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984389409481/1000000000000 : ℝ) ≤ (radius 8 (8249/65536 : ℝ)) ∧ (radius 8 (8249/65536 : ℝ)) ≤ (492194704741/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8249/65536 : ℝ)) (984389409481/1000000000000 : ℝ) (492194704741/500000000000 : ℝ) (176004234323/1000000000000 : ℝ) (176004234329/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8249/65536 : ℝ)) (984389409481/1000000000000 : ℝ) (492194704741/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8249/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984389409481/1000000000000 : ℝ) (492194704741/500000000000 : ℝ) (49609735237/50000000000 : ℝ) (992194704741/1000000000000 : ℝ) (496082001659/500000000000 : ℝ) (24804100083/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8249/65536 : ℝ)) 1 (49609735237/50000000000 : ℝ) (992194704741/1000000000000 : ℝ) (496082001659/500000000000 : ℝ) (24804100083/25000000000 : ℝ) (992179354029/1000000000000 : ℝ) (992179354031/1000000000000 : ℝ) (99217935391/100000000000 : ℝ) (124022419239/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8249/65536 : ℝ)) 2 (992179354029/1000000000000 : ℝ) (992179354031/1000000000000 : ℝ) (99217935391/100000000000 : ℝ) (124022419239/125000000000 : ℝ) (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ) (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8249/65536 : ℝ)) 3 (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ) (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ) (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ) (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8249/65536 : ℝ)) 4 (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ) (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ) (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ) (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8249/65536 : ℝ)) 5 (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ) (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ) (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ) (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8249/65536 : ℝ)) 6 (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ) (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ) (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ) (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8249/65536 : ℝ)) 7 (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ) (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ) (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ) (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8249/65536 : ℝ))) (176004234323/1000000000000 : ℝ) (176004234329/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8249/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176004234323/1000000000000 : ℝ) (176004234329/1000000000000 : ℝ) (588002117161/1000000000000 : ℝ) (117600423433/200000000000 : ℝ) (419528585823/1000000000000 : ℝ) (419528585831/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8249/65536 : ℝ))) 1 (588002117161/1000000000000 : ℝ) (117600423433/200000000000 : ℝ) (419528585823/1000000000000 : ℝ) (419528585831/1000000000000 : ℝ) (125941337873/250000000000 : ℝ) (251882675749/500000000000 : ℝ) (1986690501/4000000000 : ℝ) (248336312629/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8249/65536 : ℝ))) 2 (125941337873/250000000000 : ℝ) (251882675749/500000000000 : ℝ) (1986690501/4000000000 : ℝ) (248336312629/500000000000 : ℝ) (500218988371/1000000000000 : ℝ) (250109494189/500000000000 : ℝ) (500206417027/1000000000000 : ℝ) (100041283407/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8249/65536 : ℝ))) 3 (500218988371/1000000000000 : ℝ) (250109494189/500000000000 : ℝ) (500206417027/1000000000000 : ℝ) (100041283407/200000000000 : ℝ) (500212702699/1000000000000 : ℝ) (500212702707/1000000000000 : ℝ) (500212702659/1000000000000 : ℝ) (125053175667/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8249/65536 : ℝ))) 4 (500212702699/1000000000000 : ℝ) (500212702707/1000000000000 : ℝ) (500212702659/1000000000000 : ℝ) (125053175667/250000000000 : ℝ) (500212702679/1000000000000 : ℝ) (15631646959/31250000000 : ℝ) (250106351339/500000000000 : ℝ) (15631646959/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8249/65536 : ℝ))) 5 (500212702679/1000000000000 : ℝ) (15631646959/31250000000 : ℝ) (250106351339/500000000000 : ℝ) (15631646959/31250000000 : ℝ) (250106351339/500000000000 : ℝ) (15631646959/31250000000 : ℝ) (250106351339/500000000000 : ℝ) (15631646959/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8249/65536 : ℝ))) 6 (250106351339/500000000000 : ℝ) (15631646959/31250000000 : ℝ) (250106351339/500000000000 : ℝ) (15631646959/31250000000 : ℝ) (250106351339/500000000000 : ℝ) (15631646959/31250000000 : ℝ) (250106351339/500000000000 : ℝ) (15631646959/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8249/65536 : ℝ))) 7 (250106351339/500000000000 : ℝ) (15631646959/31250000000 : ℝ) (250106351339/500000000000 : ℝ) (15631646959/31250000000 : ℝ) (250106351339/500000000000 : ℝ) (15631646959/31250000000 : ℝ) (250106351339/500000000000 : ℝ) (15631646959/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8249/65536 : ℝ)) hmem 8 (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ) (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8249/65536 : ℝ))) hcmem 8 (250106351339/500000000000 : ℝ) (15631646959/31250000000 : ℝ) (250106351339/500000000000 : ℝ) (15631646959/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8249/65536 : ℝ)) (992179353969/1000000000000 : ℝ) (248044838493/250000000000 : ℝ) (250106351339/500000000000 : ℝ) (15631646959/31250000000 : ℝ) (791925646141/1000000000000 : ℝ) (9899070577/12500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0271_exp_lower
  have heNumeric : (2054907503641/1000000000000 : ℝ)/4 ≤ Real.exp (-4262806557299/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907503641/1000000000000 : ℝ)/4 ≤ Real.exp ((16497/131072 : ℝ)-(9899070577/12500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16497/131072 : ℝ) (8249/65536 : ℝ) (9899070577/12500000000 : ℝ) (2054907503641/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0272; no trusted numerical premise.
theorem cover8_leaf0272_exp_radius : (998035098882355689/1000000000000000000 : ℝ) ≤ Real.exp ((-16499/1048576 : ℝ)/8) ∧ Real.exp ((-16499/1048576 : ℝ)/8) ≤ (99803509888235569/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16499/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0272_exp_lower : (46005688673903203/50000000000000000 : ℝ) ≤ Real.exp ((-10657017569431/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657017569431/16000000000000 : ℝ)/8) ≤ (920113773478064061/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657017569431/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0272_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453676291/500000000000 : ℝ) ≤ 4*Real.exp (8249/65536 : ℝ)*Real.exp (-mu (radius 8 (16499/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453676291/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16499/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0272_exp_radius
  have hrNumeric : (492194235347/500000000000 : ℝ) ≤ Real.exp (-16499/1048576 : ℝ) ∧ Real.exp (-16499/1048576 : ℝ) ≤ (196877694139/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492194235347/500000000000 : ℝ) ≤ (radius 8 (16499/131072 : ℝ)) ∧ (radius 8 (16499/131072 : ℝ)) ≤ (196877694139/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16499/131072 : ℝ)) (492194235347/500000000000 : ℝ) (196877694139/200000000000 : ℝ) (35201896973/200000000000 : ℝ) (22001185609/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16499/131072 : ℝ)) (492194235347/500000000000 : ℝ) (196877694139/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16499/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492194235347/500000000000 : ℝ) (196877694139/200000000000 : ℝ) (992194235347/1000000000000 : ℝ) (248048558837/250000000000 : ℝ) (992163530217/1000000000000 : ℝ) (992163530219/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16499/131072 : ℝ)) 1 (992194235347/1000000000000 : ℝ) (248048558837/250000000000 : ℝ) (992163530217/1000000000000 : ℝ) (992163530219/1000000000000 : ℝ) (496089441391/500000000000 : ℝ) (31005590087/31250000000 : ℝ) (992178882663/1000000000000 : ℝ) (198435776533/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16499/131072 : ℝ)) 2 (496089441391/500000000000 : ℝ) (31005590087/31250000000 : ℝ) (992178882663/1000000000000 : ℝ) (198435776533/200000000000 : ℝ) (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ) (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16499/131072 : ℝ)) 3 (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ) (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ) (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ) (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16499/131072 : ℝ)) 4 (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ) (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ) (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ) (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16499/131072 : ℝ)) 5 (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ) (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ) (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ) (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16499/131072 : ℝ)) 6 (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ) (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ) (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ) (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16499/131072 : ℝ)) 7 (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ) (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ) (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ) (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16499/131072 : ℝ))) (35201896973/200000000000 : ℝ) (22001185609/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16499/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35201896973/200000000000 : ℝ) (22001185609/125000000000 : ℝ) (18375148201/31250000000 : ℝ) (147001185609/250000000000 : ℝ) (83906968689/200000000000 : ℝ) (83906968691/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16499/131072 : ℝ))) 1 (18375148201/31250000000 : ℝ) (147001185609/250000000000 : ℝ) (83906968689/200000000000 : ℝ) (83906968691/200000000000 : ℝ) (251884896469/500000000000 : ℝ) (251884896473/500000000000 : ℝ) (496677438143/1000000000000 : ℝ) (62084679769/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16499/131072 : ℝ))) 2 (251884896469/500000000000 : ℝ) (251884896473/500000000000 : ℝ) (496677438143/1000000000000 : ℝ) (62084679769/125000000000 : ℝ) (25011180777/50000000000 : ℝ) (500223615549/1000000000000 : ℝ) (50021104563/100000000000 : ℝ) (500211045639/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16499/131072 : ℝ))) 3 (25011180777/50000000000 : ℝ) (500223615549/1000000000000 : ℝ) (50021104563/100000000000 : ℝ) (500211045639/1000000000000 : ℝ) (100043466117/200000000000 : ℝ) (250108665297/500000000000 : ℝ) (100043466109/200000000000 : ℝ) (100043466111/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16499/131072 : ℝ))) 4 (100043466117/200000000000 : ℝ) (250108665297/500000000000 : ℝ) (100043466109/200000000000 : ℝ) (100043466111/200000000000 : ℝ) (100043466113/200000000000 : ℝ) (20008693223/40000000000 : ℝ) (125054332641/250000000000 : ℝ) (20008693223/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16499/131072 : ℝ))) 5 (100043466113/200000000000 : ℝ) (20008693223/40000000000 : ℝ) (125054332641/250000000000 : ℝ) (20008693223/40000000000 : ℝ) (125054332641/250000000000 : ℝ) (20008693223/40000000000 : ℝ) (125054332641/250000000000 : ℝ) (20008693223/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16499/131072 : ℝ))) 6 (125054332641/250000000000 : ℝ) (20008693223/40000000000 : ℝ) (125054332641/250000000000 : ℝ) (20008693223/40000000000 : ℝ) (125054332641/250000000000 : ℝ) (20008693223/40000000000 : ℝ) (125054332641/250000000000 : ℝ) (20008693223/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16499/131072 : ℝ))) 7 (125054332641/250000000000 : ℝ) (20008693223/40000000000 : ℝ) (125054332641/250000000000 : ℝ) (20008693223/40000000000 : ℝ) (125054332641/250000000000 : ℝ) (20008693223/40000000000 : ℝ) (125054332641/250000000000 : ℝ) (20008693223/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16499/131072 : ℝ)) hmem 8 (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ) (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16499/131072 : ℝ))) hcmem 8 (125054332641/250000000000 : ℝ) (20008693223/40000000000 : ℝ) (125054332641/250000000000 : ℝ) (20008693223/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16499/131072 : ℝ)) (496089441361/500000000000 : ℝ) (39687155309/40000000000 : ℝ) (125054332641/250000000000 : ℝ) (20008693223/40000000000 : ℝ) (158386669809/200000000000 : ℝ) (395966674533/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0272_exp_lower
  have heNumeric : (1027453676291/500000000000 : ℝ)/4 ≤ Real.exp (-10657017569431/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453676291/500000000000 : ℝ)/4 ≤ Real.exp ((8249/65536 : ℝ)-(395966674533/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8249/65536 : ℝ) (16499/131072 : ℝ) (395966674533/500000000000 : ℝ) (1027453676291/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0273; no trusted numerical premise.
theorem cover8_leaf0273_exp_radius : (62377186244206731/62500000000000000 : ℝ) ≤ Real.exp ((-4125/262144 : ℝ)/8) ∧ Real.exp ((-4125/262144 : ℝ)/8) ≤ (998034979907307697/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4125/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0273_exp_lower : (920113765060579357/1000000000000000000 : ℝ) ≤ Real.exp ((-21314037480829/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314037480829/32000000000000 : ℝ)/8) ≤ (460056882530289679/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314037480829/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0273_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907202191/1000000000000 : ℝ) ≤ 4*Real.exp (16499/131072 : ℝ)*Real.exp (-mu (radius 8 (4125/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907202191/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4125/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0273_exp_radius
  have hrNumeric : (984387531909/1000000000000 : ℝ) ≤ Real.exp (-4125/262144 : ℝ) ∧ Real.exp (-4125/262144 : ℝ) ≤ (98438753191/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984387531909/1000000000000 : ℝ) ≤ (radius 8 (4125/32768 : ℝ)) ∧ (radius 8 (4125/32768 : ℝ)) ≤ (98438753191/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4125/32768 : ℝ)) (984387531909/1000000000000 : ℝ) (98438753191/100000000000 : ℝ) (35202947047/200000000000 : ℝ) (88007367621/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4125/32768 : ℝ)) (984387531909/1000000000000 : ℝ) (98438753191/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4125/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984387531909/1000000000000 : ℝ) (98438753191/100000000000 : ℝ) (496096882977/500000000000 : ℝ) (198438753191/200000000000 : ℝ) (992163057117/1000000000000 : ℝ) (992163057119/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4125/32768 : ℝ)) 1 (496096882977/500000000000 : ℝ) (198438753191/200000000000 : ℝ) (992163057117/1000000000000 : ℝ) (992163057119/1000000000000 : ℝ) (198435682307/200000000000 : ℝ) (992178411537/1000000000000 : ℝ) (124022301427/125000000000 : ℝ) (992178411419/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4125/32768 : ℝ)) 2 (198435682307/200000000000 : ℝ) (992178411537/1000000000000 : ℝ) (124022301427/125000000000 : ℝ) (992178411419/1000000000000 : ℝ) (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ) (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4125/32768 : ℝ)) 3 (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ) (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ) (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ) (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4125/32768 : ℝ)) 4 (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ) (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ) (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ) (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4125/32768 : ℝ)) 5 (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ) (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ) (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ) (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4125/32768 : ℝ)) 6 (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ) (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ) (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ) (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4125/32768 : ℝ)) 7 (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ) (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ) (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ) (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4125/32768 : ℝ))) (35202947047/200000000000 : ℝ) (88007367621/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4125/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35202947047/200000000000 : ℝ) (88007367621/500000000000 : ℝ) (588007367617/1000000000000 : ℝ) (588007367621/1000000000000 : ℝ) (419541100769/1000000000000 : ℝ) (209770550389/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4125/32768 : ℝ))) 1 (588007367617/1000000000000 : ℝ) (588007367621/1000000000000 : ℝ) (419541100769/1000000000000 : ℝ) (209770550389/500000000000 : ℝ) (503774234193/1000000000000 : ℝ) (2518871171/5000000000 : ℝ) (49668225081/100000000000 : ℝ) (248341125409/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4125/32768 : ℝ))) 2 (503774234193/1000000000000 : ℝ) (2518871171/5000000000 : ℝ) (49668225081/100000000000 : ℝ) (248341125409/500000000000 : ℝ) (500228242501/1000000000000 : ℝ) (500228242509/1000000000000 : ℝ) (500215674023/1000000000000 : ℝ) (31263479627/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4125/32768 : ℝ))) 3 (500228242501/1000000000000 : ℝ) (500228242509/1000000000000 : ℝ) (500215674023/1000000000000 : ℝ) (31263479627/62500000000 : ℝ) (250110979131/500000000000 : ℝ) (500221958271/1000000000000 : ℝ) (250110979111/500000000000 : ℝ) (62527744779/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4125/32768 : ℝ))) 4 (250110979131/500000000000 : ℝ) (500221958271/1000000000000 : ℝ) (250110979111/500000000000 : ℝ) (62527744779/125000000000 : ℝ) (250110979121/500000000000 : ℝ) (125055489563/250000000000 : ℝ) (500221958241/1000000000000 : ℝ) (125055489563/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4125/32768 : ℝ))) 5 (250110979121/500000000000 : ℝ) (125055489563/250000000000 : ℝ) (500221958241/1000000000000 : ℝ) (125055489563/250000000000 : ℝ) (500221958241/1000000000000 : ℝ) (125055489563/250000000000 : ℝ) (500221958241/1000000000000 : ℝ) (125055489563/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4125/32768 : ℝ))) 6 (500221958241/1000000000000 : ℝ) (125055489563/250000000000 : ℝ) (500221958241/1000000000000 : ℝ) (125055489563/250000000000 : ℝ) (500221958241/1000000000000 : ℝ) (125055489563/250000000000 : ℝ) (500221958241/1000000000000 : ℝ) (125055489563/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4125/32768 : ℝ))) 7 (500221958241/1000000000000 : ℝ) (125055489563/250000000000 : ℝ) (500221958241/1000000000000 : ℝ) (125055489563/250000000000 : ℝ) (500221958241/1000000000000 : ℝ) (125055489563/250000000000 : ℝ) (500221958241/1000000000000 : ℝ) (125055489563/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4125/32768 : ℝ)) hmem 8 (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ) (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4125/32768 : ℝ))) hcmem 8 (500221958241/1000000000000 : ℝ) (125055489563/250000000000 : ℝ) (500221958241/1000000000000 : ℝ) (125055489563/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4125/32768 : ℝ)) (39687136459/40000000000 : ℝ) (496089205739/500000000000 : ℝ) (500221958241/1000000000000 : ℝ) (125055489563/250000000000 : ℝ) (395970525813/500000000000 : ℝ) (791941051647/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0273_exp_lower
  have heNumeric : (2054907202191/1000000000000 : ℝ)/4 ≤ Real.exp (-21314037480829/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907202191/1000000000000 : ℝ)/4 ≤ Real.exp ((16499/131072 : ℝ)-(791941051647/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16499/131072 : ℝ) (4125/32768 : ℝ) (791941051647/1000000000000 : ℝ) (2054907202191/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0274; no trusted numerical premise.
theorem cover8_leaf0274_exp_radius : (199606972186454777/200000000000000000 : ℝ) ≤ Real.exp ((-16501/1048576 : ℝ)/8) ∧ Real.exp ((-16501/1048576 : ℝ)/8) ≤ (499017430466136943/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16501/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0274_exp_lower : (460056878339432077/500000000000000000 : ℝ) ≤ Real.exp ((-5328509953211/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328509953211/8000000000000 : ℝ)/8) ≤ (184022751335772831/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328509953211/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0274_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453526219/500000000000 : ℝ) ≤ 4*Real.exp (4125/32768 : ℝ)*Real.exp (-mu (radius 8 (16501/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453526219/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16501/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0274_exp_radius
  have hrNumeric : (246096648281/250000000000 : ℝ) ≤ Real.exp (-16501/1048576 : ℝ) ∧ Real.exp (-16501/1048576 : ℝ) ≤ (1575018549/1600000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246096648281/250000000000 : ℝ) ≤ (radius 8 (16501/131072 : ℝ)) ∧ (radius 8 (16501/131072 : ℝ)) ≤ (1575018549/1600000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16501/131072 : ℝ)) (246096648281/250000000000 : ℝ) (1575018549/1600000000 : ℝ) (44004996361/250000000000 : ℝ) (3520399709/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16501/131072 : ℝ)) (246096648281/250000000000 : ℝ) (1575018549/1600000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16501/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246096648281/250000000000 : ℝ) (1575018549/1600000000 : ℝ) (496096648281/500000000000 : ℝ) (992193296563/1000000000000 : ℝ) (992162584017/1000000000000 : ℝ) (496081292009/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16501/131072 : ℝ)) 1 (496096648281/500000000000 : ℝ) (992193296563/1000000000000 : ℝ) (992162584017/1000000000000 : ℝ) (496081292009/500000000000 : ℝ) (992177940289/1000000000000 : ℝ) (992177940291/1000000000000 : ℝ) (99217794017/100000000000 : ℝ) (248044485043/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16501/131072 : ℝ)) 2 (992177940289/1000000000000 : ℝ) (992177940291/1000000000000 : ℝ) (99217794017/100000000000 : ℝ) (248044485043/250000000000 : ℝ) (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ) (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16501/131072 : ℝ)) 3 (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ) (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ) (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ) (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16501/131072 : ℝ)) 4 (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ) (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ) (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ) (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16501/131072 : ℝ)) 5 (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ) (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ) (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ) (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16501/131072 : ℝ)) 6 (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ) (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ) (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ) (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16501/131072 : ℝ)) 7 (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ) (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ) (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ) (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16501/131072 : ℝ))) (44004996361/250000000000 : ℝ) (3520399709/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16501/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44004996361/250000000000 : ℝ) (3520399709/20000000000 : ℝ) (294004996361/500000000000 : ℝ) (23520399709/40000000000 : ℝ) (26221709863/62500000000 : ℝ) (52443419727/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16501/131072 : ℝ))) 1 (294004996361/500000000000 : ℝ) (23520399709/40000000000 : ℝ) (26221709863/62500000000 : ℝ) (52443419727/125000000000 : ℝ) (100755735053/200000000000 : ℝ) (503778675271/1000000000000 : ℝ) (496687063261/1000000000000 : ℝ) (124171765817/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16501/131072 : ℝ))) 2 (100755735053/200000000000 : ℝ) (503778675271/1000000000000 : ℝ) (496687063261/1000000000000 : ℝ) (124171765817/250000000000 : ℝ) (500232869263/1000000000000 : ℝ) (50023286927/100000000000 : ℝ) (500220302217/1000000000000 : ℝ) (20008812089/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16501/131072 : ℝ))) 3 (500232869263/1000000000000 : ℝ) (50023286927/100000000000 : ℝ) (500220302217/1000000000000 : ℝ) (20008812089/40000000000 : ℝ) (25011329287/50000000000 : ℝ) (125056646437/250000000000 : ℝ) (5002265857/10000000000 : ℝ) (500226585709/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16501/131072 : ℝ))) 4 (25011329287/50000000000 : ℝ) (125056646437/250000000000 : ℝ) (5002265857/10000000000 : ℝ) (500226585709/1000000000000 : ℝ) (12505664643/25000000000 : ℝ) (500226585729/1000000000000 : ℝ) (500226585719/1000000000000 : ℝ) (500226585729/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16501/131072 : ℝ))) 5 (12505664643/25000000000 : ℝ) (500226585729/1000000000000 : ℝ) (500226585719/1000000000000 : ℝ) (500226585729/1000000000000 : ℝ) (500226585719/1000000000000 : ℝ) (500226585729/1000000000000 : ℝ) (500226585719/1000000000000 : ℝ) (500226585729/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16501/131072 : ℝ))) 6 (500226585719/1000000000000 : ℝ) (500226585729/1000000000000 : ℝ) (500226585719/1000000000000 : ℝ) (500226585729/1000000000000 : ℝ) (500226585719/1000000000000 : ℝ) (500226585729/1000000000000 : ℝ) (500226585719/1000000000000 : ℝ) (500226585729/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16501/131072 : ℝ))) 7 (500226585719/1000000000000 : ℝ) (500226585729/1000000000000 : ℝ) (500226585719/1000000000000 : ℝ) (500226585729/1000000000000 : ℝ) (500226585719/1000000000000 : ℝ) (500226585729/1000000000000 : ℝ) (500226585719/1000000000000 : ℝ) (500226585729/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16501/131072 : ℝ)) hmem 8 (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ) (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16501/131072 : ℝ))) hcmem 8 (500226585719/1000000000000 : ℝ) (500226585729/1000000000000 : ℝ) (500226585719/1000000000000 : ℝ) (500226585729/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16501/131072 : ℝ)) (992177940229/1000000000000 : ℝ) (124022242529/125000000000 : ℝ) (500226585719/1000000000000 : ℝ) (500226585729/1000000000000 : ℝ) (395974376949/500000000000 : ℝ) (791948753917/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0274_exp_lower
  have heNumeric : (1027453526219/500000000000 : ℝ)/4 ≤ Real.exp (-5328509953211/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453526219/500000000000 : ℝ)/4 ≤ Real.exp ((4125/32768 : ℝ)-(791948753917/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4125/32768 : ℝ) (16501/131072 : ℝ) (791948753917/1000000000000 : ℝ) (1027453526219/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0250_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0250_certificate
#check SmaleRate.Proofs.cover8_leaf0251_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0251_certificate
#check SmaleRate.Proofs.cover8_leaf0252_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0252_certificate
#check SmaleRate.Proofs.cover8_leaf0253_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0253_certificate
#check SmaleRate.Proofs.cover8_leaf0254_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0254_certificate
#check SmaleRate.Proofs.cover8_leaf0255_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0255_certificate
#check SmaleRate.Proofs.cover8_leaf0256_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0256_certificate
#check SmaleRate.Proofs.cover8_leaf0257_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0257_certificate
#check SmaleRate.Proofs.cover8_leaf0258_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0258_certificate
#check SmaleRate.Proofs.cover8_leaf0259_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0259_certificate
#check SmaleRate.Proofs.cover8_leaf0260_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0260_certificate
#check SmaleRate.Proofs.cover8_leaf0261_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0261_certificate
#check SmaleRate.Proofs.cover8_leaf0262_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0262_certificate
#check SmaleRate.Proofs.cover8_leaf0263_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0263_certificate
#check SmaleRate.Proofs.cover8_leaf0264_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0264_certificate
#check SmaleRate.Proofs.cover8_leaf0265_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0265_certificate
#check SmaleRate.Proofs.cover8_leaf0266_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0266_certificate
#check SmaleRate.Proofs.cover8_leaf0267_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0267_certificate
#check SmaleRate.Proofs.cover8_leaf0268_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0268_certificate
#check SmaleRate.Proofs.cover8_leaf0269_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0269_certificate
#check SmaleRate.Proofs.cover8_leaf0270_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0270_certificate
#check SmaleRate.Proofs.cover8_leaf0271_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0271_certificate
#check SmaleRate.Proofs.cover8_leaf0272_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0272_certificate
#check SmaleRate.Proofs.cover8_leaf0273_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0273_certificate
#check SmaleRate.Proofs.cover8_leaf0274_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0274_certificate
